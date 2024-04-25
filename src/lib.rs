use core::fmt;

use id::{Cell, CellToken, Checked};
use static_rc::StaticRc;

mod id;

type Ptr<T> = StaticRc<Cell<Node<T>, Checked>, 1, 2>;

pub struct LinkedList<T> {
    head_tail: Option<(Ptr<T>, Ptr<T>)>,
    token: CellToken<Checked>,
}

struct Node<T> {
    prev: Option<Ptr<T>>,
    next: Option<Ptr<T>>,
    value: T,
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        Self {
            head_tail: Default::default(),
            token: CellToken::new(Checked::new()),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for LinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut list = f.debug_list();
        let mut head = self.head_tail.as_ref().map(|(head, _)| head);
        while let Some(node) = head {
            let node = node.get(&self.token);
            list.entry(&node.value);
            head = node.next.as_ref();
        }

        list.finish()
    }
}

impl<T> LinkedList<T> {
    pub fn push_front(&mut self, value: T) {
        let node = Node {
            next: None,
            prev: None,
            value,
        };
        let rc = StaticRc::<Cell<Node<T>, Checked>, 2, 2>::new(self.token.cell(node));
        let (next, prev) = StaticRc::split::<1, 1>(rc);
        match self.head_tail.take() {
            Some((head, tail)) => {
                debug_assert!(head.get(&self.token).prev.is_none());
                head.get_mut(&mut self.token).prev = Some(prev);
                next.get_mut(&mut self.token).next = Some(head);
                self.head_tail = Some((next, tail));
            }
            None => {
                self.head_tail = Some((next, prev));
            }
        }
    }

    pub fn push_back(&mut self, value: T) {
        let node = Node {
            next: None,
            prev: None,
            value,
        };
        let rc = StaticRc::<Cell<Node<T>, Checked>, 2, 2>::new(self.token.cell(node));
        let (next, prev) = StaticRc::split::<1, 1>(rc);
        match self.head_tail.take() {
            Some((head, tail)) => {
                debug_assert!(tail.get(&self.token).next.is_none());
                tail.get_mut(&mut self.token).next = Some(next);
                prev.get_mut(&mut self.token).prev = Some(tail);
                self.head_tail = Some((head, prev));
            }
            None => {
                self.head_tail = Some((next, prev));
            }
        }
    }

    pub fn pop_front(&mut self) -> Option<T> {
        let (head, tail) = self.head_tail.take()?;

        let prev = if let Some(next) = head.get_mut(&mut self.token).next.take() {
            let prev = next.get_mut(&mut self.token).prev.take().unwrap();
            self.head_tail = Some((next, tail));
            prev
        } else {
            tail
        };

        let node = StaticRc::<_, 2, 2>::join(head, prev);
        let node = StaticRc::into_inner(node).into_inner();
        debug_assert!(node.next.is_none());
        debug_assert!(node.prev.is_none());
        Some(node.value)
    }

    pub fn pop_back(&mut self) -> Option<T> {
        let (head, tail) = self.head_tail.take()?;

        let next = if let Some(prev) = tail.get_mut(&mut self.token).prev.take() {
            let next = prev.get_mut(&mut self.token).next.take().unwrap();
            self.head_tail = Some((head, prev));
            next
        } else {
            head
        };

        let node = StaticRc::<_, 2, 2>::join(next, tail);
        let node = StaticRc::into_inner(node).into_inner();
        debug_assert!(node.prev.is_none());
        debug_assert!(node.next.is_none());
        Some(node.value)
    }

    pub fn iter(&self) -> Cursor<'_, T> {
        Cursor {
            token: &self.token,
            head_tail: self.head_tail.as_ref().map(|(head, tail)| (head, tail)),
        }
    }
}

pub struct Cursor<'a, T> {
    token: &'a CellToken<Checked>,
    head_tail: Option<(&'a Ptr<T>, &'a Ptr<T>)>,
}

impl<'a, T> Iterator for Cursor<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let (head, tail) = self.head_tail?;

        let head_node = head.get(self.token);
        match head_node.next.as_ref() {
            Some(next) if !StaticRc::ptr_eq(head, tail) => self.head_tail = Some((next, tail)),
            _ => self.head_tail = None,
        }

        Some(&head_node.value)
    }
}

impl<'a, T> DoubleEndedIterator for Cursor<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (head, tail) = self.head_tail?;

        let tail_node = tail.get(self.token);
        match tail_node.prev.as_ref() {
            Some(prev) if !StaticRc::ptr_eq(head, tail) => self.head_tail = Some((head, prev)),
            _ => self.head_tail = None,
        }

        Some(&tail_node.value)
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        while let Some(x) = self.pop_front() {
            drop(x);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use crate::LinkedList;

    #[test]
    fn debug() {
        let mut ll = LinkedList::default();
        ll.push_front(4);
        ll.push_front(3);
        ll.push_front(2);
        ll.push_front(1);
        ll.push_back(5);
        ll.push_back(6);
        ll.push_back(7);
        ll.push_back(8);
        assert_eq!(format!("{ll:?}"), "[1, 2, 3, 4, 5, 6, 7, 8]");
    }

    #[test]
    fn pop_front() {
        let mut ll = LinkedList::default();
        ll.push_front(4);
        ll.push_front(3);
        ll.push_front(2);
        ll.push_front(1);
        ll.push_back(5);
        ll.push_back(6);
        ll.push_back(7);
        ll.push_back(8);

        let mut vec = vec![];
        while let Some(x) = ll.pop_front() {
            vec.push(x);
        }

        assert_eq!(vec, [1, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    fn pop_back() {
        let mut ll = LinkedList::default();
        ll.push_front(4);
        ll.push_front(3);
        ll.push_front(2);
        ll.push_front(1);
        ll.push_back(5);
        ll.push_back(6);
        ll.push_back(7);
        ll.push_back(8);

        let mut vec = vec![];
        while let Some(x) = ll.pop_back() {
            vec.push(x);
        }

        assert_eq!(vec, [8, 7, 6, 5, 4, 3, 2, 1]);
    }

    #[test]
    fn iter() {
        let mut ll = LinkedList::default();
        ll.push_front(4);
        ll.push_front(3);
        ll.push_front(2);
        ll.push_front(1);
        ll.push_back(5);
        ll.push_back(6);
        ll.push_back(7);
        ll.push_back(8);

        let mut vec = vec![];
        for x in ll.iter() {
            vec.push(*x);
        }

        assert_eq!(vec, [1, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    fn iter_back() {
        let mut ll = LinkedList::default();
        ll.push_front(4);
        ll.push_front(3);
        ll.push_front(2);
        ll.push_front(1);
        ll.push_back(5);
        ll.push_back(6);
        ll.push_back(7);
        ll.push_back(8);

        let mut vec = vec![];
        for x in ll.iter().rev() {
            vec.push(*x);
        }

        assert_eq!(vec, [8, 7, 6, 5, 4, 3, 2, 1]);
    }

    #[test]
    fn iter_middle() {
        let mut ll = LinkedList::default();
        ll.push_front(4);
        ll.push_front(3);
        ll.push_front(2);
        ll.push_front(1);
        ll.push_back(5);
        ll.push_back(6);
        ll.push_back(7);
        ll.push_back(8);

        let mut vec = vec![];
        let mut iter = ll.iter();
        for x in iter.by_ref().take(4) {
            vec.push(*x);
        }
        for x in iter.rev() {
            vec.push(*x);
        }

        assert_eq!(vec, [1, 2, 3, 4, 8, 7, 6, 5]);
    }

    struct CountDrop<'a>(&'a RefCell<usize>);
    impl Drop for CountDrop<'_> {
        fn drop(&mut self) {
            *self.0.borrow_mut() += 1;
        }
    }

    #[test]
    fn leak() {
        let count = RefCell::new(0);
        let mut ll = LinkedList::default();

        for _ in 0..1000 {
            ll.push_front(CountDrop(&count));
        }

        drop(ll);
        assert_eq!(count.into_inner(), 1000);
    }
}
