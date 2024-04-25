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
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        let Some((mut head, tail)) = self.head_tail.take() else {
            return;
        };
        loop {
            let Some(next) = head.get_mut(&mut self.token).next.take() else {
                _ = StaticRc::<_, 2, 2>::join(head, tail);
                return;
            };
            let prev = next.get_mut(&mut self.token).prev.take().unwrap();
            _ = StaticRc::<_, 2, 2>::join(head, prev);
            head = next;
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
