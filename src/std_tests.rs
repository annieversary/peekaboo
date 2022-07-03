//! translation of the stdlib tests for `std::iter::Peekable`

use super::*;
use std::iter::empty;

#[test]
fn test_iterator_peekable() {
    let xs = vec![0, 1, 2, 3, 4, 5];

    let mut it = xs.iter().cloned().peekable_n::<1>();
    assert_eq!(it.len(), 6);
    assert_eq!(it.peek::<1>().unwrap(), &0);
    assert_eq!(it.len(), 6);
    assert_eq!(it.next().unwrap(), 0);
    assert_eq!(it.len(), 5);
    assert_eq!(it.next().unwrap(), 1);
    assert_eq!(it.len(), 4);
    assert_eq!(it.next().unwrap(), 2);
    assert_eq!(it.len(), 3);
    assert_eq!(it.peek::<1>().unwrap(), &3);
    assert_eq!(it.len(), 3);
    assert_eq!(it.peek::<1>().unwrap(), &3);
    assert_eq!(it.len(), 3);
    assert_eq!(it.next().unwrap(), 3);
    assert_eq!(it.len(), 2);
    assert_eq!(it.next().unwrap(), 4);
    assert_eq!(it.len(), 1);
    assert_eq!(it.peek::<1>().unwrap(), &5);
    assert_eq!(it.len(), 1);
    assert_eq!(it.next().unwrap(), 5);
    assert_eq!(it.len(), 0);
    assert!(it.peek::<1>().is_none());
    assert_eq!(it.len(), 0);
    assert!(it.next().is_none());
    assert_eq!(it.len(), 0);

    let mut it = xs.iter().cloned().peekable_n::<1>();
    assert_eq!(it.len(), 6);
    assert_eq!(it.peek::<1>().unwrap(), &0);
    assert_eq!(it.len(), 6);
    assert_eq!(it.next_back().unwrap(), 5);
    assert_eq!(it.len(), 5);
    assert_eq!(it.next_back().unwrap(), 4);
    assert_eq!(it.len(), 4);
    assert_eq!(it.next_back().unwrap(), 3);
    assert_eq!(it.len(), 3);
    assert_eq!(it.peek::<1>().unwrap(), &0);
    assert_eq!(it.len(), 3);
    assert_eq!(it.peek::<1>().unwrap(), &0);
    assert_eq!(it.len(), 3);
    assert_eq!(it.next_back().unwrap(), 2);
    assert_eq!(it.len(), 2);
    assert_eq!(it.next_back().unwrap(), 1);
    assert_eq!(it.len(), 1);
    assert_eq!(it.peek::<1>().unwrap(), &0);
    assert_eq!(it.len(), 1);
    assert_eq!(it.next_back().unwrap(), 0);
    assert_eq!(it.len(), 0);
    assert!(it.peek::<1>().is_none());
    assert_eq!(it.len(), 0);
    assert!(it.next_back().is_none());
    assert_eq!(it.len(), 0);
}

#[test]
fn test_iterator_peekable_count() {
    let xs = [0, 1, 2, 3, 4, 5];
    let ys = [10];
    let zs: [i32; 0] = [];

    assert_eq!(xs.iter().peekable_n::<1>().count(), 6);

    let mut it = xs.iter().peekable_n::<1>();
    assert_eq!(it.peek::<1>(), Some(&&0));
    assert_eq!(it.count(), 6);

    assert_eq!(ys.iter().peekable_n::<1>().count(), 1);

    let mut it = ys.iter().peekable_n::<1>();
    assert_eq!(it.peek::<1>(), Some(&&10));
    assert_eq!(it.count(), 1);

    assert_eq!(zs.iter().peekable_n::<1>().count(), 0);

    let mut it = zs.iter().peekable_n::<1>();
    assert_eq!(it.peek::<1>(), None);
}

#[test]
fn test_iterator_peekable_nth() {
    let xs = [0, 1, 2, 3, 4, 5];
    let mut it = xs.iter().peekable_n::<1>();

    assert_eq!(it.peek::<1>(), Some(&&0));
    assert_eq!(it.nth(0), Some(&0));
    assert_eq!(it.peek::<1>(), Some(&&1));
    assert_eq!(it.nth(1), Some(&2));
    assert_eq!(it.peek::<1>(), Some(&&3));
    assert_eq!(it.nth(2), Some(&5));
    assert_eq!(it.next(), None);
}

#[test]
fn test_iterator_peekable_last() {
    let xs = [0, 1, 2, 3, 4, 5];
    let ys = [0];

    let mut it = xs.iter().peekable_n::<1>();
    assert_eq!(it.peek::<1>(), Some(&&0));
    assert_eq!(it.last(), Some(&5));

    let mut it = ys.iter().peekable_n::<1>();
    assert_eq!(it.peek::<1>(), Some(&&0));
    assert_eq!(it.last(), Some(&0));

    let mut it = ys.iter().peekable_n::<1>();
    assert_eq!(it.next(), Some(&0));
    assert_eq!(it.peek::<1>(), None);
    assert_eq!(it.last(), None);
}

#[test]
fn test_iterator_peekable_fold() {
    let xs = [0, 1, 2, 3, 4, 5];
    let mut it = xs.iter().peekable_n::<1>();
    assert_eq!(it.peek::<1>(), Some(&&0));
    let i = it.fold(0, |i, &x| {
        assert_eq!(x, xs[i]);
        i + 1
    });
    assert_eq!(i, xs.len());
}

#[test]
fn test_iterator_peekable_rfold() {
    let xs = [0, 1, 2, 3, 4, 5];
    let mut it = xs.iter().peekable_n::<1>();
    assert_eq!(it.peek::<1>(), Some(&&0));
    let i = it.rfold(0, |i, &x| {
        assert_eq!(x, xs[xs.len() - 1 - i]);
        i + 1
    });
    assert_eq!(i, xs.len());
}

#[test]
fn test_iterator_peekable_next_if_eq() {
    // first, try on references
    let xs = ["Heart", "of", "Gold"];
    let mut it = xs.into_iter().peekable_n::<1>();
    // try before `peek::<1>()`
    assert_eq!(it.next_if_eq(&"trillian"), None);
    assert_eq!(it.next_if_eq(&"Heart"), Some("Heart"));
    // try after peek::<1>()
    assert_eq!(it.peek::<1>(), Some(&"of"));
    assert_eq!(it.next_if_eq(&"of"), Some("of"));
    assert_eq!(it.next_if_eq(&"zaphod"), None);
    // make sure `next()` still behaves
    assert_eq!(it.next(), Some("Gold"));

    // make sure comparison works for owned values
    let xs = [String::from("Ludicrous"), "speed".into()];
    let mut it = xs.into_iter().peekable_n::<1>();
    // make sure basic functionality works
    assert_eq!(it.next_if_eq("Ludicrous"), Some("Ludicrous".into()));
    assert_eq!(it.next_if_eq("speed"), Some("speed".into()));
    assert_eq!(it.next_if_eq(""), None);
}

#[test]
fn test_iterator_peekable_mut() {
    let mut it = [1, 2, 3].into_iter().peekable_n::<1>();
    if let Some(p) = it.peek_mut::<1>() {
        if *p == 1 {
            *p = 5;
        }
    }
    assert_eq!(it.collect::<Vec<_>>(), vec![5, 2, 3]);
}

#[test]
fn test_iterator_peekable_remember_peek_none_1() {
    // Check that the loop using .peek::<1>() terminates
    let data = [1, 2, 3];
    let mut iter = CycleIter::new(&data).peekable_n::<1>();

    let mut n = 0;
    while let Some(_) = iter.next() {
        let is_the_last = iter.peek::<1>().is_none();
        assert_eq!(is_the_last, n == data.len() - 1);
        n += 1;
        if n > data.len() {
            break;
        }
    }
    assert_eq!(n, data.len());
}

#[test]
fn test_iterator_peekable_remember_peek_none_2() {
    let data = [0];
    let mut iter = CycleIter::new(&data).peekable_n::<1>();
    iter.next();
    assert_eq!(iter.peek::<1>(), None);
    assert_eq!(iter.last(), None);
}

#[test]
fn test_iterator_peekable_remember_peek_none_3() {
    let data = [0];
    let mut iter = CycleIter::new(&data).peekable_n::<1>();
    iter.peek::<1>();
    assert_eq!(iter.nth(0), Some(&0));

    let mut iter = CycleIter::new(&data).peekable_n::<1>();
    iter.next();
    assert_eq!(iter.peek::<1>(), None);
    assert_eq!(iter.nth(0), None);
}

#[test]
fn test_peek_try_folds() {
    let f = &|acc, x| i32::checked_add(2 * acc, x);

    assert_eq!(
        (1..20).peekable_n::<1>().try_fold(7, f),
        (1..20).try_fold(7, f)
    );
    assert_eq!(
        (1..20).peekable_n::<1>().try_rfold(7, f),
        (1..20).try_rfold(7, f)
    );

    let mut iter = (1..20).peekable_n::<1>();
    assert_eq!(iter.peek::<1>(), Some(&1));
    assert_eq!(iter.try_fold(7, f), (1..20).try_fold(7, f));

    let mut iter = (1..20).peekable_n::<1>();
    assert_eq!(iter.peek::<1>(), Some(&1));
    assert_eq!(iter.try_rfold(7, f), (1..20).try_rfold(7, f));

    let mut iter = [100, 20, 30, 40, 50, 60, 70]
        .iter()
        .cloned()
        .peekable_n::<1>();
    assert_eq!(iter.peek::<1>(), Some(&100));
    assert_eq!(iter.try_fold(0, i8::checked_add), None);
    assert_eq!(iter.peek::<1>(), Some(&40));

    let mut iter = [100, 20, 30, 40, 50, 60, 70]
        .iter()
        .cloned()
        .peekable_n::<1>();
    assert_eq!(iter.peek::<1>(), Some(&100));
    assert_eq!(iter.try_rfold(0, i8::checked_add), None);
    assert_eq!(iter.peek::<1>(), Some(&100));
    assert_eq!(iter.next_back(), Some(50));

    let mut iter = (2..5).peekable_n::<1>();
    assert_eq!(iter.peek::<1>(), Some(&2));
    assert_eq!(iter.try_for_each(Err), Err(2));
    assert_eq!(iter.peek::<1>(), Some(&3));
    assert_eq!(iter.try_for_each(Err), Err(3));
    assert_eq!(iter.peek::<1>(), Some(&4));
    assert_eq!(iter.try_for_each(Err), Err(4));
    assert_eq!(iter.peek::<1>(), None);
    assert_eq!(iter.try_for_each(Err), Ok(()));

    let mut iter = (2..5).peekable_n::<1>();
    assert_eq!(iter.peek::<1>(), Some(&2));
    assert_eq!(iter.try_rfold((), |(), x| Err(x)), Err(4));
    assert_eq!(iter.peek::<1>(), Some(&2));
    assert_eq!(iter.try_rfold((), |(), x| Err(x)), Err(3));
    assert_eq!(iter.peek::<1>(), Some(&2));
    assert_eq!(iter.try_rfold((), |(), x| Err(x)), Err(2));
    assert_eq!(iter.peek::<1>(), None);
    assert_eq!(iter.try_rfold((), |(), x| Err(x)), Ok(()));
}

#[test]
fn test_peekable_non_fused() {
    let mut iter = NonFused::new(empty::<i32>()).peekable_n::<1>();

    assert_eq!(iter.peek::<1>(), None);
    assert_eq!(iter.next_back(), None);
}

// the following are helper things that are not in the std, so we copy them manually
// taken from https://github.com/rust-lang/rust/blob/effea9a2a0d501db5722d507690a1a66236933bf/library/core/tests/iter/adapters/mod.rs

/// This is an iterator that follows the Iterator contract,
/// but it is not fused. After having returned None once, it will start
/// producing elements if .next() is called again.
struct CycleIter<'a, T> {
    index: usize,
    data: &'a [T],
}

impl<'a, T> CycleIter<'a, T> {
    fn new(data: &'a [T]) -> Self {
        Self { index: 0, data }
    }
}

impl<'a, T> Iterator for CycleIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        let elt = self.data.get(self.index);
        self.index += 1;
        self.index %= 1 + self.data.len();
        elt
    }
}

/// An iterator that panics whenever `next` or next_back` is called
/// after `None` has already been returned. This does not violate
/// `Iterator`'s contract. Used to test that iterator adapters don't
/// poll their inner iterators after exhausting them.
struct NonFused<I> {
    iter: I,
    done: bool,
}

impl<I> NonFused<I> {
    fn new(iter: I) -> Self {
        Self { iter, done: false }
    }
}

impl<I> Iterator for NonFused<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        assert!(!self.done, "this iterator has already returned None");
        self.iter.next().or_else(|| {
            self.done = true;
            None
        })
    }
}

impl<I> DoubleEndedIterator for NonFused<I>
where
    I: DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        assert!(!self.done, "this iterator has already returned None");
        self.iter.next_back().or_else(|| {
            self.done = true;
            None
        })
    }
}
