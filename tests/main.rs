use peekaboo::*;

#[test]
fn it_works() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut iter = xs.iter().peekable_n::<4>();

    assert_eq!(iter.peek::<1>(), Some(&&1));
    assert_eq!(iter.peek::<3>(), Some(&&3));

    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.next(), Some(&2));

    // The iterator does not advance even if we `peek` multiple times and far ahead
    assert_eq!(iter.peek::<1>(), Some(&&3));
    assert_eq!(iter.peek::<3>(), Some(&&5));

    assert_eq!(iter.next(), Some(&3));

    assert_eq!(iter.peek::<4>(), Some(&&7));
    assert_eq!(iter.peek::<2>(), Some(&&5));

    assert_eq!(iter.next(), Some(&4));
    assert_eq!(iter.next(), Some(&5));
    assert_eq!(iter.next(), Some(&6));

    // the array has no more elements, so peek returns `None`
    assert_eq!(iter.peek::<4>(), None);

    assert_eq!(iter.next(), Some(&7));
    assert_eq!(iter.next(), Some(&8));
    assert_eq!(iter.next(), Some(&9));

    // After the iterator is finished, so is `peek()`
    assert_eq!(iter.peek::<1>(), None);
    assert_eq!(iter.next(), None);
}

#[test]
fn peek_multiple() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut iter = xs.iter().peekable_n::<4>();

    assert_eq!(iter.peek_multiple::<3>(), [Some(&&1), Some(&&2), Some(&&3)]);
    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.peek_multiple::<1>(), [Some(&&2)]);
    assert_eq!(
        iter.peek_multiple::<4>(),
        [Some(&&2), Some(&&3), Some(&&4), Some(&&5)]
    );
}

#[test]
fn next_if() {
    let mut iter = (0..5).peekable_n::<3>();
    // The first item of the iterator is 0; consume it.
    assert_eq!(iter.next_if(|&x| x == 0), Some(0));
    // The next item returned is now 1, so `consume` will return `false`.
    assert_eq!(iter.next_if(|&x| x == 0), None);
    // `next_if` saves the value of the next item if it was not equal to `expected`.
    assert_eq!(iter.next(), Some(1));
}

#[test]
fn next_if_eq() {
    let mut iter = (0..5).peekable_n::<21>();
    // The first item of the iterator is 0; consume it.
    assert_eq!(iter.next_if_eq(&0), Some(0));
    // The next item returned is now 1, so `consume` will return `false`.
    assert_eq!(iter.next_if_eq(&0), None);
    // `next_if_eq` saves the value of the next item if it was not equal to `expected`.
    assert_eq!(iter.next(), Some(1));
}

#[test]
fn count() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut iter = xs.iter().peekable_n::<7>();

    assert_eq!(iter.clone().count(), 9);
    iter.peek::<1>();
    assert_eq!(iter.clone().count(), 9);
    iter.peek::<6>();
    assert_eq!(iter.clone().count(), 9);

    iter.next();
    iter.next();

    assert_eq!(iter.clone().count(), 7);
    iter.peek::<2>();
    assert_eq!(iter.clone().count(), 7);

    iter.next();
    iter.next();

    assert_eq!(iter.clone().count(), 5);
    iter.peek::<6>();
    assert_eq!(iter.clone().count(), 5);
}

#[test]
fn nth() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut iter = xs.iter().peekable_n::<7>();

    assert_eq!(iter.nth(3), Some(&4));
    iter.peek::<5>();
    assert_eq!(iter.nth(1), Some(&6));
    assert_eq!(iter.nth(0), Some(&7));
    iter.peek::<5>();
    assert_eq!(iter.nth(1), Some(&9));
}

#[test]
fn last() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    let iter = xs.iter().peekable_n::<5>();

    assert_eq!(iter.clone().last(), Some(&9));

    let mut it = iter.clone();
    it.peek::<4>();
    assert_eq!(it.last(), Some(&9));

    let mut it = iter.clone();
    it.peek::<4>();
    for _ in 0..10 {
        it.next();
    }
    assert_eq!(it.last(), None);
}

#[test]
fn size_hint() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut iter = xs.iter().peekable_n::<5>();

    assert_eq!(iter.size_hint(), (9, Some(9)));

    // peeking doesn't change the hint
    iter.peek::<3>();
    assert_eq!(iter.size_hint(), (9, Some(9)));

    iter.nth(6);
    assert_eq!(iter.size_hint(), (2, Some(2)));

    iter.peek::<4>();
    assert_eq!(iter.size_hint(), (2, Some(2)));

    iter.nth(6);
    assert_eq!(iter.size_hint(), (0, Some(0)));
    iter.peek::<4>();
    assert_eq!(iter.size_hint(), (0, Some(0)));
}

#[test]
fn fold() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut iter = xs.iter().peekable_n::<5>();

    let sum = iter.clone().fold(0, |acc, x| acc + x);
    assert_eq!(sum, 45);

    iter.peek::<4>();
    let sum = iter.clone().fold(0, |acc, x| acc + x);
    assert_eq!(sum, 45);

    iter.next();
    let sum = iter.clone().fold(0, |acc, x| acc + x);
    assert_eq!(sum, 44);
}

#[test]
fn next_back() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut iter = xs.iter().peekable_n::<5>();

    assert_eq!(Some(&1), iter.next());
    assert_eq!(Some(&9), iter.next_back());

    iter.peek::<5>();

    assert_eq!(Some(&2), iter.next());
    assert_eq!(Some(&8), iter.next_back());
    assert_eq!(Some(&3), iter.next());
    assert_eq!(Some(&7), iter.next_back());
    assert_eq!(Some(&6), iter.next_back());

    assert_eq!(iter.peek::<5>(), None);
    assert_eq!(iter.peek::<2>(), Some(&&5));
}

#[test]
fn rfold() {
    let numbers = [1, 2, 3, 4, 5];

    let zero = "0".to_string();

    let result = numbers
        .iter()
        .peekable_n::<12>()
        .rfold(zero, |acc, &x| format!("({x} + {acc})"));

    assert_eq!(result, "(1 + (2 + (3 + (4 + (5 + 0)))))");
}
