# peekaboo

Peekable iterator that allows to peek the next `N` elements without consuming them.

## Examples

Basic usage:

```rust
let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];
// create an iterator that allows us to peek at the next 4 element
let mut iter = xs.iter().peekable_n::<4>();

// peek() lets us see into the future
assert_eq!(iter.peek::<1>(), Some(&&1));
assert_eq!(iter.peek::<3>(), Some(&&3));

// the iterator will not advance until we call `next`
assert_eq!(iter.next(), Some(&1));
assert_eq!(iter.next(), Some(&2));
```
