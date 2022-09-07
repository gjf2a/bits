# Overview

The `bits` crate features a `BitArray` struct that represents a sequence of bits. It supports
the `&`, `|` and `^` binary operators and the `!` unary operator. Because copies could get
expensive, these operators are intended to be used by reference.

If the lengths of the arguments to a binary operator differ, it will **panic**.

```
use bits::*;

let b1: BitArray = "1101".parse().unwrap();
let b2: BitArray = "0110".parse().unwrap();

assert_eq!(&b1 & &b2, "0100".parse().unwrap());
assert_eq!(&b1 | &b2, "1111".parse().unwrap());
assert_eq!(&b1 ^ &b2, "1011".parse().unwrap());
assert_eq!(!&b1, "0010".parse().unwrap());
assert_eq!(!&!&b2, b2);
```

`BitArray` objects can be built incrementally using the `add()` method. The first digit
added is the lowest-order bit. Each successive `add()` adds its bit as the next-highest order.

```
use bits::*;

let mut b = BitArray::new();
b.add(true);
b.add(false);
b.add(true);
b.add(true);

assert_eq!(b, "1101".parse().unwrap());
assert_eq!(num::BigUint::from(&b), num::BigUint::from(13 as u32));
```

`BitArray` objects can also be created by specifying a number of zeros or ones for initialization.

```
use bits::*;

let z = BitArray::zeros(10);
assert_eq!(z.len(), 10);
//assert_eq!(z, "0000000000".parse().unwrap());

let n = BitArray::ones(10);
assert_eq!(n.len(), 10);
//assert_eq!(n, "1111111111".parse().unwrap());
```

Some miscellaneous utilities include the ability to count bits, compute distances, and create
combinations.

```
use bits::*;

let b1: BitArray = "1101".parse().unwrap();
let b2: BitArray = "0110".parse().unwrap();

assert_eq!(b1.count_bits_on(), 3);
assert_eq!(b2.count_bits_on(), 2);
assert_eq!(distance(&b1, &b2), 3);

let c = BitArray::all_combinations(2);
let cv: Vec<BitArray> = ["00", "10", "01", "11"].iter().map(|s| s.parse().unwrap()).collect();
assert_eq!(c, cv);
```
