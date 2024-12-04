# `typus_fugit`
![Crates.io](https://img.shields.io/crates/v/typus_fugit.svg)
[![Docs.rs](https://img.shields.io/docsrs/typus_fugit)](https://docs.rs/typus_fugit)


> `typus_fugit` provides a comprehensive library of `Duration` and `Instant` for the handling of time in embedded systems, using compile-time types to represent values.

This library began as a fork of [`fugit`](https://github.com/korken89/fugit/tree/0ad21f78f7d0b4f691ba9c7445f93299039d9f54), which is, in turn, a heavily inspired of `std::chrono`'s `Duration` from C++ which does all it can at compile time.

The decision to fork was due to the desire to replace const-generics values represented in the type system. This provides:

- Specification of legal values within the type system
- Evaluation of values within the type system
- Erasure of machine representation of values until needed at execution time

Initial implementation uses `typenum` for type-level values and evaluation. There is an intent to migrate to `type_eval` when it's ready.

## Aims

* Try to stay in sync with `fugit`
  * If users wish to switch between the two, the process should be low-friction and relatively reliable
  * If `fugit` decides to migrate to types instead of consts, the result should not look very different to `typus_fugit`
* `no_std` library with goals of user-friendliness and performance first
  * Priority placed on type-level evaluation
  * When type-level evaluation isn't available, use `const fn` where the possible.
  * All timebase operations performed using type-level evaluation
* Support for both `u32` and `u64` backing storage with efficient instruction lowering on MCUs
  * On Cortex-M3 and up: no soft-impls pulled in for both `u32` and `u64` except when changing base on `u64`
  * Comparisons on `u32` and `u64` do not use division, only changing base with all constants calculated at compile time
* Selection of base happens at compile time, within the type-system.
  * A common problem is that run time changing of base robs us of a lot of optimization opportunities, but since types are used here, bases are evaluated at compile time.

