# Week Four Meeting

## Schedule
15 Oct 2019, 15:00 - 16:00

## Status
* Completed proofs `identity` rules
* Half-way proving `splitJoin` rules

## Question
* The equality of `Vec t (n * m)` and `Vec t (m * n)` is causing issues in reasoning the primitive `join`, and further affecting `splitJoin` rule
    * using the type `Vec t (m * n)` is easy to reason about join, but causing issues defining `splitJoin`
    * `Vec t (n * m)` satisfies the definition of `splitJoin`, but not easy to reason in `join`
    - A: meeting arranged (we have help)
* Still trying to find a neat way to prove `split`, adding lemma `splitAt` might be useful?
    - A: use `drop` and `take`
* `split` for array size not divisible by `m`?
    - A:  always divisible