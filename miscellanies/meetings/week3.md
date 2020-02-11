# Week Three Meeting

## Schedule
8 Oct 2019, 15:00 - 16:00

## Status
* Read through paper proofs
* Start defining primitives

## Questions
* The usage of built-ins? 
    * for example, I planned to prove **identity rule**
    * data types involved are `Nat` and LIFT `Array` (Agda `Vec`)
    * need to define `id` and `map`
    * then I found `id` and `map` are defined in `Function` and `Vec`

## Answers
* We define the primitives by ourselves
* For current stage, we do not define the LIFT data types in Agda, instead, we use Agda default data types
    * for example, LIFT `Data` contains `NatData`, `ScalarData`, `TupleData`, `ArrayData` etc., we use `Set` in Agda to represent LIFT `Data` for now
    * we might need to specify these data types in detail in the future

## Plan for this week
* Write proofs for identity rules and split-join rules