# Week Two Meeting

## Schedule
1 Oct 2019, 15:00 - 16:00

## Approach
* Define data types and semantics
    * Data types
* Define primitive types and semantics
    * `map`, `zip`, `join`, `reduce`, `split`, etc.
* Prove LIFT rewrite rules
    * Figure out the rules to look into and then define primitive type semantics
* Prove ELEVATE strategies (extension)
* Evaluation
    - define the semantics effectively
    - lemma/modular
    - is it a good way
    - the correctness

## Questions
* Defining semantics of LIFT in Agda, should I refer to `Data.scala` or `Type.scala`?
    * Treat `ScalarType` as a whole to avoid over complication on floating point numbers
    * LIFT array as Agda `Vec`
    * LIFT index as Agda `Fin`
    * LIFT tuple as Agda `Tuple`
* Any build artifacts required?
    * Just source code
* How to understand/define `IndexData` or `IndexType`
     * LIFT index as Agda `Fin`

## Required submission
* Submit one page project proposal before Friday (4 Oct 2019)