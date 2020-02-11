# Week Seven Meeting
## Schedule
5 Nov 2019, 15:00 - 16:00

## Status
* Finished reduce rule
* Finished partial reduction rule
* Added rewrite pattern matching for refining proofs

## Discussion
* Issues with `partRed`, the `id` (inital combinator) is not used anywhere
* Issues with the first partial reduction, the `id` doesn't match on the two sides
* Need some typeclass (in agda `Record`) for abstracting operators with certain properties, such as [discussion here](https://lists.chalmers.se/pipermail/agda/2015/007769.html).
* Make the proofs more structure

## Plan
* refine partial reduction, the id elements
* maintain a list of proved primitives and rewrite rules