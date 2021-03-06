# Timelog

* Proving the Correctness of Rewrite Rules in LIFT’s Rewrite-Based System
* Xueying Qin
* 2335466
* Supervisor: Michel Steuwer

## Guidance

* This file contains the time log for your project. It will be submitted along with your final dissertation.
* **YOU MUST KEEP THIS UP TO DATE AND UNDER VERSION CONTROL.**
* This timelog should be filled out honestly, regularly (daily) and accurately. It is for *your* benefit.
* Follow the structure provided, grouping time by weeks.  Quantise time to the half hour.

## Week 1

### 23 Sep 2019
* *1 hour* meeting with supervisor
* *2.5 hours* environment setup, installing Agda dependencies and configuring IDE spacemacs
* *0.5 hours* reading project requirements and instructions
* *1 hours* reading materials sent by supervior after meeting 

### 24 Sep 2019
* *4 hours* attending l4 project introduction lectures
* *2 hours* organising references using Zotero

### 25 Sep 2019
* *2 hours* github repository setup
* *2 hours* LIFT, ELEVATE and DPIA background reading

### 26 Sep 2019
* *1 hour* familiarising Agda key bindings in spacemacs
* *2 hours* understanding LIFT source code, especially AST and primitives
* *2 hours* background reading

### 27 Sep 2019
* *4 hours* gathering data types, primitives and rewrite rules from latest version of source code and papers

## Week 2
### 30 Sep 2019
* *1 hour* documenting project plans and time log
* *1 hour* background reading

### 01 Oct 2019
* *2 hours* drafting project proposal and gathering questions
* *1 hour* meeting with supervisor
* *0.5 hours* documenting information gethered from meeting

### 02 Oct 2019
* *2.5 hours* background reading on papers and source code

### 03 Oct 2019
* *2 hours* writing project proposal

## Week 3
### 07 Oct 2019
* *2 hours* analysing primitive definition and paper proofs
### 08 Oct 2019
* *1 hour* meeting with supervisor
* *0.5 hours* documenting information gethered from meeting
### 09 Oct 2019
* *2 hours* implementing primitives `id`, `split`, `join`
### 10 Oct 2019
* *3 hours* implementing primitives `id`, `split`, `join` and lemmas
### 11 Oct 2019
* *4 hours* Add proofs for 2 identity rules and worked on the split-join rule

## Week 4
### 14 Oct 2019
* *0.5 hour* updating documents
* *2 hours* rewriting `join` with lemma

### 15 Oct 2019
* *2 hours* writing proofs for `spiltJoin`
* *1 hour* meeting with supervisor
* *3 hours* proving `split` (finally done)

### 16 Oct 2019
* *1 hour* writing proof for fusion rule option one
* *1 hour* meeting and discussing about using `subst` in reasoning Vec size
* *4.5 hours* proving lemmas for `splitJoin` 

### 17 Oct 2019
* *5 hours* proving lemma `map-split`, `map-drop` and `map-take`, restructuring the semantics of `take` and `drop` to simplify the proof of lemmas and rewrite rules

### 18 Oct 2019
* *0.5 hours* proving the second simplification rule
* *1.5 hours* refining the semantics of primitives, proving the first simplification rule and refining the proof for split-join rule

## Week 5
### 21 Oct 2019
* *1 hour* reading about the tiling rule and writing definitions of `slide` and `reduce`

### 22 Oct 2019
* *1 hour* meeting with supervisor
* *0.5 hours* documenting issues discussed in meeting and implemented `reduceSeq` and `reduce`

### 23 Oct 2019
* *2 hours* reading and implementing `slide`

### 24 Oct 2019
* *3 hours* proving the second fusion rule, fixing the type issue of the lambda function in paper proof
* *1 hour* trying agda `REWRITE` pragma, protentially it can be used for simplifying the semantics of the primitives

### 25 Oct 2019
* *1 hour* finished proving the second fusion rule and clean up code

## Week 6
### 28 Oct 2019
* *2.5 hours* refining proofs with `REWRITE` pragma

### 29 Oct 2019
* *2 hours* refining `_+_`, finished definition for `slide`, cleaning up proofs
* *1 hour* supervisor meeting

### 30 Oct 2019
* *0.5 hours* adding proof for sub rules of `tiling`, documenting notes

### 31 Oct 2019
* *2 hours* adding definition for `partRed`
* *3 hours* proving the reduction rule

## Week 7
### 4 Nov 2019
* *8 hours* defined abstract binary operator, refined the proof of reduction rule, added pattern matching rewrites, add proof for second partial reduction rule

### 5 Nov 2019
* *2 hours* added proofs for rewrites, cleaned up code
* *1 hour* supervisor meeting

### 8 Nov 2019
* *2 hours* added Record for abstract binary operator and id element

## Week 8
### 11 Nov 2019
* *5 hours* refined `partRed`, redution rule, add proof for first partial reduction rule

### 12 Nov 2019
* *3 hours* refining the second partial reduction rule
* *1 hour* meeting with supervisor

### 14 Nov 2019
* *2 hours* adding proof for lemma

## Week 9
* paused
## Week 10
* paused
## Week 11
* paused

## Week 12
* *4.5 hours* refining definition of `partRed`, finished the proof of the second partial reduction rule
### 17 Sec 2019
* *1 hour* meeting with supervisor
### 18 Dec 2019
* *2 hours* writing status report

## Week 13
### 14 Jan 2020
* *1 hour* meeting with supervisor
### 15 Jan 2020
* *2 hours* proving identity rule for vector transpose
* *1 hour* define `padCst` and `mapⁿ`

## Week 14

### 20 Jan 2020
* *2 hours* proving movement rules `mapMapFBeforeTranspose` and `slideBeforeMapMapF`
* *1 hours* refactor code

### 22 Jan 2020
* *2 hours* proving movement rule `joinBeforeTranspose`, useful lemmas were developed
* *2 hours* trying to prove `joinBeforeJoin`, there are some issues caused by dependent types and the associative of `_++_` for `Vec` has not yet been proven.

### 23 Jan 2020
* *5.5 hours* proving movement rule `transposeBeforeMapJoin`, useful lemmas were developed
* *0.5 hour* updating docs, such as timelog

### 24 Jan 2020
* *1 hour* proving movement rules `mapTransposeBeforeJoin` and `mapJoinBeforeTranspose`
* *0.5 hours* simplify existing proof, clean up lemmas

## Week 15
### 28 Jan 2020
* *1 hour* clean up repository

## Week 16
### 03 Feb 2020
* *3 hours* researching about heterogeneous equality and add proof for `JoinBeforeJoin`
* *0.5 hours* redefining `map_n`

### 04 Feb 2020
* *0.5 hours* adding definition of `slide_2`
* *3 hours* proving tiling rule, finished base case

### 05 Feb 2020
* *1 hour* cleaning up repo and add expamle for proving heterogeneous equality
* *5 hours* adding proofs for `transposeBeforeMapSplit`, `mapSplitBeforeTranspose` and `transposeBeforeSplit`

### 06 Feb 2020
* *2 hours* adding proof for `transposeBeforeSlide`

### 07 Feb 2020
* *0.5 hours* adding proofs for `transposeBeforeMapSlide` and `mapSlideBeforeTranspose`
* *0.5 hour* adding declaration for `slideBeforeSplit`
* *0.5 hours* adding documentations and cleanning up code

## Week 17
### 10 Feb 2020
* *2 hours* Adding proofs for lemmas for proving tiling rule

### 11 Feb 2020
* *2 hours* documenting code and add github page for project

### 12 Feb 2020
* *0.5 hours* Updating time log

## Week 18 (17 Feb 2020 - 21 Feb 2020)
* *1 hour* meeting with supervisor
* *3 hours* fixing type system soundness

## Week 19 (24 Feb 2020 - 29 Feb 2020)
* *1 hour* meeting with supervisor

## Week 20 (02 Mar 2020 - 06 Mar 2020)
* *1 hour* meeting with supervisor

## Week 21 (09 Mar 2020 - 13 Mar 2020)
* *1 hour* meeting with supervisor
* *10 hours* writing dissertation

## Week 22 (16 Mar 2020 - 20 Mar 2020)
* *1 hour* meeting with supervisor
* *3 hours* clean up code
* *15 hours* writing dissertation

## Week 23 (23 Mar 2020 - 27 Mar 2020)
* *1 hour* meeting with supervisor
* *3 hours* clean up code
* *15 hours* writing dissertation

## Week 23 (30 Mar 2020 - 03 April 2020)
* *1 hour* meeting with supervisor
* *1 hours* clean up code
* *5 hours* writing dissertation
* *2 hours* recording presentation