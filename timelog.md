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