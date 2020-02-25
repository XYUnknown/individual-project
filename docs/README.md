# ReADmE
## Project: Proving the Correctness of Rewrite Rules in LIFT’s Rewrite-Based System
The approach of LIFT is to provide high-performance high-level programming with code portability. LIFT achieves this via a rewrite-based system to transform and optimise programs. 

The rewrite system of LIFT systematically transforms high-level algorithmic patterns into low-level high-performance OpenCL code with equivalent functionality. During this process, a set of rewrite rules are applied. Ensuring the correctness of these rules is important for ensuring the functionality is not altered during the rewrite process. Currently, the correctness of these rules is only proven correct on paper and only for a subset of the used rules. Thus, in this project, I will develop mechanical proofs using the proof assistant tool Agda to show the correctness of the rewrite rules used in LIFT code rewrite system.

This web page serves as a record of the development process and results in the project.
Here is a list of things the developer is ~~struggling with~~ interested in:
1. Formalising complex tensor operations in Agda
2. Pattern matching on `Vec`s with complex sizes, such as ` Vec t (sz + n * (suc sp) + (suc m) * suc (n + sp + n * sp))`
3. Agda `REWRITE` pragma
4. Proof irrelevence and without-K
5. Heterogeneous equality

## Posts
1. A list of proven rewrite rules: [List](https://xyunknown.github.io/individual-project/list.lagda)
