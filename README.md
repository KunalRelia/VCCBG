# Lean4 Formalization of the VCCBG paper
This repository is aimed at formalizing the algorithmic results of the vertex cover problem on cubic bridgeless graphs (VCCBG) [paper](https://kunalrelia.github.io/img/VCCBG.pdf) using Lean4. Currently, we are focusing on the formalization of the proof of correctness of the alternative algorithm presented in Section C of the paper, which proves that VCCBG $\in$ P.

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean installed on your machine.
See [the installation instructions](https://lean-lang.org/install/).

Next, please clone this repository. Then, follow these steps:

```
% cd VCCBG/
% lake exe cache get (or lake exe cache get! for complete download)
% lake build
```

## Status
We have completed the formalization of key proofs ("Goals Accomplished!"). However, we used a couple of axioms to do so. Hence, to ensure the Lean formalization is unconditional (assumption-free) just like the paper's results, we are refactoring or reengineering many files. Therefore, the Lean code in this repository is divided into two bins: completed and in-progress. 

### Completed: 
* Thm12.lean
* Thm13Lemma9.lean
* Thm13Lemma11.lean

### In-progress:
all other files
