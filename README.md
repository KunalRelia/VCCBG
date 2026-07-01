# Lean4 Formalization of the VCCBG paper
This repository formalizes the algorithmic results of the vertex cover problem on cubic bridgeless graphs (VCCBG) [paper](https://kunalrelia.github.io/img/VCCBG.pdf) using Lean4. Specifically, we provide the formalization of the proof of correctness of the alternative algorithm presented in Section C of the paper, which proves that VCCBG $\in$ P.

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean installed on your machine.
See [the installation instructions](https://lean-lang.org/install/).

Next, please clone this repository. Then, follow these steps:

```
% cd VCCBG/
% lake exe cache get
% lake build
```

