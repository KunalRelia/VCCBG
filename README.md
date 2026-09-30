# VCCBG Formalization

This repository contains the formal verification in **Lean** of results from the paper on the computational complexity of the **Vertex Cover Problem on Cubic Bridgeless Graphs (VCCBG)**. 

Specifically, this repository formalizes:
1. an unconditional deterministic polynomial-time exact algorithm for VCCBG (Theorem 2, Part II).
2. the proof of NP-completeness of VCCBG (Theorem 1, Section B)
3. the proof of correctness of an alternative unconditional deterministic polynomial-time exact algorithm for VCCBG (Theorem 13, Section C). 

---

## Overview of the Formalization

### Theorem 2, Part II (VCCBG is in P)

**Theorem 2** is proven via the conjunction of two main theorems: **Theorem 8** (proof of correctness of Algorithm 1) and **Theorem 9** (Algorithm 1 runs in O(m^5) time). Specifically, **Theorem 8** is proven via the conjunction of two main lemmas:
1. **Lemma 6 (Soundness):** *"If Algorithm 1 returns Yes, then the given instance of VC–CBG is a Yes instance."*
2. **Lemma 5 (Completeness):** *"If the given instance of VC–CBG is a Yes instance, then Algorithm 1 returns Yes."*

#### Key Concepts & Analogies
The formalization strictly mirrors the structure of the paper, covering:
* **Novel Data Structure:** Represents table.
* **Novel Concept:** *Diminishing hops* (conceptually analogous to augmenting paths used for maximum matching).
* **Graph-Theoretic Theorem:** Bridging diminishing hops and minimum vertex cover (analogous to Berge's Theorem).
* **Algorithmic Result:** An algorithm utilizing diminishing hops to find a minimum vertex cover (analogous to the Blossom Algorithm using augmenting paths to find maximum matching due to Berge's Theorem).

<img src="https://github.com/KunalRelia/kunalrelia.github.io/blob/master/img/APMM-DHMVC.png" alt="Analogy betweeen Augmenting Paths and Diminishing Hops" width="500"/>

---

### Theorem 1, Section B (VCCBG is NP-complete)

**Theorem 1** is proven by proof by reduction:
1. vertex cover problem on 2-vertex-connected cubic planar graphs is NP-complete [Mohar, 2001].
2. every 2-vertex-connected graph is bridgeless [Whitney, 1932].
    - vertex cover problem on bridgeless cubic planar graphs is NP-complete.
3. vertex cover problem on bridgeless cubic graphs is NP-complete.

We axiomatize the previously published results (e.g., Mohar's result. For a summary, please see [VCCBGMain.lean](https://github.com/KunalRelia/VCCBG/blob/main/VCCBGMain.lean)). 

--- 

### Theorem 13, Section C (Proof of Correctness of the Alternative Algorithm)

**Theorem 13** is proven via the conjunction of two main lemmas:
1. **Lemma 10 (Soundness):** *"If Algorithm A returns Yes, then the given instance of VC–CBG is a Yes instance."*
2. **Lemma 9 (Completeness):** *"If the given instance of VC–CBG is a Yes instance, then Algorithm A returns Yes."*

#### Key Concepts & Analogies
The formalization strictly mirrors the structure of the paper, covering:
* **Novel Concepts:** *Alternating bipartite graphs and diminishing bipartite graphs* (conceptually analogous to alternating paths and augmenting paths used for maximum matching).
* **Graph-Theoretic Theorem:** Bridging diminishing bipartite graphs and minimum vertex cover (analogous to Berge's Theorem).
* **Algorithmic Result:** An algorithm utilizing diminishing bipartite graphs to find a minimum vertex cover (analogous to the Blossom Algorithm using augmenting paths to find maximum matching due to Berge's Theorem).

We axiomatize the previously published results. **Importantly**, we axiomatize an unpublished result that is proven in the paper.

--- 

## Building & Verification
To build the Lean files of this project, you need to have a working version of Lean installed on your machine. See [the installation instructions](https://lean-lang.org/install/).

Next, please clone this repository. Then, follow these steps:

```
% cd VCCBG/
% lake exe cache get (or lake exe cache get! for complete download)
% lake build
```

---

## Related Repositories
The previous version of this GitHub repository formalizing earlier algorithms in Section C of the VCCBG paper has been moved [here](https://github.com/KunalRelia/VCCBG-SecC-Legacy) to a legacy repository.

A strict subset of the formalization, specifically Part II's proof of correctness, can be found here: [KunalRelia/VCCBG-PartII-Palomar](https://github.com/KunalRelia/VCCBG-PartII-Palomar).

---

## AI Assistance Disclaimer
The Lean code in this repository was generated and refined iteratively using Claude (Sonnet 4.6 / 5 / 5.5 using the Low / Medium / Max thinking modes), with Gemini (3.6 Flash / 3.1 Pro) used as an additional source for some code. Gemini, GPT, and Claude were also utilized for debugging, with careful cross-checking to ensure logical soundness and freedom from context bias. All proofs have been checked and verified by the Lean theorem prover.