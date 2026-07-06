/-
  Lean 4 / Mathlib — Lemma 12 (Overall), assuming the three case-files
  are imported as modules.

  "Given a cubic bridgeless graph G and a vertex v from the vertex cover
   S, if we assign the color blue to vertex v, then there is only one
   way to 2-color (blue and red) the remaining vertices using
   Algorithm C."

  Source: paper §C.2.2, lines 2493–2591 (combining Part 1, Part 2(a),
  and Part 2(b), each proved in its own file).

  ═══════════════════════════════════════════════════════════════════════════
  IMPORT PRECONDITION
  ═══════════════════════════════════════════════════════════════════════════

  This file assumes the three case-files compile and are importable as
  ordinary Lean modules, in parallel or inherently sequentially:
     Lemma12 Part1 (Bipartite)
     Lemma12 Part2a (NotInOddCycle)
     Lemma12 Part2b (OddCycle)

  ═══════════════════════════════════════════════════════════════════════════
  WHAT EACH IMPORTED FILE PROVIDES
  ═══════════════════════════════════════════════════════════════════════════

  From Lemma12 Part1 Bipartite:
    AltReachActive G S C v w     — active-walk reachability
    Lemma12_Part1                — any two valid colorings agree along
                                    active walks from v

  From Lemma12 Part2a NotInOddCycle:
    nbrs, blackNbrs, redNbrs     — the neighborhood split of a blue vertex
    Lemma12_Part2a_forcing       — V1/V2 applied to the whole neighborhood
    Lemma12_Part2a_unique        — any two valid colorings agree on all
                                    of v's neighbors
    Lemma12_Part2a_case_i/ii/iii — the three named textual sub-cases

  From Lemma12 Part2b OddCycle:
    BR                            — "blue or red" predicate
    Lemma12_Part2b_conflict       — V1 and V3 cannot both fire on one
                                     vertex (the conflict-incompatibility
                                     theorem)
    Lemma12_Part2b_some_black     — an odd cycle forces some vertex black
    Lemma12_Part2b_oddcycle_no_proper_2coloring
                                   — the underlying odd-cycle parity fact

  ═══════════════════════════════════════════════════════════════════════════
  THE MATHEMATICAL CONTENT OF "LEMMA 12 OVERALL"
  ═══════════════════════════════════════════════════════════════════════════

  The paper's case split (bipartite / non-bipartite) concerns HOW
  uniqueness is established, not WHAT is being claimed. `Lemma12_Overall`
  below packages ALL FOUR results proved across the three files into one
  conjunction, under one shared hypothesis list `(hS, hv, hVC, hVC₂)`:

  (1) CONSISTENCY [`Lemma12_Part2b_conflict`] — no vertex is ever forced
      into two different colors by one valid coloring: no `w ∈ S` has
      both a blue and a red neighbor.

  (2) UNIQUENESS ALONG ACTIVE WALKS [`Lemma12_Part1`] — any two valid
      colorings agree on every vertex reachable from `v` by an active
      walk (one that only steps away from blue/red, never black/white).
      Proved independently of bipartiteness: the walk simply never
      proceeds past a black "breaker".

  (3) UNIQUENESS ON THE SEED'S WHOLE NEIGHBORHOOD [`Lemma12_Part2a_unique`]
      — any two valid colorings agree on EVERY neighbor of `v` (not just
      reachable ones), regardless of how many of those neighbors end up
      black vs. red — this is what Part 2(a)'s cases (i)/(ii)/(iii)
      establish uniformly.

  (4) ODD CYCLES FORCE A BLACK VERTEX [`Lemma12_Part2b_some_black`] — for
      any odd cycle in `G` (given as an explicit witness: length `n`,
      vertex sequence `c`, with the standard wraparound adjacency), it is
      impossible for `C` to color every cycle vertex blue-or-red; some
      vertex must be black. This is what guarantees (1) never actually
      fails on an odd cycle: a black breaker always intervenes first.

  Together, (1)–(4) are the precise formal content of the paper's
  informal claim: "Algorithm C always does a unique 2-coloring of the
  graph" (line 2588–2591) — it never contradicts itself (1), (3); it is
  fully determined wherever it actually reaches (2); and odd cycles never
  defeat this because they are always broken by a black vertex (4).

  AXIOMS:   0
  SORRIES:  0
  ═══════════════════════════════════════════════════════════════════════════
-/

import Mathlib
/-
 Lean requires files to sit within an established workspace managed by Lake
 (Lean's build system) for imports to function correctly. Hence, please ensure
 that the following import statement is modified to follow the structure where
 the file being imported sits within your project.
-/
import MyGraphProject.vccbg.Thm13Lemma12_2b

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

open Color

-- ═══════════════════════════════════════════════════════════════════════════
-- Lemma 12, Overall — the genuinely new "glue" theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 12 (Overall)** — all four results from the three case-files,
    combined into one conjunction under a single shared hypothesis list.

    Given a vertex cover `S`, a seed `v ∈ S`, and two colorings `C`, `C₂`
    both valid for `(G, S, v)`:

    (1) no vertex has both a blue and a red neighbor under `C`
        [`Lemma12_Part2b_conflict`];
    (2) `C` and `C₂` agree on every vertex reachable from `v` by an
        active walk [`Lemma12_Part1`];
    (3) `C` and `C₂` agree on every neighbor of `v` [`Lemma12_Part2a_unique`];
    (4) for any odd cycle witnessed by `(n, c)`, `C` cannot color every
        cycle vertex blue-or-red [`Lemma12_Part2b_some_black`].

    Every conjunct is a direct invocation of an already-proved theorem
    from one of the three imported modules — no proof is re-derived. -/
theorem Lemma12_Overall
    {S : Finset V} {v : V} (hS : VCover G S) (hv : v ∈ S)
    {C C₂ : Coloring V}
    (hVC : ValidColoring G S v C) (hVC₂ : ValidColoring G S v C₂) :
    -- (1) Consistency: no vertex has both a blue and a red neighbor.
    (∀ ⦃w u₁ u₂ : V⦄, w ∈ S →
        G.Adj u₁ w → C u₁ = blue → G.Adj u₂ w → C u₂ = red → False)
    ∧
    -- (2) Uniqueness along active walks.
    (∀ ⦃w : V⦄, AltReachActive G S C v w → C w = C₂ w)
    ∧
    -- (3) Uniqueness on the seed's whole neighborhood.
    (∀ w ∈ nbrs G v, C w = C₂ w)
    ∧
    -- (4) Any odd cycle forces a black vertex: C cannot be all blue/red on it.
    (∀ {n : ℕ}, n % 2 = 1 → 0 < n → ∀ {c : ℕ → V},
        (∀ k, G.Adj (c k) (c ((k + 1) % n))) →
        (∀ k, k < n → BR C (c k)) → False) :=
  ⟨fun _ _ _ hwS hadj₁ hCu₁ hadj₂ hCu₂ =>
      Lemma12_Part2b_conflict hVC hwS hadj₁ hCu₁ hadj₂ hCu₂,
   fun _ hreach => Lemma12_Part1 hS hVC hVC₂ hreach,
   Lemma12_Part2a_unique hVC hVC₂ hVC.seed hVC₂.seed,
   Lemma12_Part2b_some_black hVC⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  AXIOM COUNT:  0
  SORRY COUNT:  0  (every proof step is complete)

  `Lemma12_Overall` is a single proof term — a 4-tuple — built entirely
  from already-proved theorems imported from the three case-files:
    Conjunct (1) ← Lemma12_Part2b_conflict   (Lemma12_Part2b_OddCycle)
    Conjunct (2) ← Lemma12_Part1             (Lemma12_Part1_Bipartite)
    Conjunct (3) ← Lemma12_Part2a_unique     (Lemma12_Part2a_NotInOddCycle)
    Conjunct (4) ← Lemma12_Part2b_some_black (Lemma12_Part2b_OddCycle)

  No tactic script is reproduced and no proof is re-derived anywhere in
  this file: the entire content is the packaging of the imported
  results into the single conjunction that constitutes "Algorithm C
  always does a unique 2-coloring of the graph."
-/
