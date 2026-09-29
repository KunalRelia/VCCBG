/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 12 (Overall).

  "Given a cubic bridgeless graph G and a vertex v from the vertex cover
   S, if we assign the color blue to vertex v, then there is only one
   way to 2-color (blue and red) the remaining vertices using
   Algorithm C."

  Source: paper §C.2.2, lines 2493–2591 (combining Part 1, Part 2(a),
  and Part 2(b), each proved in its own file).

  ═══════════════════════════════════════════════════════════════════════════
  WHAT EACH IMPORTED FILE PROVIDES (current versions)
  ═══════════════════════════════════════════════════════════════════════════

  From Lemma12 Part1:
    Color (5 constructors), Coloring, VCover  — shared vocabulary
    AlgC, runAlgC, initColoring, fuelBound     — the recursive algorithm
                                                  model (five colors)
    ValidColoring G S nbrOrder v fuel C        — `C = runAlgC G S nbrOrder
                                                  fuel v`
    Lemma12_Part1                              — any two valid colorings
                                                  for the SAME run
                                                  parameters are literally
                                                  equal as functions
    Lemma12_Part1_apply                        — the pointwise restatement

  From Lemma12 Part2a:
    nbrs, blackNbrs, redNbrs                   — the neighborhood split of
                                                  a blue vertex (`G.Adj`-
                                                  based)
    OrderMatchesAdj G nbrOrder                  — bridges `nbrOrder`'s
                                                  algorithmic traversal to
                                                  `G`'s actual adjacency
    Lemma12_Part2a_forcing                      — UNCONDITIONAL forcing:
                                                  every `S`-neighbor of the
                                                  seed ends up black, every
                                                  non-`S`-neighbor ends up
                                                  red — no hypothesis about
                                                  the seed's own eventual
                                                  color needed
    Lemma12_Part2a_unique                       — any two valid colorings
                                                  (same run parameters)
                                                  agree on all of v's
                                                  neighbors (immediate
                                                  corollary of
                                                  `Lemma12_Part1_apply`)
    Lemma12_Part2a_case_i/ii/iii                 — the three named textual
                                                  sub-cases

  From Lemma12 Part2b:
    BR                                          — "blue or red" predicate
    NoBlueBlue / ValidColoring_NoBlueBlue        — no two adjacent vertices
                                                  are ever simultaneously
                                                  blue under a valid
                                                  coloring
    Lemma12_Part2b_conflict                      — if `w ∈ S` has a blue
                                                  neighbor `u`, `w` is
                                                  UNCONDITIONALLY forced
                                                  black (`C w = black`)
    Lemma12_Part2b_some_black                    — an odd cycle forces
                                                  some vertex black (needs
                                                  `VCover G S` explicitly)
    Lemma12_Part2b_oddcycle_no_proper_2coloring
                                                  — the underlying odd-
                                                  cycle parity fact (pure
                                                  combinatorics, unchanged)

  ═══════════════════════════════════════════════════════════════════════════
  THE MATHEMATICAL CONTENT OF "LEMMA 12 OVERALL"
  ═══════════════════════════════════════════════════════════════════════════

  Given a vertex cover `S`, a seed `v ∈ S`, a traversal order `nbrOrder`
  faithfully enumerating `G`'s adjacency (`hOrder`), sufficient fuel, and
  two colorings `C`, `C₂` both valid for `(G, S, nbrOrder, v, fuel)`,
  `Lemma12_Overall` below packages FOUR results into one conjunction:

  (1) CONFLICT RESOLUTION [`Lemma12_Part2b_conflict`] — if some `w ∈ S`
      has a neighbor `u` colored blue under `C`, then `w` itself is
      UNCONDITIONALLY forced black.

  (2) DETERMINISM [`Lemma12_Part1`] — `C` and `C₂`, being valid for the
      SAME run parameters, are literally the SAME function: `C = C₂`.

  (3) UNIQUENESS ON THE SEED'S WHOLE NEIGHBORHOOD
      [`Lemma12_Part2a_unique`] — `C` and `C₂` agree on every neighbor
      of `v` (an immediate corollary of (2), stated separately to match
      the paper's own case-by-case framing of Part 2(a)).

  (4) ODD CYCLES FORCE A BLACK VERTEX [`Lemma12_Part2b_some_black`] —
      for any odd cycle in `G` (given as an explicit witness: length
      `n`, vertex sequence `c`, with the standard wraparound adjacency),
      it is impossible for `C` to color every cycle vertex blue-or-red;
      some vertex must be black.

  Together, (1)–(4) are the precise formal content of the paper's
  informal claim: "Algorithm C always does a unique 2-coloring of the
  graph" (line 2588–2591) — it never contradicts itself (1); it is a
  bona fide deterministic function (2), (3); and odd cycles never
  defeat this because they are always broken by a black vertex (4).
-/

public import VCCBGSecC.thm13_lemma12_2b

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

open Color

-- ═══════════════════════════════════════════════════════════════════════════
-- Lemma 12, Overall — the genuinely new "glue" theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 12 (Overall)** — all four results from the three case-files,
    combined into one conjunction under a single shared hypothesis list.

    Given a vertex cover `S`, a seed `v ∈ S`, a traversal order `nbrOrder`
    faithfully enumerating `G`'s adjacency (`hOrder`), a length bound
    (`hlen`), sufficient fuel (`hfuel`), and two colorings `C`, `C₂` both
    valid for `(G, S, nbrOrder, v, fuel)` (in the recursive-`runAlgC`
    sense of `ValidColoring`, five-color model):

    (1) if `w ∈ S` has a blue neighbor `u` under `C`, `w` is
        UNCONDITIONALLY forced black under `C`
        [`Lemma12_Part2b_conflict`];
    (2) `C` and `C₂` are literally equal as functions [`Lemma12_Part1`];
    (3) `C` and `C₂` agree on every neighbor of `v`
        [`Lemma12_Part2a_unique`];
    (4) for any odd cycle witnessed by `(n, c)`, `C` cannot color every
        cycle vertex blue-or-red [`Lemma12_Part2b_some_black`].

    Every conjunct is a direct invocation of an already-proved theorem
    from one of the three imported modules — no proof is re-derived. -/
public theorem Lemma12_Overall
    {S : Finset V} {v : V} (hS : VCover G S) (hv : v ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ}
    (hfuel : fuelBound (initColoring G S nbrOrder v) (nbrOrder v) ≤ fuel)
    {C C₂ : Coloring V}
    (hVC : ValidColoring G S nbrOrder v fuel C)
    (hVC₂ : ValidColoring G S nbrOrder v fuel C₂) :
    (∀ ⦃w u : V⦄, w ∈ S → G.Adj u w → C u = blue → C w = black)
    ∧
    (C = C₂)
    ∧
    (∀ w ∈ nbrs G v, C w = C₂ w)
    ∧
    (∀ {n : ℕ}, n % 2 = 1 → 0 < n → ∀ {c : ℕ → V},
        (∀ k, G.Adj (c k) (c ((k + 1) % n))) →
        (∀ k, k < n → BR C (c k)) → False) :=
  ⟨fun {w u} hwS hadj hCu =>
      Lemma12_Part2b_conflict G S hv hOrder hlen hfuel hVC hwS hadj hCu,
   Lemma12_Part1 hVC hVC₂,
  fun w hw =>
    Lemma12_Part2a_unique G hVC hVC₂ w hw,
  -- Lemma12_Part2a_unique hVC hVC₂,
   fun {n} hn_odd hn_pos {c} hadj hBR =>
      Lemma12_Part2b_some_black G S hv hOrder hlen hfuel hVC hn_odd hn_pos hadj hBR hS⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  `Lemma12_Overall` is a single proof term — a 4-tuple — built entirely
  from already-proved theorems imported from the three (now five-color)
  case-files:
    Conjunct (1) ← Lemma12_Part2b_conflict   (thm13_lemma12_2b)
    Conjunct (2) ← Lemma12_Part1             (thm13_lemma12_1)
    Conjunct (3) ← Lemma12_Part2a_unique     (thm13_lemma12_2a)
    Conjunct (4) ← Lemma12_Part2b_some_black (thm13_lemma12_2b)

  No tactic script is reproduced and no proof is re-derived anywhere in
  this file: the entire content is the packaging of four imported
  results into the single conjunction that constitutes "Algorithm C
  always does a unique 2-coloring of the graph."
-/
