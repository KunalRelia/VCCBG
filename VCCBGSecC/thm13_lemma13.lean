/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 13   [v3 — updated for the FIVE-COLOR
  Algorithm-C model (white/blue/red/black/yellow), matching
  `thm13_lemma12_overall.lean` and its predecessor chain:
  `thm13_lemma12_1` / `thm13_lemma12_2a` /
  `thm13_lemma12_2b`.]

  "Given a cubic bridgeless graph G and a vertex v from the vertex cover
   S, if the graph is colored using Algorithm C by seeding on vertex v,
   then the red and blue vertices form a bipartite graph."

  Source: paper §C.2.2, lines 2592–2614 (and footnote 52).
-/

public import VCCBGSecC.thm13_lemma12_overall

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

open Color

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The two structural facts, re-derived from the five-color recursive
--     model.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **No-blue-blue**: no two adjacent vertices are both blue, under the
    final coloring produced by `runAlgC` seeded at `v0 ∈ S`.

    Paper (lines 2603–2604): "A neighboring vertex of a blue vertex that
    is also in the vertex cover S is colored black. By design, no
    adjacent vertices can be colored blue."

    Proof: immediate from `ValidColoring_NoBlueBlue`
    (`thm13_lemma12_2b`), which establishes the genuine
    `NoBlueBlue` invariant — no two adjacent vertices are EVER
    simultaneously blue under a valid coloring. -/
public theorem Lemma13_no_blue_blue
    {S : Finset V}
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    {v0 : V} {fuel : ℕ}
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    {u w : V} (hadj : G.Adj u w) (hCu : C u = blue) (hCw : C w = blue) :
    False :=
  ValidColoring_NoBlueBlue G S nbrOrder hOrder hVC u w hadj hCu hCw

/-- **No-red-red**: no two adjacent vertices are both red, under the
    final coloring produced by `runAlgC` seeded at `v0 ∈ S`.

    Paper (lines 2605–2608): "A neighboring vertex of a red vertex that
    is also not in the vertex cover S is not possible because the red
    vertex, by design, is not in the vertex cover S. Therefore, its
    neighbor must be in the given vertex cover S for it to be a valid
    vertex cover."

    Proof: `ValidColoring_red_not_S` (imported via
    `thm13_lemma12_1`, threaded through `_2a` / `_2b`)
    shows any red vertex under a valid coloring lies outside `S`. So if
    `u`, `w` are both red, both lie outside `S`, directly contradicting
    `VCover G S` applied to the edge `(u, w)`, which demands
    `u ∈ S ∨ w ∈ S`. -/
public theorem Lemma13_no_red_red
    {S : Finset V} {v0 : V}
    {nbrOrder : V → List V}
    {fuel : ℕ}
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S)
    {u w : V} (hadj : G.Adj u w) (hCu : C u = red) (hCw : C w = red) :
    False := by
  have huS : u ∉ S := ValidColoring_red_not_S G S nbrOrder hVC hCu
  have hwS : w ∉ S := ValidColoring_red_not_S G S nbrOrder hVC hCw
  rcases hSVC hadj with h | h
  · exact huS h
  · exact hwS h

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Bipartite-structure packaging
-- ═══════════════════════════════════════════════════════════════════════════

/-- `BipColoring G U W`: the predicates `U`, `W` form a bipartition of
    (a subset of) the vertices of `G` with no internal edges — the
    precise structural content of "the induced subgraph on `U ∪ W` is
    bipartite." -/
public structure BipColoring (G : SimpleGraph V) (U W : V → Prop) : Prop where
  /-- No vertex is both `U` and `W`. -/
  disj : ∀ x, ¬ (U x ∧ W x)
  /-- No two adjacent vertices are both `U`. -/
  noU  : ∀ ⦃u w⦄, G.Adj u w → U u → ¬ U w
  /-- No two adjacent vertices are both `W`. -/
  noW  : ∀ ⦃u w⦄, G.Adj u w → W u → ¬ W w

/-- **Lemma 13**: under the coloring produced by `runAlgC` seeded at
    `v0 ∈ S` (with `nbrOrder` faithfully enumerating `G`'s adjacency,
    sufficient fuel, and `S` a genuine vertex cover), the blue vertices
    and the red vertices form a bipartite graph.

    Paper (lines 2609–2611): "the 2-coloring (red and blue) of the
    graph G done by Algorithm C, by definition, implies that the
    induced subgraph of red and blue vertices is a bipartite graph."

    Proof: `disj` is immediate (a vertex's color is a single value, so
    it cannot be both `blue` and `red` at once — `Color.noConfusion`
    via `decide`). `noU` is `Lemma13_no_blue_blue`; `noW` is
    `Lemma13_no_red_red`. -/
public theorem Lemma13
    {S : Finset V} {v0 : V}
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    {fuel : ℕ}
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S) :
    BipColoring G (fun x => C x = blue) (fun x => C x = red) where
  disj := fun x ⟨hb, hr⟩ => by rw [hb] at hr; exact absurd hr (by decide)
  noU  := fun u w hadj hCu hCw =>
    Lemma13_no_blue_blue hOrder hVC hadj hCu hCw
  noW  := fun u w hadj hCu hCw =>
    Lemma13_no_red_red hVC hSVC hadj hCu hCw

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Proof map:
    Lemma13_no_blue_blue — ONE LINE: direct application of
                           `ValidColoring_NoBlueBlue`
                           (thm13_lemma12_2b), which itself
                           establishes `NoBlueBlue` with no
                           temporal/ordering argument, purely from the
                           forward-preserved `BlueNbrsResolved`
                           invariant already exported by
                           `thm13_lemma12_1`.
    Lemma13_no_red_red   — UNCHANGED in substance from v2:
                           `ValidColoring_red_not_S` (`lemma12_1`) applied to
                           both `u` and `w`; `VCover G S` applied to the
                           edge `(u, w)` then contradicts both being
                           `∉ S`. Only the calling convention changed
                           (`G S nbrOrder` now explicit leading
                           arguments).                          (6 lines)
    BipColoring          — predicate-level bipartition structure,
                           UNCHANGED from v1/v2, no `[Fintype V]`
                           required for the structure itself.
    Lemma13              — `disj` trivial (`Color.noConfusion` via
                           `decide`); `noU`/`noW` are exactly the two
                           theorems above, now taking the five-color
                           model's hypothesis list
                           (`hOrder`, `hVC`, `hSVC`) instead of the
                           four-color model's.
-/
