/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 14

  "Given a cubic bridgeless graph G that is colored using Algorithm C
   and a vertex v from the vertex cover S, the resultant bipartite
   graph is an S-alternating bipartite graph."

  Source: paper §C.2.2, lines 2615–2631.
-/

public import VCCBGSecC.thm13_lemma13

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Color

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Lemma 14 — core membership fact.
-- ═══════════════════════════════════════════════════════════════════════════

variable (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)

/-- **Lemma 14 — core membership fact**:
    under the (deterministic) final coloring `C` produced by `runAlgC`
    seeded at `v0 ∈ S`: if `w` ends up blue, `w ∈ S`; if `w` ends up
    red, `w ∉ S`.

    Paper (lines 2622–2630): "A seed vertex, which is colored blue, is
    always in the vertex cover S. ... a neighboring red vertex is not
    in S as it would be colored 'black' if it were in the vertex cover
    S. ... The neighbors of a red vertex must be in the given vertex
    cover and be colored blue."

    Proof: `ValidColoring_blue_in_S` and `ValidColoring_red_not_S` are
    both GLOBAL, already-exported facts about the final coloring
    (`thm13_lemma12_1`, §9) — no reachability tracking, and
    no fresh induction, is needed here at all. -/
public theorem Lemma14_membership
    {v0 : V} (hv0 : v0 ∈ S)
    {fuel : ℕ} {C : Coloring V}
    (hVC : ValidColoring G S nbrOrder v0 fuel C) :
    ∀ {w : V}, (C w = blue → w ∈ S) ∧ (C w = red → w ∉ S) :=
  fun {w} =>
    ⟨fun hb => ValidColoring_blue_in_S G S nbrOrder hv0 hVC hb,
     fun hr => ValidColoring_red_not_S G S nbrOrder hVC hr⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The blue/red Finsets — kept as `reachU`/`reachW` for downstream
--     compatibility, simply "the blue vertices"/"the red vertices"
--     under the (fully deterministic) final coloring `C`. `v` is
--     carried purely for signature compatibility with
--     `thm13_lemma15` / `thm13_lemma16_*`, which reference
--     `reachU G S C v` positionally.
-- ═══════════════════════════════════════════════════════════════════════════

open Classical in
/-- The Finset of vertices colored blue under `C` — the "U" set of
    Definition 24. (`v` unused — kept for downstream signature
    compatibility.) -/
@[expose] public noncomputable def reachU (G : SimpleGraph V) (S : Finset V) (C : Coloring V)
    (v : V) : Finset V :=
  Finset.univ.filter (fun w => C w = blue)

open Classical in
/-- The Finset of vertices colored red under `C` — the "W" set of
    Definition 24. (`v` unused — kept for downstream signature
    compatibility.) -/
@[expose] public noncomputable def reachW (G : SimpleGraph V) (S : Finset V) (C : Coloring V)
    (v : V) : Finset V :=
  Finset.univ.filter (fun w => C w = red)

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Lemma 14 — the complete S-alternating bipartite graph
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 14**: the bipartite graph induced by Algorithm C's coloring
    (seeded at `v0 ∈ S`) is an S-alternating bipartite graph, in the
    precise sense of Definition 24 (`AltBip`, imported transitively via
    `TheoremTwelveDBG`).

    Paper: "Overall, we have: 1. a set U of blue vertices. It satisfies
    the first condition stated in Definition 24: U ⊆ S. 2. a set V of
    red vertices. It satisfies the second and the only remaining
    condition stated in Definition 24: V ∩ S = ∅. Thus, we can conclude
    that the induced bipartite graph is an S-alternating bipartite
    graph."

    Proof: `disj`/`noU`/`noW`/`cross` reuse `Lemma13_no_blue_blue` /
    `Lemma13_no_red_red` (`thm13_lemma13`) directly. -/
@[expose] public noncomputable def Lemma14_witness
    {v0 : V} (hv0 : v0 ∈ S)
    (hOrder : OrderMatchesAdj G nbrOrder)
    {fuel : ℕ} {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S) :
    AltBip G S where
  toBipSub :=
  { U := reachU G S C v0
    W := reachW G S C v0
    disj := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      rw [hx] at hx'
      exact absurd hx' (by decide)
    noU := by
      intro u w hadj hu hw
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
      exact Lemma13_no_blue_blue hOrder hVC hadj hu hw
    noW := by
      intro u w hadj hu hw
      simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
      exact Lemma13_no_red_red hVC hSVC hadj hu hw
    cross := by
      intro u w hadj hu hwUW
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases Finset.mem_union.mp hwUW with hwU | hwW
      · simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hwU
        exact absurd hwU
          (fun hCwb => Lemma13_no_blue_blue hOrder hVC hadj hu hCwb)
      · exact hwW }
  U_sub := by
    intro x hx
    simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact (Lemma14_membership G S nbrOrder hv0 hVC).1 hx
  W_disj := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact (Lemma14_membership G S nbrOrder hv0 hVC).2 hx

/-- **Lemma 14** (theorem form): the bipartite graph induced by
    Algorithm C's coloring, seeded at `v0 ∈ S`, IS an S-alternating
    bipartite graph — i.e. an `AltBip G S` exists whose `U`/`W` are
    exactly the blue/red vertices of `C`. -/
public theorem Lemma14
    {v0 : V} (hv0 : v0 ∈ S)
    (hOrder : OrderMatchesAdj G nbrOrder)
    {fuel : ℕ} {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S) :
    ∃ A : AltBip G S,
      A.toBipSub.U = reachU G S C v0 ∧ A.toBipSub.W = reachW G S C v0 :=
  ⟨Lemma14_witness G S nbrOrder hv0 hOrder hVC hSVC, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Proof map:
    Lemma14_membership       — ONE-LINE pairing of `ValidColoring_blue_in_S`
                               and `ValidColoring_red_not_S`, BOTH already
                               exported (with zero axioms) by
                               `thm13_lemma12_1`'s own §9 — no
                               fresh induction needed in THIS file at all.
    reachU, reachW            — Finset.univ.filter over `C x = blue` /
                               `C x = red` directly (no reachability
                               conjunct); `v` kept unused for signature
                               compatibility with Lemma15/16.
    Lemma14_witness           — `def`: assembles a complete
                               (imported) `AltBip G S` term:
                                 disj/noU/noW/cross — reuse
                                   `Lemma13_no_blue_blue` /
                                   `Lemma13_no_red_red`
                                   (thm13_lemma13) directly.
                                 U_sub/W_disj — directly from
                                   `Lemma14_membership`, called with
                                   `G S nbrOrder` as explicit leading
                                   arguments.
    Lemma14                   — `theorem`: wraps `Lemma14_witness` in
                               an existential, both projection
                               equalities closed by `rfl`.
-/
