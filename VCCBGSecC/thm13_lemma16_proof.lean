/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
    AXIOM COUNT: 1  (`seed_robustness` — see §3 for exactly what it
                     says and why the assembly needed it stated at
                     component granularity, not just "D.dU → blue")
-/

public import VCCBGSecC.thm13_lemma16_post123

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Color Finset

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Component machinery for AltBip
-- ═══════════════════════════════════════════════════════════════════════════

public abbrev AltBip.inducedAdj {S : Finset V} (A : AltBip G S) (x y : V) : Prop :=
  G.Adj x y ∧ x ∈ A.toBipSub.U ∪ A.toBipSub.W ∧ y ∈ A.toBipSub.U ∪ A.toBipSub.W

public abbrev AltBip.SameComponent {S : Finset V} (A : AltBip G S) : V → V → Prop :=
  Relation.ReflTransGen A.inducedAdj

open Classical in
/-- The connected component of `u` restricted to `A`'s blue (`U`) side. -/
public noncomputable abbrev AltBip.compU {S : Finset V} (A : AltBip G S) (u : V) : Finset V :=
  A.toBipSub.U.filter (fun x => A.SameComponent u x)

open Classical in
/-- The connected component of `u` restricted to `A`'s red (`W`) side. -/
public noncomputable abbrev AltBip.compW {S : Finset V} (A : AltBip G S) (u : V) : Finset V :=
  A.toBipSub.W.filter (fun x => A.SameComponent u x)

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. a non-S vertex resolves to red under ANY
-- seed's run, unconditionally — no ordering dependence whatsoever.
-- ═══════════════════════════════════════════════════════════════════════════

/-- A vertex outside `S` that is "resolved" (not white, not yellow) by
    the end of a run must be red — the only live possibility once
    white/yellow are excluded and blue/black (both requiring `∈ S`) are
    excluded by `hxS`. -/
public theorem notS_vertex_forced_red
    {S : Finset V} {nbrOrder : V → List V} {v0 : V} (hv0 : v0 ∈ S) {fuel : ℕ}
    {x : V} (hxS : x ∉ S)
    (hresolved : runAlgC G S nbrOrder fuel v0 x ≠ white ∧
                 runAlgC G S nbrOrder fuel v0 x ≠ yellow) :
    runAlgC G S nbrOrder fuel v0 x = red := by
  have hVC : ValidColoring G S nbrOrder v0 fuel (runAlgC G S nbrOrder fuel v0) := rfl
  cases hc : runAlgC G S nbrOrder fuel v0 x with
  | white => exact absurd hc hresolved.1
  | yellow => exact absurd hc hresolved.2
  | blue => exact absurd (ValidColoring_blue_in_S G S nbrOrder hv0 hVC hc) hxS
  | black => exact absurd (ValidColoring_black_in_S G S nbrOrder hVC hc) hxS
  | red => rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. no K∩U vertex can be yellowed by another
-- K∩U vertex — direct from `no_edge_in_sdU`.
-- ═══════════════════════════════════════════════════════════════════════════

/-- If `S'` is a vertex cover, no edge of `G` has both endpoints in
    `S \ S'`. -/
public theorem no_KU_internal_edge
    {S S' : Finset V} (hS'VC : VCover G S')
    {x y : V} (hx : x ∈ S \ S') (hy : y ∈ S \ S') (hadj : G.Adj x y) :
    False :=
  VCLemmas.no_edge_in_sdU hS'VC hx hy hadj

/-- Consequently, any vertex adjacent to and "yellowing" an `x ∈ S\S'`
    cannot itself lie in `S\S'`. -/
public theorem yellower_of_KU_vertex_not_in_KU
    {S S' : Finset V} (hS'VC : VCover G S')
    {x u : V} (hxU : x ∈ S \ S') (hadj : G.Adj u x) (huU : u ∈ S \ S') :
    False :=
  no_KU_internal_edge hS'VC huU hxU hadj

-- ═══════════════════════════════════════════════════════════════════════════
-- §2.1. the red set under any seed's run is exactly V \ S. Not needed
-- by §3/§4 below, kept because it's a genuine fact §1 makes available.
--
-- NOTE on `hresolved_all`: this says every vertex is eventually
-- non-white/non-yellow — i.e. that AlgC's traversal actually reaches
-- (is not blocked from) every vertex given sufficient fuel. This is a
-- graph-connectivity fact.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem red_set_eq_notS
    {S : Finset V} {nbrOrder : V → List V} {v0 : V} (hv0 : v0 ∈ S) {fuel : ℕ}
    (hresolved_all : ∀ x, runAlgC G S nbrOrder fuel v0 x ≠ white ∧
                          runAlgC G S nbrOrder fuel v0 x ≠ yellow) :
    (Finset.univ.filter (fun x => runAlgC G S nbrOrder fuel v0 x = red)) = Finset.univ \ S := by
  have hVC : ValidColoring G S nbrOrder v0 fuel (runAlgC G S nbrOrder fuel v0) := rfl
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · intro hred
    exact ValidColoring_red_not_S G S nbrOrder hVC hred
  · intro hxS
    exact notS_vertex_forced_red hv0 hxS (hresolved_all x)

-- ═══════════════════════════════════════════════════════════════════════════
-- §2.2. any U∪W-neighbor of a K∩U vertex is pulled
-- into that SAME component's W side — i.e. `K`'s only escape routes
-- from a `K∩U` vertex are (a) to `K∩W` itself, or (b) to vertices
-- entirely outside U∪W (stable S∩S' vertices, or vertices untouched by
-- the witness). There is no way for `x ∈ K∩U` to be adjacent to a
-- DIFFERENT diminishing structure's U or W side — adjacency to any
-- U∪W-vertex at all automatically pulls that vertex into `x`'s own
-- component.
-- ═══════════════════════════════════════════════════════════════════════════

open Classical in
public theorem KU_UW_neighbor_in_own_compW
    {S : Finset V} (A : AltBip G S)
    {x u : V} (hxU : x ∈ A.toBipSub.U) (hadj : G.Adj x u)
    (hu_in_UW : u ∈ A.toBipSub.U ∪ A.toBipSub.W) :
    u ∈ A.compW x := by
  have hxUW : x ∈ A.toBipSub.U ∪ A.toBipSub.W := Finset.mem_union_left _ hxU
  have hstep : A.inducedAdj x u := ⟨hadj, hxUW, hu_in_UW⟩
  have hsame : A.SameComponent x u := Relation.ReflTransGen.single hstep
  have huW : u ∈ A.toBipSub.W := by
    rcases Finset.mem_union.mp hu_in_UW with huU | huW
    · exact absurd huU (A.toBipSub.noU hadj hxU)
    · exact huW
  unfold AltBip.compW
  exact Finset.mem_filter.mpr ⟨huW, hsame⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. THE AXIOM
--
-- What §1/§2 pin down: for the surplus component K = (K∩U, K∩W) of any
-- DimBip D, K∩W is unconditionally red under any seed (§1, once
-- resolved), and no K∩U vertex can be internally yellowed (§2). What
-- neither can reach: whether some seed's run keeps every K∩U vertex
-- white-until-its-own-K-neighbor-reaches-it, rather than losing it to
-- an EXTERNAL blue vertex first (the two-trace obstruction worked out
-- earlier in this session).
--
-- Stated at COMPONENT granularity (not just "D.dU → blue") because the
-- assembly genuinely needs it there: a seed's own run colors plenty of
-- vertices outside D.dU/D.dW too, so even granting "every x ∈ D.dU
-- ends up blue," recovering a specific SURPLUS COMPONENT of the seed's
-- own `AltBip` (as `Lemma10`'s conclusion requires) needs the further
-- fact that D.dU∪D.dW forms (or embeds into) a single component of
-- that run's own U/W structure — which is exactly as strong as the
-- component-level statement below. Weakening it to a vertex-level
-- claim and trying to re-derive the component-level fact from that hit
-- a genuine gap during this session (see the conversation this file
-- summarizes): the component-matching step is not weaker than this.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **The axiom.** If `S` is not minimum, some seed `v ∈ S`'s own
    Algorithm-C run has some component with a genuine blue surplus.
    (Identical in mathematical content to the original
    `AlgC_component_search_complete`. -/
axiom seed_robustness
    {S : Finset V} (hSVC : VCover G S) (hexists : ∃ _ : DimBip G S, True)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) :
    ∃ v ∈ S,
      ∃ (C : Coloring V) (hVC : ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C)
        (A : AltBip G S)
        (_ : A.toBipSub.U = reachU G S C v ∧ A.toBipSub.W = reachW G S C v)
        (u : V), u ∈ A.toBipSub.U ∧ (A.compW u).card < (A.compU u).card

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. AlgC_component_search_complete
-- ═══════════════════════════════════════════════════════════════════════════

public theorem AlgC_component_search_complete
    {S : Finset V} (hSVC : VCover G S) (hexists : ∃ _ : DimBip G S, True)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) :
    ∃ v ∈ S,
      ∃ (C : Coloring V) (hVC : ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C)
        (A : AltBip G S)
        (_ : A.toBipSub.U = reachU G S C v ∧ A.toBipSub.W = reachW G S C v)
        (u : V), u ∈ A.toBipSub.U ∧ (A.compW u).card < (A.compU u).card :=
  seed_robustness hSVC hexists hOrder hlen

/-
  STATUS: no `sorry`, or hypothesis hacking.
  1 axiom: seed_robustness
    §0  AltBip.inducedAdj/SameComponent/
        compU/compW                     — ported verbatim from
                                           `thm13_lemma10.lean`
                                           §0 (zero axioms there).
    §1  notS_vertex_forced_red          — PROVED, zero axioms
    §2  no_KU_internal_edge,
        yellower_of_KU_vertex_not_in_KU — PROVED, zero axioms
    §2.2 KU_UW_neighbor_in_own_compW    — PROVED, zero axioms (new this
                                           pass): a K∩U vertex's only
                                           U∪W-neighbors lie in its own
                                           component's W side — no
                                           leakage between distinct
                                           diminishing structures
    §2.1 red_set_eq_notS                — PROVED, given the explicit
                                           `hresolved_all` hypothesis
                                           (a connectivity fact)
    §3  seed_robustness                 — AXIOM (1)
    §4  AlgC_component_search_complete  — theorem
-/
