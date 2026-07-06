/-
  Formal Lean 4 / Mathlib Verification of Theorem 12
  "Diminishing Bipartite Graph and Vertex Cover"

  Source: §C.1.2 of the paper (lines 2325–2413).
-/

import Mathlib

-- Suppress linter noise about unused typeclass hypotheses.
-- These are pulled in by the section `variable`s for statements that
-- need them globally but individual lemmas may not use all of them.
-- For example, cubic and bridgeless properties are necessary downstream.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Vertex covers
-- ═══════════════════════════════════════════════════════════════════════════

/-- `VCover G S`: every edge of G has at least one endpoint in S. -/
def VCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ S ∨ v ∈ S

/-- `MinVCover G S`: S is a vertex cover of minimum cardinality. -/
def MinVCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  VCover G S ∧ ∀ T : Finset V, VCover G T → S.card ≤ T.card

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Structures (Definitions 24 and 25 of the paper)
-- ═══════════════════════════════════════════════════════════════════════════

/-- `BipSub G`: an induced bipartite subgraph with bipartition (U, W).
    ("W" is the paper's "V_set"; renamed to avoid shadowing the universe `V`.) -/
structure BipSub (G : SimpleGraph V) where
  U : Finset V
  W    : Finset V
  disj  : Disjoint U W
  noU   : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ U → v ∉ U
  noW   : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ W → v ∉ W
  cross : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ U → v ∈ U ∪ W → v ∈ W

/-- **Definition 24**: S-alternating bipartite graph.
    U ⊆ S  and  W ∩ S = ∅. -/
structure AltBip (G : SimpleGraph V) (S : Finset V) extends BipSub G where
  U_sub : toBipSub.U ⊆ S
  W_disj : Disjoint toBipSub.W S

/-- **Definition 25**: S-diminishing bipartite graph.
    Alternating, U nonempty, |U| > |W|, flipping yields a valid cover. -/
structure DimBip (G : SimpleGraph V) (S : Finset V) extends AltBip G S where
  U_ne : toAltBip.toBipSub.U.Nonempty
  U_gt_W  : toAltBip.toBipSub.W.card < toAltBip.toBipSub.U.card
  flip_vc : VCover G ((S \ toAltBip.toBipSub.U) ∪ toAltBip.toBipSub.W)

namespace DimBip

variable {S : Finset V}

abbrev dU (D : DimBip G S) : Finset V := D.toAltBip.toBipSub.U
abbrev dW (D : DimBip G S) : Finset V := D.toAltBip.toBipSub.W

/-- The flipped cover S' = (S \ U) ∪ W. -/
def flipped (D : DimBip G S) : Finset V := (S \ D.dU) ∪ D.dW

end DimBip

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Lemmas
-- ═══════════════════════════════════════════════════════════════════════════

namespace VCLemmas

variable {S : Finset V}

-- ─────────────────────────────────────────────────────────────────────────
-- §3.1  Cardinality of a set-difference when one set is a subset
-- ─────────────────────────────────────────────────────────────────────────

/-- If s ⊆ t then #(t \ s) = #t - #s.
    Proved from the partition t = (t ∩ s) ∪ (t \ s) together with
    t ∩ s = s (when s ⊆ t), avoiding the ambiguous `Finset.card_sdiff`. -/
private lemma card_sdiff_of_subset {s t : Finset V} (h : s ⊆ t) :
    (t \ s).card = t.card - s.card := by
  have hd : Disjoint s (t \ s) := disjoint_sdiff_self_right
  have hu : s ∪ t \ s = t := Finset.union_sdiff_of_subset h
  have := Finset.card_union_of_disjoint hd
  rw [hu] at this
  omega

-- ─────────────────────────────────────────────────────────────────────────
-- §3.2  A DimBip produces a strictly smaller vertex cover
-- ─────────────────────────────────────────────────────────────────────────

/-- If D is a DimBip for S, then D.flipped is a vertex cover strictly
    smaller than S.  This is the easy (⇐) direction core.

    After rewriting, the cardinality goal reduces to:
        S.card - D.dU.card + D.dW.card < S.card
    which is equivalent to  D.dW.card < D.dU.card  (i.e. D.U_gt_W).
    Both D.U_gt_W and the bound D.dU.card ≤ S.card must be in scope for
    omega to close the goal; the previous version omitted D.U_gt_W. -/
lemma dimBip_gives_smaller (D : DimBip G S) :
    VCover G D.flipped ∧ D.flipped.card < S.card := by
  refine ⟨D.flip_vc, ?_⟩
  have hUsub  : D.dU ⊆ S := D.toAltBip.U_sub
  have hUleS  : D.dU.card ≤ S.card := Finset.card_le_card hUsub
  -- Key inequality from Definition 25: |W| < |U|.
  have hWltU  : D.dW.card < D.dU.card := D.U_gt_W
  -- (S \ U) and W are disjoint: W ∩ S = ∅  ⊇  W ∩ (S \ U).
  have hdisj  : Disjoint (S \ D.dU) D.dW := by
    rw [Finset.disjoint_left]
    intro x hx hxW
    exact absurd (Finset.mem_sdiff.mp hx).1
      (Finset.disjoint_left.mp D.toAltBip.W_disj hxW)
  -- Rewrite card(flipped) = (|S| - |U|) + |W|, then omega uses hWltU + hUleS.
  rw [DimBip.flipped, Finset.card_union_of_disjoint hdisj,
      card_sdiff_of_subset hUsub]
  -- Goal: S.card - D.dU.card + D.dW.card < S.card
  -- Follows from: D.dW.card < D.dU.card  and  D.dU.card ≤ S.card.
  omega

-- ─────────────────────────────────────────────────────────────────────────
-- §3.3  Symmetric-difference infrastructure for the (⇒) direction
-- ─────────────────────────────────────────────────────────────────────────

/-- U-part of the symmetric difference S △ S': the vertices in S but not S'. -/
def sdU (S S' : Finset V) : Finset V := S \ S'

/-- W-part of the symmetric difference S △ S': the vertices in S' but not S. -/
def sdW (S S' : Finset V) : Finset V := S' \ S

lemma sdU_sub (S S' : Finset V) : sdU S S' ⊆ S := Finset.sdiff_subset

lemma sdW_disj_S (S S' : Finset V) : Disjoint (sdW S S') S := by
  rw [Finset.disjoint_left]
  intro x hx hxS
  exact (Finset.mem_sdiff.mp hx).2 hxS

lemma sdU_sdW_disj (S S' : Finset V) : Disjoint (sdU S S') (sdW S S') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1

/-- No G-edge has both endpoints in S \ S' — else S' would fail to cover it. -/
lemma no_edge_in_sdU (hS' : VCover G S')
    {u v : V} (hu : u ∈ sdU S S') (hv : v ∈ sdU S S') (hadj : G.Adj u v) :
    False := by
  rcases hS' hadj with h | h
  · exact (Finset.mem_sdiff.mp hu).2 h
  · exact (Finset.mem_sdiff.mp hv).2 h

/-- No G-edge has both endpoints in S' \ S — else S would fail to cover it. -/
lemma no_edge_in_sdW (hS : VCover G S)
    {u v : V} (hu : u ∈ sdW S S') (hv : v ∈ sdW S S') (hadj : G.Adj u v) :
    False := by
  rcases hS hadj with h | h
  · exact (Finset.mem_sdiff.mp hu).2 h
  · exact (Finset.mem_sdiff.mp hv).2 h

/-- |S'| < |S|  implies  |S' \ S| < |S \ S'|.
    Strategy: derive both partition identities
        #S  = #(S ∩ S') + #(S \ S')
        #S' = #(S ∩ S') + #(S' \ S)
    by computing card of a disjoint union and rewriting its union-set
    equality into the `have`, so `this` becomes the numeric equation. -/
lemma card_sdiff_ineq {S S' : Finset V} (h : S'.card < S.card) :
    (sdW S S').card < (sdU S S').card := by
  simp only [sdU, sdW]
  have hpartS : (S ∩ S').card + (S \ S').card = S.card := by
    have hd : Disjoint (S ∩ S') (S \ S') :=
      Finset.disjoint_left.mpr fun x hx hx' =>
        (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
    have hu : S ∩ S' ∪ S \ S' = S := by
      ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
    have hc := Finset.card_union_of_disjoint hd
    rw [hu] at hc; linarith
  have hpartS' : (S ∩ S').card + (S' \ S).card = S'.card := by
    have hd : Disjoint (S ∩ S') (S' \ S) :=
      Finset.disjoint_left.mpr fun x hx hx' =>
        (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).1
    have hu : S ∩ S' ∪ S' \ S = S' := by
      ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
    have hc := Finset.card_union_of_disjoint hd
    rw [hu] at hc; linarith
  omega

/-- The swap reconstructs S': (S \ (S \ S')) ∪ (S' \ S) = S'. -/
lemma swap_eq (S S' : Finset V) : (S \ sdU S S') ∪ sdW S S' = S' := by
  simp only [sdU, sdW]
  ext x; simp only [mem_union, mem_sdiff]; tauto

/-- Hence the swap is a vertex cover (it equals S'). -/
lemma swap_is_vc (hS' : VCover G S') :
    VCover G ((S \ sdU S S') ∪ sdW S S') := by
  rw [swap_eq]; exact hS'

end VCLemmas

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Theorem 12
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 12** (Diminishing Bipartite Graph and Vertex Cover).

    Given a cubic bridgeless graph G and a vertex cover S with |S| ≤ |V| − 1,
    S is a minimum vertex cover if and only if no S-diminishing bipartite
    graph (DimBip) exists w.r.t. S.

    Proved by contrapositive in both directions.
    The (⇒) direction constructs a DimBip from the symmetric difference
    of S with any strictly smaller cover S'.

    Note: `hcubic` and `hbridgeless` are included for signature fidelity
    with the paper.  Theorem 12 itself does not use them in its proof;
    they are needed by Algorithm A (Petersen's theorem / perfect matching).
-/
theorem Theorem12
    (hS_vc : VCover G S)
    (hS_bound : S.card ≤ Fintype.card V - 1)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e) :
    MinVCover G S ↔ ¬ ∃ _ : DimBip G S, True := by
  constructor
  -- ─────────────────────────────────────────────────────────────────────
  -- (⇐)  If a DimBip D exists, S is not minimum.  Contrapositive:
  --       assume MinVCover G S and a DimBip D; derive False.
  -- ─────────────────────────────────────────────────────────────────────
  · intro hmin ⟨D, _⟩
    obtain ⟨hvc, hlt⟩ := VCLemmas.dimBip_gives_smaller D
    -- hlt  : D.flipped.card < S.card
    -- hmin.2 applied to D.flipped gives: S.card ≤ D.flipped.card
    have hge : S.card ≤ D.flipped.card := hmin.2 D.flipped hvc
    omega
  -- ─────────────────────────────────────────────────────────────────────
  -- (⇒)  If S is not minimum, a DimBip exists.  Contrapositive:
  --       assume ¬∃DimBip; prove MinVCover G S.
  -- ─────────────────────────────────────────────────────────────────────
  · intro hno_dim
    by_contra hnotmin
    simp only [MinVCover, not_and] at hnotmin
    have hnotmin' := hnotmin hS_vc
    push_neg at hnotmin'
    obtain ⟨S', hS'_vc, hS'_lt⟩ := hnotmin'
    -- Build U and W as plain Finset values (no `let`, to keep types transparent).
    -- U = S \ S',  W = S' \ S
    set U := S \ S' with hUdef
    set W := S' \ S with hWdef
    have hUW_disj : Disjoint U W := by
      simp only [hUdef, hWdef]
      exact VCLemmas.sdU_sdW_disj S S'
    have hU_sub : U ⊆ S := by
      simp only [hUdef]; exact VCLemmas.sdU_sub S S'
    have hW_disj : Disjoint W S := by
      simp only [hWdef]; exact VCLemmas.sdW_disj_S S S'
    have hcard : W.card < U.card := by
      simp only [hUdef, hWdef]
      exact VCLemmas.card_sdiff_ineq hS'_lt
    have hU_ne : U.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp; simp [hemp] at hcard
    have hnoU : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ U → v ∉ U := by
      intro u v hadj hu hv
      simp only [hUdef] at hu hv
      exact VCLemmas.no_edge_in_sdU hS'_vc hu hv hadj
    have hnoW : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ W → v ∉ W := by
      intro u v hadj hu hv
      simp only [hWdef] at hu hv
      exact VCLemmas.no_edge_in_sdW hS_vc hu hv hadj
    have hcross : ∀ ⦃u v : V⦄, G.Adj u v → u ∈ U → v ∈ U ∪ W → v ∈ W :=
      fun u v hadj huU hvUW => by
        rcases Finset.mem_union.mp hvUW with hvU | hvW
        · exact absurd hvU (hnoU hadj huU)
        · exact hvW
    -- The flip (S \ U) ∪ W = S' is a vertex cover.
    -- We spell the type out explicitly so it matches DimBip.flip_vc.
    have hswap : VCover G ((S \ U) ∪ W) := by
      have : (S \ U) ∪ W = S' := by
        simp only [hUdef, hWdef]
        exact VCLemmas.swap_eq S S'
      rw [this]; exact hS'_vc
    -- Assemble the DimBip record.
    exact hno_dim ⟨{
        toBipSub := { U, W, disj := hUW_disj, noU := hnoU,
                      noW := hnoW, cross := hcross }
        U_sub    := hU_sub
        W_disj   := hW_disj
        U_ne     := hU_ne
        U_gt_W   := hcard
        flip_vc  := hswap
      }, trivial⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Directional corollaries
-- ═══════════════════════════════════════════════════════════════════════════

theorem no_dimBip_implies_min
    (hS_vc : VCover G S)
    (hS_bound : S.card ≤ Fintype.card V - 1)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (hno         : ¬ ∃ _ : DimBip G S, True) :
    MinVCover G S :=
  (Theorem12 hS_vc hS_bound hcubic hbridgeless).mpr hno

theorem min_implies_no_dimBip
    (hS_vc : VCover G S)
    (hS_bound : S.card ≤ Fintype.card V - 1)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (hmin        : MinVCover G S) :
    ¬ ∃ _ : DimBip G S, True :=
  (Theorem12 hS_vc hS_bound hcubic hbridgeless).mp hmin

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: Zero sorry.

  Proof structure:
    Theorem12 (⇐): dimBip_gives_smaller → hlt + hmin.2 → omega
    Theorem12 (⇒): by_contra → hnotmin' (∃ smaller cover S') →
                   build DimBip with U = S\S', W = S'\S, then exact hno_dim
      • card_sdiff_of_subset  : partition identity + union_sdiff_of_subset
      • dimBip_gives_smaller  : card_sdiff_of_subset + card_union_disjoint + omega
      • no_edge_in_sdU/W      : VCover case split + mem_sdiff
      • card_sdiff_ineq        : two partition identities + omega
      • swap_is_vc             : swap_eq (tauto) + VCover of S'
-/
