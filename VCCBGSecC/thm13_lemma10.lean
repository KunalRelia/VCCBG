/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formal Lean 4 / Mathlib Verification of Lemma 10

  Source: §C.2.2 of the paper, lines 2726–2737 (the closing argument of
  Lemma 16 / the "completeness" step).

  This file:
    • Re-derives `compFlip_vcover` / `compFlip_card_lt` (component-
      restricted analogues of `Lemma15_flip_vc` / the cardinality
      argument in `algB_step_card_lt_of_reach_lt`), zero axioms.
    • Redefines Algorithm B's step/sweep/run at the component level
      (`algB_step''`, `algB_sweep''`, `algB_run''`), with the SAME
      vcover-preservation / cardinality-monotonicity / fixed-point
      structure as the global version in post123, zero axioms.
    • Closes `Lemma10`.
-/

public import VCCBGSecC.thm13_lemma16_proof

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

public theorem AltBip.SameComponent.refl {S : Finset V} (A : AltBip G S) (x : V) :
    A.SameComponent x x :=
  Relation.ReflTransGen.refl

public theorem AltBip.SameComponent.symm {S : Finset V} {A : AltBip G S} {x y : V}
    (h : A.SameComponent x y) : A.SameComponent y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
    refine Relation.ReflTransGen.head ?_ ih
    exact ⟨hyz.1.symm, hyz.2.2, hyz.2.1⟩

public theorem AltBip.SameComponent.trans {S : Finset V} {A : AltBip G S} {x y z : V}
    (h1 : A.SameComponent x y) (h2 : A.SameComponent y z) :
    A.SameComponent x z :=
  Relation.ReflTransGen.trans h1 h2

public def AltBip.compSetoid {S : Finset V} (A : AltBip G S) : Setoid V where
  r := A.SameComponent
  iseqv :=
    ⟨fun x => AltBip.SameComponent.refl A x,
     fun {x y} h => AltBip.SameComponent.symm h,
     fun {x y z} h1 h2 => AltBip.SameComponent.trans h1 h2⟩

public theorem AltBip.compU_eq_of_sameComponent {S : Finset V} {A : AltBip G S}
    {u u' : V} (h : A.SameComponent u u') : A.compU u = A.compU u' := by
  ext y
  simp only [AltBip.compU, Finset.mem_filter]
  constructor
  · rintro ⟨hyU, hycomp⟩
    exact ⟨hyU, AltBip.SameComponent.trans (AltBip.SameComponent.symm h) hycomp⟩
  · rintro ⟨hyU, hycomp⟩
    exact ⟨hyU, AltBip.SameComponent.trans h hycomp⟩

public theorem AltBip.compW_eq_of_sameComponent {S : Finset V} {A : AltBip G S}
    {u u' : V} (h : A.SameComponent u u') : A.compW u = A.compW u' := by
  ext y
  simp only [AltBip.compW, Finset.mem_filter]
  constructor
  · rintro ⟨hyW, hycomp⟩
    exact ⟨hyW, AltBip.SameComponent.trans (AltBip.SameComponent.symm h) hycomp⟩
  · rintro ⟨hyW, hycomp⟩
    exact ⟨hyW, AltBip.SameComponent.trans h hycomp⟩

open Classical in
/-- Pigeonhole: if `A` has a global blue surplus, some component does. -/
public theorem AltBip.exists_surplus_component
    {S : Finset V} (A : AltBip G S)
    (hgt : A.toBipSub.W.card < A.toBipSub.U.card) :
    ∃ u ∈ A.toBipSub.U, (A.compW u).card < (A.compU u).card := by
  by_contra hcon
  push Not at hcon
  let : Setoid V := A.compSetoid
  set π : V → Quotient A.compSetoid := fun x => ⟦x⟧ with hπdef
  set t : Finset (Quotient A.compSetoid) :=
    (A.toBipSub.U ∪ A.toBipSub.W).image π with htdef
  have hUmem : ∀ x ∈ A.toBipSub.U, π x ∈ t := fun x hx =>
    Finset.mem_image_of_mem π (Finset.mem_union_left _ hx)
  have hWmem : ∀ x ∈ A.toBipSub.W, π x ∈ t := fun x hx =>
    Finset.mem_image_of_mem π (Finset.mem_union_right _ hx)
  have hUsum : A.toBipSub.U.card =
      ∑ c ∈ t, (A.toBipSub.U.filter (fun x => π x = c)).card :=
    Finset.card_eq_sum_card_fiberwise hUmem
  have hWsum : A.toBipSub.W.card =
      ∑ c ∈ t, (A.toBipSub.W.filter (fun x => π x = c)).card :=
    Finset.card_eq_sum_card_fiberwise hWmem
  have hfiber_le : ∀ c ∈ t,
      (A.toBipSub.U.filter (fun x => π x = c)).card ≤
      (A.toBipSub.W.filter (fun x => π x = c)).card := by
    intro c hc
    simp only [htdef, Finset.mem_image, Finset.mem_union] at hc
    obtain ⟨x₀, hx₀mem, hx₀eq⟩ := hc
    have hUfiber : A.toBipSub.U.filter (fun x => π x = c) = A.compU x₀ := by
      ext x
      simp only [AltBip.compU, Finset.mem_filter, hπdef, ← hx₀eq]
      constructor
      · rintro ⟨hxU, hxeq⟩
        exact ⟨hxU, AltBip.SameComponent.symm (Quotient.exact hxeq)⟩
      · rintro ⟨hxU, hxcomp⟩
        exact ⟨hxU, Quotient.sound (AltBip.SameComponent.symm hxcomp)⟩
    have hWfiber : A.toBipSub.W.filter (fun x => π x = c) = A.compW x₀ := by
      ext x
      simp only [AltBip.compW, Finset.mem_filter, hπdef, ← hx₀eq]
      constructor
      · rintro ⟨hxW, hxeq⟩
        exact ⟨hxW, AltBip.SameComponent.symm (Quotient.exact hxeq)⟩
      · rintro ⟨hxW, hxcomp⟩
        exact ⟨hxW, Quotient.sound (AltBip.SameComponent.symm hxcomp)⟩
    rw [hUfiber, hWfiber]
    rcases hx₀mem with hx₀U | hx₀W
    · exact hcon x₀ hx₀U
    · by_cases hne : (A.compU x₀).Nonempty
      · obtain ⟨u', hu'⟩ := hne
        simp only [AltBip.compU, Finset.mem_filter] at hu'
        obtain ⟨hu'U, hu'comp⟩ := hu'
        rw [AltBip.compU_eq_of_sameComponent hu'comp,
            AltBip.compW_eq_of_sameComponent hu'comp]
        exact hcon u' hu'U
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        exact Finset.card_empty ▸ Nat.zero_le _
  have hsum_le :
      (∑ c ∈ t, (A.toBipSub.U.filter (fun x => π x = c)).card) ≤
      ∑ c ∈ t, (A.toBipSub.W.filter (fun x => π x = c)).card :=
    Finset.sum_le_sum hfiber_le
  rw [← hUsum, ← hWsum] at hsum_le
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. compFlip_vcover — the component-restricted flip is a vertex cover.
-- ═══════════════════════════════════════════════════════════════════════════
open Classical in
public theorem compFlip_vcover
    {S : Finset V} {v0 : V} (hv0 : v0 ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S)
    (A : AltBip G S)
    (hA : A.toBipSub.U = reachU G S C v0 ∧ A.toBipSub.W = reachW G S C v0)
    (u : V) :
    VCover G ((S \ A.compU u) ∪ A.compW u) := by
  have hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x := hOrder.irrefl
  have hNBB : NoBlueBlue G C := ValidColoring_NoBlueBlue G S nbrOrder hOrder hVC
  intro a b hadj
  rcases hSVC hadj with haS | hbS
  · by_cases haU : a ∈ A.compU u
    · have haU' : a ∈ A.toBipSub.U := (Finset.mem_filter.mp haU).1
      have hacomp : A.SameComponent u a := (Finset.mem_filter.mp haU).2
      have haUreach : a ∈ reachU G S C v0 := hA.1 ▸ haU'
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at haUreach
      have hCa' : runAlgC G S nbrOrder fuel v0 a = blue := by
        unfold ValidColoring at hVC; exact hVC ▸ haUreach
      have hbOrder : b ∈ nbrOrder a := (hOrder a b).mpr hadj
      by_cases hbS' : b ∈ S
      · have key := runAlgC_blue_neighbors_resolved_general G S nbrOrder hirrefl hlen hv0 hfuel
          hCa' b hbOrder hbS'
        rcases key with hblack | hblue
        · have hCb_black' : C b = black := by unfold ValidColoring at hVC; exact hVC ▸ hblack
          have hbU : b ∉ A.compU u := by
            intro hmem
            have hbU' : b ∈ A.toBipSub.U := (Finset.mem_filter.mp hmem).1
            have hbUreach : b ∈ reachU G S C v0 := hA.1 ▸ hbU'
            simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hbUreach
            rw [hCb_black'] at hbUreach
            exact absurd hbUreach (by decide)
          exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hbS', hbU⟩))
        · exfalso
          have hCb_blue' : C b = blue := by unfold ValidColoring at hVC; exact hVC ▸ hblue
          exact hNBB a b hadj haUreach hCb_blue'
      · have hred := runAlgC_blue_notS_neighbor_red G S nbrOrder hirrefl hlen hv0 hfuel
          hCa' b hbOrder hbS'
        have hCb_red' : C b = red := by unfold ValidColoring at hVC; exact hVC ▸ hred
        have hbW' : b ∈ A.toBipSub.W := by
          rw [hA.2]
          simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hCb_red'
        have hbUW : b ∈ A.toBipSub.U ∪ A.toBipSub.W := Finset.mem_union_right _ hbW'
        have haUW : a ∈ A.toBipSub.U ∪ A.toBipSub.W := Finset.mem_union_left _ haU'
        have hstep : A.inducedAdj a b := ⟨hadj, haUW, hbUW⟩
        have hbcomp : A.SameComponent u b := Relation.ReflTransGen.tail hacomp hstep
        exact Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbW', hbcomp⟩))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haS, haU⟩))
  · by_cases hbU : b ∈ A.compU u
    · have hbU' : b ∈ A.toBipSub.U := (Finset.mem_filter.mp hbU).1
      have hbcomp : A.SameComponent u b := (Finset.mem_filter.mp hbU).2
      have hbUreach : b ∈ reachU G S C v0 := hA.1 ▸ hbU'
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hbUreach
      have hCb' : runAlgC G S nbrOrder fuel v0 b = blue := by
        unfold ValidColoring at hVC; exact hVC ▸ hbUreach
      have hadj' : G.Adj b a := hadj.symm
      have haOrder : a ∈ nbrOrder b := (hOrder b a).mpr hadj'
      by_cases haS' : a ∈ S
      · have key := runAlgC_blue_neighbors_resolved_general G S nbrOrder hirrefl hlen hv0 hfuel
          hCb' a haOrder haS'
        rcases key with hblack | hblue
        · have hCa_black' : C a = black := by unfold ValidColoring at hVC; exact hVC ▸ hblack
          have haU : a ∉ A.compU u := by
            intro hmem
            have haU' : a ∈ A.toBipSub.U := (Finset.mem_filter.mp hmem).1
            have haUreach : a ∈ reachU G S C v0 := hA.1 ▸ haU'
            simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at haUreach
            rw [hCa_black'] at haUreach
            exact absurd haUreach (by decide)
          exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haS', haU⟩))
        · exfalso
          have hCa_blue' : C a = blue := by unfold ValidColoring at hVC; exact hVC ▸ hblue
          exact hNBB b a hadj' hbUreach hCa_blue'
      · have hred := runAlgC_blue_notS_neighbor_red G S nbrOrder hirrefl hlen hv0 hfuel
          hCb' a haOrder haS'
        have hCa_red' : C a = red := by unfold ValidColoring at hVC; exact hVC ▸ hred
        have haW' : a ∈ A.toBipSub.W := by
          rw [hA.2]
          simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hCa_red'
        have haUW : a ∈ A.toBipSub.U ∪ A.toBipSub.W := Finset.mem_union_right _ haW'
        have hbUW : b ∈ A.toBipSub.U ∪ A.toBipSub.W := Finset.mem_union_left _ hbU'
        have hstep : A.inducedAdj b a := ⟨hadj', hbUW, haUW⟩
        have hacomp : A.SameComponent u a := Relation.ReflTransGen.tail hbcomp hstep
        exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haW', hacomp⟩))
    · exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hbS, hbU⟩))

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. compFlip_card_lt — cardinality strictly decreases.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem compFlip_card_lt
    {S : Finset V} (A : AltBip G S) (u : V)
    (hUsub : A.compU u ⊆ S) (hWdisj : Disjoint (A.compW u) S)
    (hlt : (A.compW u).card < (A.compU u).card) :
    ((S \ A.compU u) ∪ A.compW u).card < S.card := by
  have h_disj : Disjoint (S \ A.compU u) (A.compW u) :=
    Disjoint.symm (hWdisj.mono_right Finset.sdiff_subset)
  rw [Finset.card_union_of_disjoint h_disj, Finset.card_sdiff_of_subset hUsub]
  have hUle : (A.compU u).card ≤ S.card := Finset.card_le_card hUsub
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. algB_step'' — component-restricted Algorithm B step. Fully
--     Prop-guarded so it needs no term-level hypotheses in its own
--     signature, matching the original `algB_step`'s shape.
-- ═══════════════════════════════════════════════════════════════════════════

open Classical in
public noncomputable def algB_step''
    (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)
    (hOrder : OrderMatchesAdj G nbrOrder) (v : V) : Finset V :=
  if hv : v ∈ S then
    if hSVC : VCover G S then
      let C := runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v
      let A := Lemma14_witness G S nbrOrder hv hOrder
        (show ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C from rfl) hSVC
      if h : ∃ u ∈ A.toBipSub.U, (A.compW u).card < (A.compU u).card then
        (S \ A.compU h.choose) ∪ A.compW h.choose
      else S
    else S
  else S

public theorem algB_step''_vcover
    {S : Finset V} (hSVC : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (v : V) (hv : v ∈ S) :
    VCover G (algB_step'' G S nbrOrder hOrder v) := by
  unfold algB_step''
  rw [dite_eq_left hv, dite_eq_left hSVC]
  set C := runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v with hCdef
  set A := Lemma14_witness G S nbrOrder hv hOrder
    (show ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C from hCdef) hSVC with hAdef
  by_cases h : ∃ u ∈ A.toBipSub.U, (A.compW u).card < (A.compU u).card
  · rw [dite_eq_left h]
    have hVC : ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C := hCdef
    have hAeq : A.toBipSub.U = reachU G S C v ∧ A.toBipSub.W = reachW G S C v := by
      rw [hAdef]; exact ⟨rfl, rfl⟩
    exact compFlip_vcover hv hOrder hlen (seedFuel_sufficient G S nbrOrder v) hVC hSVC A hAeq
      h.choose
  · rw [dite_eq_right h]; exact hSVC

open Classical in
public theorem algB_step''_eq_or_card_lt
    {S : Finset V} (hSVC : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (v : V) (hv : v ∈ S) :
    algB_step'' G S nbrOrder hOrder v = S ∨
    (algB_step'' G S nbrOrder hOrder v).card < S.card := by
  unfold algB_step''
  rw [dite_eq_left hv, dite_eq_left hSVC]
  set C := runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v with hCdef
  set A := Lemma14_witness G S nbrOrder hv hOrder
    (show ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C from hCdef) hSVC with hAdef
  by_cases h : ∃ u ∈ A.toBipSub.U, (A.compW u).card < (A.compU u).card
  · right
    rw [dite_eq_left h]
    obtain ⟨hu_mem, hu_lt⟩ := h.choose_spec
    have hUsub : A.compU h.choose ⊆ S := by
      intro x hx
      have hxU : x ∈ A.toBipSub.U := (Finset.mem_filter.mp hx).1
      exact A.U_sub hxU
    have hWdisj : Disjoint (A.compW h.choose) S := by
      rw [Finset.disjoint_left]
      intro x hx hxS
      have hxW : x ∈ A.toBipSub.W := (Finset.mem_filter.mp hx).1
      exact (Finset.disjoint_left.mp A.W_disj) hxW hxS
    exact compFlip_card_lt A h.choose hUsub hWdisj hu_lt
  · left; rw [dite_eq_right h]

public theorem algB_step''_card_le
    {S : Finset V} (hSVC : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (v : V) (hv : v ∈ S) :
    (algB_step'' G S nbrOrder hOrder v).card ≤ S.card := by
  rcases algB_step''_eq_or_card_lt hSVC hOrder hlen v hv with heq | hlt
  · rw [heq]
  · exact Nat.le_of_lt hlt

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. algB_sweep'' / algB_run'' — mechanical ports of the global
--     versions in post123, unfolding one extra `dite_eq_left hv` per seed.
-- ═══════════════════════════════════════════════════════════════════════════

public noncomputable def algB_sweep''
    (G : SimpleGraph V) (nbrOrder : V → List V) (hOrder : OrderMatchesAdj G nbrOrder)
    (seeds : List V) (S : Finset V) : Finset V :=
  seeds.foldl (fun S' v => algB_step'' G S' nbrOrder hOrder v) S

public theorem algB_sweep''_vcover
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V) :
    VCover G (algB_sweep'' G nbrOrder hOrder seeds S) := by
  unfold algB_sweep''
  induction seeds generalizing S with
  | nil => exact hS
  | cons v vs ih =>
    simp only [List.foldl_cons]
    by_cases hv : v ∈ S
    · have hstep : VCover G (algB_step'' G S nbrOrder hOrder v) :=
        algB_step''_vcover hS hOrder hlen v hv
      exact ih hstep
    · have heq : algB_step'' G S nbrOrder hOrder v = S := by
        unfold algB_step''; rw [dite_eq_right hv]
      rw [heq]; exact ih hS

public theorem algB_sweep''_eq_or_card_lt
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V) :
    algB_sweep'' G nbrOrder hOrder seeds S = S ∨
    (algB_sweep'' G nbrOrder hOrder seeds S).card < S.card := by
  unfold algB_sweep''
  induction seeds generalizing S with
  | nil => left; rfl
  | cons v vs ih =>
    simp only [List.foldl_cons]
    by_cases hv : v ∈ S
    · rcases algB_step''_eq_or_card_lt hS hOrder hlen v hv with hstep_eq | hstep_lt
      · rw [hstep_eq]; exact ih hS
      · have hstep_vc : VCover G (algB_step'' G S nbrOrder hOrder v) :=
          algB_step''_vcover hS hOrder hlen v hv
        rcases ih hstep_vc with htail_eq | htail_lt
        · rw [htail_eq]; right; exact hstep_lt
        · right; exact lt_trans htail_lt hstep_lt
    · have heq : algB_step'' G S nbrOrder hOrder v = S := by
        unfold algB_step''; rw [dite_eq_right hv]
      rw [heq]; exact ih hS

public theorem algB_sweep''_card_le
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V) :
    (algB_sweep'' G nbrOrder hOrder seeds S).card ≤ S.card := by
  rcases algB_sweep''_eq_or_card_lt hS hOrder hlen seeds with heq | hlt
  · rw [heq]
  · exact Nat.le_of_lt hlt

public noncomputable def algB_run''
    (G : SimpleGraph V) (nbrOrder : V → List V) (hOrder : OrderMatchesAdj G nbrOrder)
    (seeds : List V) (k : ℕ) (S : Finset V) : Finset V :=
  match k with
  | 0 => S
  | k' + 1 => algB_sweep'' G nbrOrder hOrder seeds (algB_run'' G nbrOrder hOrder seeds k' S)

public theorem algB_run''_vcover
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V) (k : ℕ) :
    VCover G (algB_run'' G nbrOrder hOrder seeds k S) := by
  induction k with
  | zero => exact hS
  | succ k' ih => exact algB_sweep''_vcover ih hOrder hlen seeds

public theorem algB_run''_of_sweep_eq
    {S : Finset V} {nbrOrder : V → List V} {hOrder : OrderMatchesAdj G nbrOrder}
    {seeds : List V}
    (heq : algB_sweep'' G nbrOrder hOrder seeds S = S) (k : ℕ) :
    algB_run'' G nbrOrder hOrder seeds k S = S := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    change algB_sweep'' G nbrOrder hOrder seeds (algB_run'' G nbrOrder hOrder seeds k' S) = S
    rw [ih, heq]

public theorem algB_run''_succ
    {S : Finset V} {nbrOrder : V → List V} {hOrder : OrderMatchesAdj G nbrOrder}
    {seeds : List V} (k : ℕ) :
    algB_run'' G nbrOrder hOrder seeds (k + 1) S =
    algB_run'' G nbrOrder hOrder seeds k (algB_sweep'' G nbrOrder hOrder seeds S) := by
  induction k generalizing S with
  | zero => rfl
  | succ k' ih =>
    change algB_sweep'' G nbrOrder hOrder seeds
      (algB_run'' G nbrOrder hOrder seeds (k' + 1) S) = _
    rw [ih]; rfl

public theorem algB_run''_reaches_fixed_point
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V)
    (n : ℕ) (hn : S.card ≤ n) :
    algB_sweep'' G nbrOrder hOrder seeds (algB_run'' G nbrOrder hOrder seeds n S) =
    algB_run'' G nbrOrder hOrder seeds n S := by
  induction n generalizing S with
  | zero =>
    have hS0 : S.card = 0 := by omega
    rcases algB_sweep''_eq_or_card_lt hS hOrder hlen seeds with heq | hlt
    · exact heq
    · omega
  | succ n' ih =>
    rcases algB_sweep''_eq_or_card_lt hS hOrder hlen seeds with heq | hlt
    · rw [algB_run''_of_sweep_eq heq (n' + 1)]; exact heq
    · have hnext_vc : VCover G (algB_sweep'' G nbrOrder hOrder seeds S) :=
        algB_sweep''_vcover hS hOrder hlen seeds
      have hnext_bound : (algB_sweep'' G nbrOrder hOrder seeds S).card ≤ n' := by omega
      rw [algB_run''_succ n']
      exact ih hnext_vc hnext_bound

public theorem algB_sweep''_eq_imp_step_eq
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    (seeds : List V) (hfixed : algB_sweep'' G nbrOrder hOrder seeds S = S)
    (v : V) (hv : v ∈ seeds) (hvS : v ∈ S) :
    algB_step'' G S nbrOrder hOrder v = S := by
  induction seeds generalizing S with
  | nil => contradiction
  | cons x xs ih =>
    unfold algB_sweep'' at hfixed
    simp only [List.foldl_cons] at hfixed
    set S' := algB_step'' G S nbrOrder hOrder x with hS'def
    have hS'_vc : VCover G S' := by
      by_cases hxS : x ∈ S
      · rw [hS'def]; exact algB_step''_vcover hS hOrder hlen x hxS
      · have heq : algB_step'' G S nbrOrder hOrder x = S := by
          unfold algB_step''; rw [dite_eq_right hxS]
        rw [hS'def, heq]; exact hS
    have hS'_le : S'.card ≤ S.card := by
      by_cases hxS : x ∈ S
      · rw [hS'def]; exact algB_step''_card_le hS hOrder hlen x hxS
      · have heq : algB_step'' G S nbrOrder hOrder x = S := by
          unfold algB_step''; rw [dite_eq_right hxS]
        rw [hS'def, heq]
    have htail_le : (algB_sweep'' G nbrOrder hOrder xs S').card ≤ S'.card :=
      algB_sweep''_card_le hS'_vc hOrder hlen xs
    have hS'_eq : S' = S := by
      have hcard_eq : S'.card = S.card := by
        have h1 : S.card ≤ S'.card := hfixed ▸ htail_le
        omega
      by_cases hxS : x ∈ S
      · rcases algB_step''_eq_or_card_lt hS hOrder hlen x hxS with heq | hlt
        · rw [hS'def]; exact heq
        · exfalso; rw [hS'def] at hcard_eq; omega
      · rw [hS'def]; unfold algB_step''; rw [dite_eq_right hxS]
    have hfixed_xs : algB_sweep'' G nbrOrder hOrder xs S = S := by
      rw [hS'_eq] at hfixed; exact hfixed
    rcases List.mem_cons.mp hv with rfl | hv_xs
    · have h1 : algB_step'' G S nbrOrder hOrder v = S' := by rw [hS'def]
      rw [h1, hS'_eq]
    · exact ih hS hfixed_xs hv_xs hvS

open Classical in
/-- **Search completeness at a fixed point, component-restricted:
    at a sweep fixed point, every remaining seed's OWN run has
    no component with a blue surplus, for any `u` in it. -/
public theorem algB_fixed_point_no_diminishing_component
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    (seeds : List V) (hfixed : algB_sweep'' G nbrOrder hOrder seeds S = S) :
    ∀ v ∈ seeds, v ∈ S →
      ∀ (C : Coloring V) (hVC : ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C)
        (A : AltBip G S)
        (_ : A.toBipSub.U = reachU G S C v ∧ A.toBipSub.W = reachW G S C v)
        (u : V), u ∈ A.toBipSub.U → (A.compU u).card ≤ (A.compW u).card := by
  intro v hv_seeds hv_S C hVC A hA u huU
  by_contra hlt
  push Not at hlt
  have hstep_eq : algB_step'' G S nbrOrder hOrder v = S :=
    algB_sweep''_eq_imp_step_eq hS hOrder hlen seeds hfixed v hv_seeds hv_S
  have hexists : ∃ u ∈ A.toBipSub.U, (A.compW u).card < (A.compU u).card :=
    ⟨u, huU, hlt⟩
  unfold algB_step'' at hstep_eq
  rw [dite_eq_left hv_S, dite_eq_left hS] at hstep_eq
  set C' := runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v with hC'def
  set A' := Lemma14_witness G S nbrOrder hv_S hOrder
    (show ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C' from hC'def) hS with hA'def
  have hCC' : C = C' := Lemma12_Part1 hVC (show ValidColoring G S nbrOrder v
    (seedFuel G S nbrOrder v) C' from hC'def)
  have hAU' : A'.U = A.U := by rw [hA'def, hA.1]; change reachU G S C' v = reachU G S C v; rw [← hCC']
  have hAW' : A'.W = A.W := by rw [hA'def, hA.2]; change reachW G S C' v = reachW G S C v; rw [← hCC']
  have hexists' : ∃ u ∈ A'.toBipSub.U, (A'.compW u).card < (A'.compU u).card := by
    obtain ⟨u', hu'mem, hu'lt⟩ := hexists
    refine ⟨u', hAU' ▸ hu'mem, ?_⟩
    have hcompU_eq : A'.compU u' = A.compU u' := by
      unfold AltBip.compU; congr 1
      unfold AltBip.SameComponent AltBip.inducedAdj
      rw [hAU', hAW']
      -- --unfold AltBip.compU; rw [hAU']
      -- --congr 1
      -- have hSame : A'.SameComponent = A.SameComponent := AltBip.SameComponent_eq hAU' hAW'
      -- rw [hSame]
    have hcompW_eq : A'.compW u' = A.compW u' := by
      unfold AltBip.compW; congr 1
      unfold AltBip.SameComponent AltBip.inducedAdj
      rw [hAU', hAW']
      -- --unfold AltBip.compW; rw [hAW']
      -- --congr 1
      -- have hSame : A'.SameComponent = A.SameComponent := AltBip.SameComponent_eq hAU' hAW'
      -- rw [hSame]
    rw [hcompU_eq, hcompW_eq]; exact hu'lt
  rw [dite_eq_left hexists'] at hstep_eq
  have hstep_lt : ((S \ A'.compU hexists'.choose) ∪ A'.compW hexists'.choose).card < S.card := by
    obtain ⟨hu_mem, hu_lt⟩ := hexists'.choose_spec
    have hUsub : A'.compU hexists'.choose ⊆ S := by
      intro x hx
      have hxU : x ∈ A'.toBipSub.U := (Finset.mem_filter.mp hx).1
      exact A'.U_sub hxU
    have hWdisj : Disjoint (A'.compW hexists'.choose) S := by
      rw [Finset.disjoint_left]
      intro x hx hxS
      have hxW : x ∈ A'.toBipSub.W := (Finset.mem_filter.mp hx).1
      exact (Finset.disjoint_left.mp A'.W_disj) hxW hxS
    exact compFlip_card_lt A' hexists'.choose hUsub hWdisj hu_lt
  rw [hstep_eq] at hstep_lt
  exact lt_irrefl S.card hstep_lt

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Lemma 10, closed.
-- ═══════════════════════════════════════════════════════════════════════════

public def FixedPointCover''
    (G : SimpleGraph V) (S₀ : Finset V) (nbrOrder : V → List V)
    (hOrder : OrderMatchesAdj G nbrOrder) (M : Finset (Sym2 V)) (n : ℕ) : Prop :=
  S₀.card ≤ n ∧
  algB_sweep'' G nbrOrder hOrder (seedsOf M) (algB_run'' G nbrOrder hOrder (seedsOf M) n S₀)
    = algB_run'' G nbrOrder hOrder (seedsOf M) n S₀

public theorem Lemma10_no_dimBip_at_fixed_point''
    {S₀ S : Finset V} (hS₀ : VCover G S₀)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {M : Finset (Sym2 V)} (hM : IsPerfectMatching M)
    {n : ℕ} (hfp : FixedPointCover'' G S₀ nbrOrder hOrder M n)
    (hSeq : S = algB_run'' G nbrOrder hOrder (seedsOf M) n S₀) :
    ¬ ∃ _ : DimBip G S, True := by
  intro hexists
  obtain ⟨hn, hfixed⟩ := hfp
  have hS_vc : VCover G S := hSeq ▸ algB_run''_vcover hS₀ hOrder hlen (seedsOf M) n
  have hfixed' : algB_sweep'' G nbrOrder hOrder (seedsOf M) S = S := hSeq ▸ hfixed
  obtain ⟨v, hvS, C, hVC, A, hA, u, huU, hu_lt⟩ :=
    AlgC_component_search_complete hS_vc hexists hOrder hlen
  have hv_seed : v ∈ seedsOf M := mem_seedsOf_of_perfect hM v
  have hno_dim := algB_fixed_point_no_diminishing_component hS_vc hOrder hlen (seedsOf M)
    hfixed' v hv_seed hvS C hVC A hA u huU
  omega

public theorem Lemma10''
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    {S₀ S : Finset V} (hS₀ : VCover G S₀)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {M : Finset (Sym2 V)} (hM : IsPerfectMatching M)
    {n : ℕ} (hfp : FixedPointCover'' G S₀ nbrOrder hOrder M n)
    (hSeq : S = algB_run'' G nbrOrder hOrder (seedsOf M) n S₀)
    (hSbound : S.card ≤ Fintype.card V - 1) :
    MinVCover G S := by
  have hS_vc : VCover G S := hSeq ▸ algB_run''_vcover hS₀ hOrder hlen (seedsOf M) n
  have hno_dim : ¬ ∃ _ : DimBip G S, True :=
    Lemma10_no_dimBip_at_fixed_point'' hS₀ hOrder hlen hM hfp hSeq
  exact (Theorem12 hS_vc hSbound hcubic hbridgeless).mpr hno_dim

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Extension: soundness for VC-CBG.
-- ═══════════════════════════════════════════════════════════════════════════

@[expose] public def IsYesInstance (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, VCover G S ∧ S.card ≤ k

public theorem Lemma10_soundness_yes_instance
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    {S₀ S : Finset V} (hS₀ : VCover G S₀)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {M : Finset (Sym2 V)} (hM : IsPerfectMatching M)
    {n : ℕ} (hfp : FixedPointCover'' G S₀ nbrOrder hOrder M n)
    (hSeq : S = algB_run'' G nbrOrder hOrder (seedsOf M) n S₀)
    (hSbound : S.card ≤ Fintype.card V - 1)
    {k : ℕ} (hAlgAYes : S.card ≤ k) :
    IsYesInstance G k := by
  have hMin : MinVCover G S :=
    Lemma10'' hcubic hbridgeless hS₀ hOrder hlen hM hfp hSeq hSbound
  exact ⟨S, hMin.1, hAlgAYes⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking. (seed_robustness is inherited)

-/
