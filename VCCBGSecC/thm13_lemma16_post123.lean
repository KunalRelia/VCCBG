/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 16, "post-1,2,3" phase

  "Guaranteeing a complete search" and the closing argument of Lemma 16.

  Source: paper §C.2.2, lines 2684–2710.
-/

public import VCCBGSecC.thm13_lemma16_123

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

open Color

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Coverage of perfect matching (paper lines 2691–2693)
-- ═══════════════════════════════════════════════════════════════════════════

public theorem Lemma16_seed_coverage
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e) :
    ∃ M : Finset (Sym2 V), IsPerfectMatching M ∧ ∀ v : V, ∃ e ∈ M, v ∈ e := by
  obtain ⟨M, hM, _⟩ := PetersenMatching hcubic hbridgeless
  exact ⟨M, hM, hM.2⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. `algB_step` — single seed cover update
-- ═══════════════════════════════════════════════════════════════════════════

/-- One step of Algorithm B's inner loop: seed Algorithm C at `v` and flip `S`
    if a diminishing subcover is found; otherwise leave `S` unchanged. -/
public noncomputable def algB_step
    (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V) (v : V) :
    Finset V :=
  let C := runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v
  if (reachW G S C v).card < (reachU G S C v).card then
    (S \ reachU G S C v) ∪ reachW G S C v
  else
    S

/-- Cardinality reduction lemma for `algB_step` when a diminishing subcover exists. -/
public theorem algB_step_card_lt_of_reach_lt
    {S : Finset V} {nbrOrder : V → List V}
    (v : V) (hv : v ∈ S)
    (hlt : (reachW G S (runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v) v).card <
           (reachU G S (runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v) v).card) :
    (algB_step G S nbrOrder v).card < S.card := by
  unfold algB_step
  rw [ite_eq_left hlt]
  set C := runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v with hCdef
  set U := reachU G S C v
  set W := reachW G S C v
  have hlt' : W.card < U.card := by
    simpa [C, U, W] using hlt
  have hVC :
      ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C := by
    exact hCdef
  have hmem :
      ∀ {w : V}, (C w = blue → w ∈ S) ∧ (C w = red → w ∉ S) :=
    Lemma14_membership G S nbrOrder hv hVC
  have hU_sub : U ⊆ S := by
    intro x hx
    simp only [U, reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hmem.1 hx
  have hW_disj : Disjoint W S := by
    rw [Finset.disjoint_left]
    intro x hxW hxS
    simp only [W, reachW, Finset.mem_filter, Finset.mem_univ, true_and] at hxW
    exact (hmem.2 hxW) hxS
  have h_disj : Disjoint (S \ U) W :=
    Disjoint.symm (hW_disj.mono_right (Finset.sdiff_subset))
  rw [Finset.card_union_of_disjoint h_disj]
  rw [Finset.card_sdiff]
  have hUS : U ∩ S = U := by
    exact Finset.inter_eq_left.mpr hU_sub
  rw [hUS]
  have hU_card_le : U.card ≤ S.card :=
    Finset.card_le_card hU_sub
  omega

/-- `algB_step` preserves the vertex-cover property. -/
public theorem algB_step_vcover
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (v : V) (hv : v ∈ S) :
    VCover G (algB_step G S nbrOrder v) := by
  unfold algB_step
  set C := runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v with hCdef
  by_cases hlt : (reachW G S C v).card < (reachU G S C v).card
  · rw [ite_eq_left hlt]
    have hVC : ValidColoring G S nbrOrder v (seedFuel G S nbrOrder v) C := hCdef
    exact
      Lemma15_flip_vc hv hOrder hlen (seedFuel_sufficient G S nbrOrder v) hVC hS
  · rw [ite_eq_right hlt]
    exact hS

/-- `algB_step` either leaves `S` unchanged or strictly decreases cardinality. -/
public theorem algB_step_eq_or_card_lt
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (v : V) (hv : v ∈ S) :
    algB_step G S nbrOrder v = S ∨ (algB_step G S nbrOrder v).card < S.card := by
  by_cases hlt : (reachW G S (runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v) v).card <
                 (reachU G S (runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v) v).card
  · right
    exact algB_step_card_lt_of_reach_lt v hv hlt
  · left
    unfold algB_step
    rw [ite_eq_right hlt]

/-- `algB_step` never increases cover cardinality. -/
public theorem algB_step_card_le
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (v : V) (hv : v ∈ S) :
    (algB_step G S nbrOrder v).card ≤ S.card := by
  rcases algB_step_eq_or_card_lt hS hOrder hlen v hv with heq | hlt
  · rw [heq]
  · exact Nat.le_of_lt hlt

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. `algB_sweep` and `algB_run` — fixed-point termination proofs
-- ═══════════════════════════════════════════════════════════════════════════

/-- A complete sweep over a seed sequence. -/
public noncomputable def algB_sweep
    (G : SimpleGraph V) (nbrOrder : V → List V) (seeds : List V) (S : Finset V) : Finset V :=
  seeds.foldl (fun S' v => if v ∈ S' then algB_step G S' nbrOrder v else S') S

/-- `algB_sweep` maintains the vertex-cover invariant. -/
public theorem algB_sweep_vcover
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V) :
    VCover G (algB_sweep G nbrOrder seeds S) := by
  unfold algB_sweep
  induction seeds generalizing S with
  | nil => exact hS
  | cons v vs ih =>
    simp only [List.foldl_cons]
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv]
      have hstep := algB_step_vcover hS hOrder hlen v hv
      exact ih hstep
    · rw [ite_eq_right hv]
      exact ih hS

/-- `algB_sweep` either leaves `S` intact or strictly reduces its cardinality. -/
public theorem algB_sweep_eq_or_card_lt
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V) :
    algB_sweep G nbrOrder seeds S = S ∨ (algB_sweep G nbrOrder seeds S).card < S.card := by
  unfold algB_sweep
  induction seeds generalizing S with
  | nil => left; rfl
  | cons v vs ih =>
    simp only [List.foldl_cons]
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv]
      rcases algB_step_eq_or_card_lt hS hOrder hlen v hv with hstep_eq | hstep_lt
      · rw [hstep_eq]
        exact ih hS
      · have hstep_vc := algB_step_vcover hS hOrder hlen v hv
        rcases ih hstep_vc with htail_eq | htail_lt
        · rw [htail_eq]; right; exact hstep_lt
        · right; exact lt_trans htail_lt hstep_lt
    · rw [ite_eq_right hv]
      exact ih hS

public theorem algB_sweep_card_le
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V) :
    (algB_sweep G nbrOrder seeds S).card ≤ S.card := by
  rcases algB_sweep_eq_or_card_lt hS hOrder hlen seeds with heq | hlt
  · rw [heq]
  · exact Nat.le_of_lt hlt

/-- Iterating `algB_sweep` for `k` passes. -/
public noncomputable def algB_run
    (G : SimpleGraph V) (nbrOrder : V → List V) (seeds : List V) (k : ℕ) (S : Finset V) : Finset V :=
  match k with
  | 0 => S
  | k' + 1 => algB_sweep G nbrOrder seeds (algB_run G nbrOrder seeds k' S)

public theorem algB_run_vcover
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V) (k : ℕ) :
    VCover G (algB_run G nbrOrder seeds k S) := by
  induction k with
  | zero => exact hS
  | succ k' ih =>
    exact algB_sweep_vcover ih hOrder hlen seeds

public theorem algB_run_of_sweep_eq
    {S : Finset V} {nbrOrder : V → List V} {seeds : List V}
    (heq : algB_sweep G nbrOrder seeds S = S) (k : ℕ) :
    algB_run G nbrOrder seeds k S = S := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    change algB_sweep G nbrOrder seeds (algB_run G nbrOrder seeds k' S) = S
    rw [ih, heq]

public theorem algB_run_succ
    {S : Finset V} {nbrOrder : V → List V} {seeds : List V} (k : ℕ) :
    algB_run G nbrOrder seeds (k + 1) S =
    algB_run G nbrOrder seeds k (algB_sweep G nbrOrder seeds S) := by
  induction k generalizing S with
  | zero => rfl
  | succ k' ih =>
    change algB_sweep G nbrOrder seeds (algB_run G nbrOrder seeds (k' + 1) S) = _
    rw [ih]
    rfl

/-- **Termination Theorem**:
    Within `n ≥ |S|` sweeps, Algorithm B reaches a stationary fixed point. -/
public theorem algB_run_reaches_fixed_point
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) (seeds : List V)
    (n : ℕ) (hn : S.card ≤ n) :
    algB_sweep G nbrOrder seeds (algB_run G nbrOrder seeds n S) =
    algB_run G nbrOrder seeds n S := by
  induction n generalizing S with
  | zero =>
    have hS0 : S.card = 0 := by omega
    rcases algB_sweep_eq_or_card_lt hS hOrder hlen seeds with heq | hlt
    · exact heq
    · omega
  | succ n' ih =>
    rcases algB_sweep_eq_or_card_lt hS hOrder hlen seeds with heq | hlt
    · rw [algB_run_of_sweep_eq heq (n' + 1)]
      exact heq
    · have hnext_vc := algB_sweep_vcover hS hOrder hlen seeds
      have hnext_bound : (algB_sweep G nbrOrder seeds S).card ≤ n' := by omega
      rw [algB_run_succ n']
      exact ih hnext_vc hnext_bound

/-- If `algB_sweep` leaves `S` unchanged, every seed step `v ∈ seeds` with `v ∈ S` must leave `S` unchanged. -/
public theorem algB_sweep_eq_imp_step_eq
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    (seeds : List V) (hfixed : algB_sweep G nbrOrder seeds S = S)
    (v : V) (hv : v ∈ seeds) (hvS : v ∈ S) :
    algB_step G S nbrOrder v = S := by
  induction seeds generalizing S with
  | nil => contradiction
  | cons x xs ih =>
    unfold algB_sweep at hfixed
    simp only [List.foldl_cons] at hfixed
    set S' := if x ∈ S then algB_step G S nbrOrder x else S with hS'def
    have hS'_vc : VCover G S' := by
      by_cases hxS : x ∈ S
      · rw [ite_eq_left hxS] at hS'def
        rw [hS'def]
        exact algB_step_vcover hS hOrder hlen x hxS
      · rw [ite_eq_right hxS] at hS'def
        rw [hS'def]
        exact hS
    have hS'_le : S'.card ≤ S.card := by
      by_cases hxS : x ∈ S
      · rw [ite_eq_left hxS] at hS'def
        rw [hS'def]
        exact algB_step_card_le hS hOrder hlen x hxS
      · rw [ite_eq_right hxS] at hS'def
        rw [hS'def]
    have htail_le : (algB_sweep G nbrOrder xs S').card ≤ S'.card :=
      algB_sweep_card_le hS'_vc hOrder hlen xs
    have hS'_eq : S' = S := by
      have hcard_eq : S'.card = S.card := by
        have h1 : S.card ≤ S'.card := hfixed ▸ htail_le
        omega
      by_cases hxS : x ∈ S
      · rw [ite_eq_left hxS] at hS'def
        rcases algB_step_eq_or_card_lt hS hOrder hlen x hxS with heq | hlt
        · rw [hS'def, heq]
        · rw [hS'def] at hcard_eq
          omega
      · rw [ite_eq_right hxS] at hS'def
        exact hS'def
    have hfixed_xs : algB_sweep G nbrOrder xs S = S := by
      rw [hS'_eq] at hfixed
      exact hfixed
    rcases List.mem_cons.mp hv with rfl | hv_xs
    · have h1 : algB_step G S nbrOrder v = S' := by
        rw [hS'def, ite_eq_left hvS]
      rw [h1, hS'_eq]
    · exact ih hS hfixed_xs hv_xs hvS

/-- **Search Completeness at Fixed Point**:
    When Algorithm B reaches a sweep fixed point `algB_sweep G nbrOrder seeds S = S`,
    every seed `v ∈ seeds` (that remains in `S`) has been tested by Algorithm C and
    yields NO diminishing subcover (i.e., `|U_v| ≤ |W_v|`). -/
public theorem algB_fixed_point_no_diminishing_subcover
    {S : Finset V} (hS : VCover G S) {nbrOrder : V → List V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    (seeds : List V) (hfixed : algB_sweep G nbrOrder seeds S = S) :
    ∀ v ∈ seeds, v ∈ S →
      let C := runAlgC G S nbrOrder (seedFuel G S nbrOrder v) v
      (reachU G S C v).card ≤ (reachW G S C v).card := by
  intro v hv_in_seeds hv_in_S
  dsimp
  by_contra hlt
  push Not at hlt
  have hstep_lt : (algB_step G S nbrOrder v).card < S.card :=
    algB_step_card_lt_of_reach_lt v hv_in_S hlt
  have hstep_eq : algB_step G S nbrOrder v = S :=
    algB_sweep_eq_imp_step_eq hS hOrder hlen seeds hfixed v hv_in_seeds hv_in_S
  rw [hstep_eq] at hstep_lt
  exact lt_irrefl S.card hstep_lt

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking. (Petersen Matching axiom imported.)

-/
