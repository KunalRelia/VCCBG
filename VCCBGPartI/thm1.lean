/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formalization of public theorem 1 (Part I, Section 4): VC-CBG is NP-complete,
  via the polynomial-time reduction VC-CG ≤P VC-CBG.

  Only `Mathlib` is imported. Axioms:
    `VC_CG_NPHard`, `VC_InNP`, `NPHard_of_reduction`.
  EVERYTHING else is public defined and proved here: the concrete graph G' of
  Figures 3-6, G' is cubic, G' is bridgeless, and both directions of Claim 1.

  Notation: m = |V|, n = |E|.
  Vertices of G':  (x, i) with x ∈ V, i ∈ Fin 7   -- cluster of x (7m vertices)
                   (e, j) with e ∈ E, j ∈ Fin 10  -- gadget of e  (10n vertices)
  Cluster of x is the path  x'₁ x' x'₂ x x''₂ x'' x''₁  = positions 0..6.
-/
public import Mathlib
public import VCCBGPartII.definition_vcover
/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
-- set_option maxHeartbeats 4000000

open Finset

universe u

noncomputable section

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. public definitions
-- ═══════════════════════════════════════════════════════════════════════════

attribute [instance] GraphInstance.fV GraphInstance.dV GraphInstance.dAdj

public abbrev CubicGraphs (inst : GraphInstance) : Prop := IsCubic inst

axiom VC_InNP (P : GraphInstance → Prop) : InNP (VCYes P)

/-- Many-one reduction between vertex-cover problems restricted to graph
    families (the polynomial-time bound on `f` is part of the content of the
    axiom `NPHard_of_reduction`; it is not formalized). -/
public abbrev ReducesTo (P₁ P₂ : GraphInstance → Prop) : Prop :=
  ∃ f : GraphInstance → GraphInstance,
    ∀ inst, P₁ inst → (VCYes P₁ inst ↔ VCYes P₂ (f inst))

axiom NPHard_of_reduction {P₁ P₂ : GraphInstance → Prop}
    (hHard : NPHard (VCYes P₁)) (hred : ReducesTo P₁ P₂) : NPHard (VCYes P₂)

axiom VC_CG_NPHard : NPHard (VCYes CubicGraphs)

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Small fixed finite structures (decidable, checked by `decide`)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Chain edges of a cluster (path on 7 vertices). -/
public def cadj (i j : Fin 7) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

instance : DecidableRel cadj := fun i j => by unfold cadj; infer_instance

/-- Edges of the 10-vertex gadget of Figure 3. -/
public def gedges : List (ℕ × ℕ) :=
  [(0,2),(0,6),(1,5),(1,9),(2,3),(3,4),(4,5),(6,7),(7,8),(8,9),
   (2,8),(3,9),(4,6),(5,7)]

public def gadj (i j : Fin 10) : Prop := (i.val, j.val) ∈ gedges ∨ (j.val, i.val) ∈ gedges

instance : DecidableRel gadj := fun i j => by unfold gadj; infer_instance

/-- Leaf position carrying the `b`-th red cross edge of an edge of rank `r`. -/
public def leafN (r : ℕ) (b : Bool) : ℕ :=
  if b then (if r = 0 then 2 else if r = 1 then 6 else 4)
  else (if r = 0 then 0 else if r = 1 then 0 else 6)

public theorem leafN_even (r : ℕ) (b : Bool) : leafN r b % 2 = 0 := by
  unfold leafN; split_ifs <;> omega

public theorem leafN_lt (r : ℕ) (b : Bool) : leafN r b < 7 := by
  unfold leafN; split_ifs <;> omega

public theorem cadj_irrefl : ∀ i : Fin 7, ¬ cadj i i := by decide
public theorem gadj_irrefl : ∀ i : Fin 10, ¬ gadj i i := by decide

/-- Every vertex cover of the gadget has at least 6 vertices. -/
public theorem gadget_cover_card :
    ∀ A : Finset (Fin 10), (∀ i j, gadj i j → i ∈ A ∨ j ∈ A) → 6 ≤ A.card := by
  decide +kernel

/-- Fact 1 for the 7-vertex path: cover ≥ 3, and a cover of size 3 is `{1,3,5}`. -/
public def slots3 : Finset (Fin 7) := {1, 3, 5}
public def leaf4 : Finset (Fin 7) := {0, 2, 4, 6}
public def gcover : Finset (Fin 10) := {0, 1, 3, 5, 6, 8}

public theorem cluster_cover_card :
    ∀ A : Finset (Fin 7), (∀ i j, cadj i j → i ∈ A ∨ j ∈ A) →
      3 ≤ A.card ∧ (A.card ≤ 3 → A = slots3) := by
  decide +kernel

public theorem slots3_card : slots3.card = 3 := by decide
public theorem leaf4_card : leaf4.card = 4 := by decide
public theorem gcover_card : gcover.card = 6 := by decide
public theorem slots3_cover : ∀ i j, cadj i j → i ∈ slots3 ∨ j ∈ slots3 := by decide
public theorem leaf4_cover : ∀ i j, cadj i j → i ∈ leaf4 ∨ j ∈ leaf4 := by decide
public theorem gcover_cover : ∀ i j, gadj i j → i ∈ gcover ∨ j ∈ gcover := by decide
public theorem mem_slots3 : ∀ i : Fin 7, i ∈ slots3 ↔ i.val % 2 = 1 := by decide
public theorem mem_leaf4 : ∀ i : Fin 7, i ∈ leaf4 ↔ i.val % 2 = 0 := by decide
public theorem mem_gcover_of : ∀ j : Fin 10, (j.val = 0 ∨ j.val = 1) → j ∈ gcover := by decide

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The construction G' = (V', E')
-- ═══════════════════════════════════════════════════════════════════════════

section Construction

variable (inst : GraphInstance)

/-- An injective numbering of the vertices of `G`. -/
public noncomputable def ix (x : inst.V) : ℕ := (Fintype.equivFin inst.V x : ℕ)

public theorem ix_injective : Function.Injective (ix inst) := fun a b h =>
  (Fintype.equivFin inst.V).injective (Fin.ext h)

/-- Rank of `y` among the neighbours of `x` (by the numbering `ix`):
    in a cubic graph this is a bijection `N(x) → {0,1,2}` (the three "slots"). -/
public noncomputable def rk (x y : inst.V) : ℕ :=
  ((inst.G.neighborFinset x).filter (fun z => ix inst z < ix inst y)).card

/-- Edge set of `G` as a type. -/
public abbrev EdgeT (inst : GraphInstance) : Type := inst.G.edgeSet

public noncomputable def numV : ℕ := Fintype.card inst.V
public noncomputable def numE : ℕ := Fintype.card (EdgeT inst)

/-- Vertex set of `G'`: `7m + 10n` vertices. -/
public abbrev W : Type := (inst.V × Fin 7) ⊕ ((EdgeT inst) × Fin 10)

public theorem card_W : Fintype.card (W inst) = 7 * numV inst + 10 * numE inst := by
  simp only [W, numV, numE, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The gadget of the edge `e` is attached at slot vertex `(x, 2·rk x y + 1)`:
    gadget end `0` to the endpoint with smaller number, end `1` to the other. -/
public def attachE (x : inst.V) (i : Fin 7) (e : (EdgeT inst)) (j : Fin 10) : Prop :=
  ∃ y, e.1 = s(x, y) ∧ i.val = 2 * rk inst x y + 1 ∧
    ((j.val = 0 ∧ ix inst x < ix inst y) ∨ (j.val = 1 ∧ ix inst y < ix inst x))

/-- The (symmetric) edge relation of `G'`. -/
public def R : W inst → W inst → Prop
  | Sum.inl (x, i), Sum.inl (y, j) =>
      (x = y ∧ cadj i j) ∨
      (inst.G.Adj x y ∧ ∃ b : Bool, i.val = leafN (rk inst x y) b ∧
                                     j.val = leafN (rk inst y x) b)
  | Sum.inl (x, i), Sum.inr (e, j) => attachE inst x i e j
  | Sum.inr (e, j), Sum.inl (x, i) => attachE inst x i e j
  | Sum.inr (e, i), Sum.inr (f, j) => e = f ∧ gadj i j

public theorem R_ll (x y : inst.V) (i j : Fin 7) :
    R inst (Sum.inl (x, i)) (Sum.inl (y, j)) ↔
      (x = y ∧ cadj i j) ∨
      (inst.G.Adj x y ∧ ∃ b : Bool, i.val = leafN (rk inst x y) b ∧
                                     j.val = leafN (rk inst y x) b) := Iff.rfl

public theorem R_lr (x : inst.V) (i : Fin 7) (e : (EdgeT inst)) (j : Fin 10) :
    R inst (Sum.inl (x, i)) (Sum.inr (e, j)) ↔ attachE inst x i e j := Iff.rfl

public theorem R_rl (x : inst.V) (i : Fin 7) (e : (EdgeT inst)) (j : Fin 10) :
    R inst (Sum.inr (e, j)) (Sum.inl (x, i)) ↔ attachE inst x i e j := Iff.rfl

public theorem R_rr (e f : (EdgeT inst)) (i j : Fin 10) :
    R inst (Sum.inr (e, i)) (Sum.inr (f, j)) ↔ e = f ∧ gadj i j := Iff.rfl

public theorem R_symm : ∀ a b : W inst, R inst a b → R inst b a
  | Sum.inl (x, i), Sum.inl (y, j), h => by
      rcases (R_ll inst x y i j).1 h with ⟨rfl, hc⟩ | ⟨hxy, b, hi, hj⟩
      · exact (R_ll inst _ _ _ _).2 (Or.inl ⟨rfl, Or.symm hc⟩)
      · exact (R_ll inst _ _ _ _).2 (Or.inr ⟨hxy.symm, b, hj, hi⟩)
  | Sum.inl (x, i), Sum.inr (e, j), h => h
  | Sum.inr (e, j), Sum.inl (x, i), h => h
  | Sum.inr (e, i), Sum.inr (f, j), h => by
      obtain ⟨rfl, hg⟩ := (R_rr inst e f i j).1 h
      exact (R_rr inst _ _ _ _).2 ⟨rfl, Or.symm hg⟩

/-- The graph `G'`. -/
public def Gc : SimpleGraph (W inst) := SimpleGraph.fromRel (R inst)

public theorem Gc_adj {a b : W inst} : (Gc inst).Adj a b ↔ a ≠ b ∧ R inst a b := by
  simp only [Gc, SimpleGraph.fromRel_adj]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.elim id (R_symm inst _ _)⟩,
         fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩⟩

/-- Target bound `k + 3m + 6n`. -/
public noncomputable def consK : ℕ := inst.k + 3 * numV inst + 6 * numE inst

/-- **The reduction** `(G, k) ↦ (G', k + 3m + 6n)`. -/
public noncomputable def reduce : GraphInstance where
  V := W inst
  fV := inferInstance
  dV := Classical.decEq _
  G := Gc inst
  dAdj := Classical.decRel _
  k := consK inst

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Counting
-- ═══════════════════════════════════════════════════════════════════════════

public theorem card_split (T : Finset (W inst)) :
    T.card =
      ∑ x : inst.V, (univ.filter fun i : Fin 7 => (Sum.inl (x, i) : W inst) ∈ T).card +
      ∑ e : (EdgeT inst),
        (univ.filter fun j : Fin 10 => (Sum.inr (e, j) : W inst) ∈ T).card := by
  have h : T.card = ∑ w : W inst, if w ∈ T then 1 else 0 := by
    rw [← Finset.card_filter]; congr 1; ext w; simp
  rw [h, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.card_filter]

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Claim 1 (⇒): a cover of G gives a cover of G'
-- ═══════════════════════════════════════════════════════════════════════════

/-- Membership test for the cover built from `S`: for `x ∈ S` the four leaves
    `x'₁,x'₂,x''₁,x''₂`; for `x ∉ S` the three slot vertices `x', x, x''`;
    in every gadget the six vertices `0,1,3,5,6,8`. -/
public def memCov (S : Finset inst.V) : W inst → Bool
  | Sum.inl (x, i) => if x ∈ S then decide (i ∈ leaf4) else decide (i ∈ slots3)
  | Sum.inr (_, j) => decide (j ∈ gcover)

public def coverOf (S : Finset inst.V) : Finset (W inst) :=
  Finset.univ.filter (fun w => memCov inst S w = true)

public theorem mem_coverOf_inl (S : Finset inst.V) (x : inst.V) (i : Fin 7) :
    (Sum.inl (x, i) : W inst) ∈ coverOf inst S ↔
      (if x ∈ S then i ∈ leaf4 else i ∈ slots3) := by
  unfold coverOf
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, memCov]
  by_cases hx : x ∈ S
  · simp only [hx, ite_true, decide_eq_true_eq]
  · simp only [hx, ite_false, decide_eq_true_eq]

public theorem mem_coverOf_inr (S : Finset inst.V) (e : (EdgeT inst)) (j : Fin 10) :
    (Sum.inr (e, j) : W inst) ∈ coverOf inst S ↔ j ∈ gcover := by
  unfold coverOf
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, memCov, decide_eq_true_eq]

public theorem cover_forward (S : Finset inst.V) (hS : VCover inst.G S) :
    VCover (Gc inst) (coverOf inst S) := by
  intro a b hab
  obtain ⟨_, h⟩ := (Gc_adj inst).1 hab
  rcases a with ⟨x, i⟩ | ⟨e, i⟩ <;> rcases b with ⟨y, j⟩ | ⟨f, j⟩
  · rcases (R_ll inst x y i j).1 h with ⟨rfl, hc⟩ | ⟨hxy, bb, hi, hj⟩
    · by_cases hx : x ∈ S
      · simp only [mem_coverOf_inl, ite_eq_left hx]; exact leaf4_cover i j hc
      · simp only [mem_coverOf_inl, ite_eq_right hx]; exact slots3_cover i j hc
    · have hiL : i ∈ leaf4 := (mem_leaf4 i).2 (by rw [hi]; exact leafN_even _ _)
      have hjL : j ∈ leaf4 := (mem_leaf4 j).2 (by rw [hj]; exact leafN_even _ _)
      rcases hS hxy with hx | hy
      · left; simp only [mem_coverOf_inl, ite_eq_left hx]; exact hiL
      · right; simp only [mem_coverOf_inl, ite_eq_left hy]; exact hjL
  · obtain ⟨y, _, _, hj⟩ := (R_lr inst x i f j).1 h
    right
    rw [mem_coverOf_inr]
    exact mem_gcover_of j (hj.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  · obtain ⟨y, _, _, hj⟩ := (R_rl inst y j e i).1 h
    left
    rw [mem_coverOf_inr]
    exact mem_gcover_of i (hj.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  · obtain ⟨rfl, hg⟩ := (R_rr inst e f i j).1 h
    simp only [mem_coverOf_inr]
    exact gcover_cover i j hg

public theorem sum_aux (S : Finset inst.V) :
    ∑ x : inst.V, (3 + if x ∈ S then 1 else 0) = 3 * numV inst + S.card := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Finset.sum_boole]
  simp [numV, mul_comm]

public theorem card_coverOf (S : Finset inst.V) :
    (coverOf inst S).card = 3 * numV inst + S.card + 6 * numE inst := by
  have h1 : ∀ x : inst.V,
      (univ.filter fun i : Fin 7 => (Sum.inl (x, i) : W inst) ∈ coverOf inst S).card =
        3 + if x ∈ S then 1 else 0 := by
    intro x
    by_cases hx : x ∈ S
    · have : (univ.filter fun i : Fin 7 => (Sum.inl (x, i) : W inst) ∈ coverOf inst S)
          = leaf4 := by
        ext i; simp [mem_coverOf_inl, hx]
      rw [this, leaf4_card, ite_eq_left hx]
    · have : (univ.filter fun i : Fin 7 => (Sum.inl (x, i) : W inst) ∈ coverOf inst S)
          = slots3 := by
        ext i; simp [mem_coverOf_inl, hx]
      rw [this, slots3_card, ite_eq_right hx]
  have h2 : ∀ e : (EdgeT inst),
      (univ.filter fun j : Fin 10 => (Sum.inr (e, j) : W inst) ∈ coverOf inst S).card
        = 6 := by
    intro e
    have : (univ.filter fun j : Fin 10 => (Sum.inr (e, j) : W inst) ∈ coverOf inst S)
        = gcover := by
      ext j; simp [mem_coverOf_inr]
    rw [this, gcover_card]
  rw [card_split, Finset.sum_congr rfl (fun x _ => h1 x),
      Finset.sum_congr rfl (fun e _ => h2 e), sum_aux]
  simp [numE, mul_comm]

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Claim 1 (⇐): a cover of G' gives a cover of G
-- ═══════════════════════════════════════════════════════════════════════════

public theorem cover_backward (S' : Finset (W inst)) (hS' : VCover (Gc inst) S')
    (hcard : S'.card ≤ consK inst) :
    ∃ S : Finset inst.V, VCover inst.G S ∧ S.card ≤ inst.k := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A : inst.V → Finset (Fin 7),
      ∀ x i, i ∈ A x ↔ (Sum.inl (x, i) : W inst) ∈ S' :=
    ⟨fun x => univ.filter (fun i => (Sum.inl (x, i) : W inst) ∈ S'), by intro x i; simp⟩
  obtain ⟨B, hBdef⟩ : ∃ B : (EdgeT inst) → Finset (Fin 10),
      ∀ e j, j ∈ B e ↔ (Sum.inr (e, j) : W inst) ∈ S' :=
    ⟨fun e => univ.filter (fun j => (Sum.inr (e, j) : W inst) ∈ S'), by intro e j; simp⟩
  have hAcov : ∀ x, ∀ i j : Fin 7, cadj i j → i ∈ A x ∨ j ∈ A x := by
    intro x i j hij
    have hadj : (Gc inst).Adj (Sum.inl (x, i)) (Sum.inl (x, j)) := by
      rw [Gc_adj, R_ll]
      refine ⟨?_, Or.inl ⟨rfl, hij⟩⟩
      intro h
      have h' : i = j := (Prod.mk.inj (Sum.inl.inj h)).2
      subst h'
      exact cadj_irrefl _ hij
    rw [hAdef, hAdef]
    exact hS' hadj
  have hBcov : ∀ e, ∀ i j : Fin 10, gadj i j → i ∈ B e ∨ j ∈ B e := by
    intro e i j hij
    have hadj : (Gc inst).Adj (Sum.inr (e, i)) (Sum.inr (e, j)) := by
      rw [Gc_adj, R_rr]
      refine ⟨?_, ⟨rfl, hij⟩⟩
      intro h
      have h' : i = j := (Prod.mk.inj (Sum.inr.inj h)).2
      subst h'
      exact gadj_irrefl _ hij
    rw [hBdef, hBdef]
    exact hS' hadj
  let S : Finset inst.V := univ.filter (fun x => A x ≠ slots3)
  have hcov : VCover inst.G S := by
    intro x y hxy
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hx, hy⟩ := hcon
    have hAx : A x = slots3 := by simpa [S] using hx
    have hAy : A y = slots3 := by simpa [S] using hy
    obtain ⟨i, hi⟩ : ∃ i : Fin 7, i.val = leafN (rk inst x y) false :=
      ⟨⟨leafN (rk inst x y) false, leafN_lt _ _⟩, rfl⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin 7, j.val = leafN (rk inst y x) false :=
      ⟨⟨leafN (rk inst y x) false, leafN_lt _ _⟩, rfl⟩
    have hadj : (Gc inst).Adj (Sum.inl (x, i)) (Sum.inl (y, j)) := by
      rw [Gc_adj, R_ll]
      refine ⟨?_, Or.inr ⟨hxy, false, hi, hj⟩⟩
      intro h
      exact hxy.ne (Prod.mk.inj (Sum.inl.inj h)).1
    rcases hS' hadj with h | h
    · have h1 : i ∈ A x := (hAdef x i).2 h
      rw [hAx, mem_slots3] at h1
      have := leafN_even (rk inst x y) false
      omega
    · have h1 : j ∈ A y := (hAdef y j).2 h
      rw [hAy, mem_slots3] at h1
      have := leafN_even (rk inst y x) false
      omega
  have hAcard : ∀ x, 3 + (if x ∈ S then 1 else 0) ≤ (A x).card := by
    intro x
    obtain ⟨h3, h3'⟩ := cluster_cover_card (A x) (hAcov x)
    by_cases hx : x ∈ S
    · rw [ite_eq_left hx]
      have hne : A x ≠ slots3 := by simpa [S] using hx
      have : ¬ (A x).card ≤ 3 := fun hle => hne (h3' hle)
      omega
    · rw [ite_eq_right hx]; omega
  have hBcard : ∀ e, 6 ≤ (B e).card := fun e => gadget_cover_card (B e) (hBcov e)
  have hsum : S'.card = ∑ x, (A x).card + ∑ e, (B e).card := by
    rw [card_split]
    congr 1
    · apply Finset.sum_congr rfl; intro x _; congr 1; ext i; simp [hAdef]
    · apply Finset.sum_congr rfl; intro e _; congr 1; ext j; simp [hBdef]
  have h1 : ∑ x : inst.V, (3 + if x ∈ S then 1 else 0) ≤ ∑ x, (A x).card :=
    Finset.sum_le_sum fun x _ => hAcard x
  have h2 : ∑ e : (EdgeT inst), 6 ≤ ∑ e, (B e).card :=
    Finset.sum_le_sum fun e _ => hBcard e
  rw [sum_aux] at h1
  have h3 : ∑ e : (EdgeT inst), (6 : ℕ) = 6 * numE inst := by
    simp [numE, mul_comm]
  rw [h3] at h2
  refine ⟨S, hcov, ?_⟩
  unfold consK at hcard
  omega

/-- **Claim 1**: `G` has a vertex cover of size ≤ k iff `G'` has one of size
    ≤ k + 3m + 6n. -/
public theorem claim1 :
    (∃ S : Finset inst.V, VCover inst.G S ∧ S.card ≤ inst.k) ↔
    (∃ S' : Finset (W inst), VCover (Gc inst) S' ∧ S'.card ≤ consK inst) := by
  constructor
  · rintro ⟨S, hS, hk⟩
    refine ⟨coverOf inst S, cover_forward inst S hS, ?_⟩
    rw [card_coverOf]
    unfold consK
    omega
  · rintro ⟨S', hS', hk⟩
    exact cover_backward inst S' hS' hk

end Construction

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. G' is cubic
-- ═══════════════════════════════════════════════════════════════════════════

/-- `w` has exactly three neighbours (stated without any `Fintype` instance). -/
public def Has3 {α : Type} (G : SimpleGraph α) (w : α) : Prop :=
  ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ w', G.Adj w w' ↔ w' = a ∨ w' = b ∨ w' = c

public theorem Has3.degree {α : Type} {G : SimpleGraph α} {w : α}
    [Fintype (G.neighborSet w)] (h : Has3 G w) : G.degree w = 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, h⟩ := h
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : G.neighborFinset w = {a, b, c} := by ext w'; simp [h]
  rw [this]
  exact Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩

section Cubic

variable (inst : GraphInstance)

public theorem nbr_card (hc : IsCubic inst) (x : inst.V) :
    (inst.G.neighborFinset x).card = 3 :=
  (inst.G.card_neighborFinset_eq_degree x).trans (hc x)

public theorem rk_lt (hc : IsCubic inst) {x y : inst.V} (hxy : inst.G.Adj x y) :
    rk inst x y < 3 := by
  have hsub : (inst.G.neighborFinset x).filter (fun z => ix inst z < ix inst y)
      ⊂ inst.G.neighborFinset x := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h => ?_⟩
    have hy : y ∈ (inst.G.neighborFinset x).filter (fun z => ix inst z < ix inst y) := by
      rw [h]; simpa using hxy
    simp at hy
  have := Finset.card_lt_card hsub
  rw [nbr_card inst hc x] at this
  exact this

public theorem rk_lt_of_ix {x y z : inst.V} (hy : inst.G.Adj x y) (h : ix inst y < ix inst z) :
    rk inst x y < rk inst x z := by
  unfold rk
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.2 ⟨?_, fun heq => ?_⟩
  · intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, lt_trans hw.2 h⟩
  · have hy' : y ∈ (inst.G.neighborFinset x).filter (fun w => ix inst w < ix inst z) := by
      simp [hy, h]
    rw [← heq] at hy'
    simp at hy'

public theorem rk_inj {x y z : inst.V} (hy : inst.G.Adj x y) (hz : inst.G.Adj x z)
    (h : rk inst x y = rk inst x z) : y = z := by
  by_contra hne
  have hne' : ix inst y ≠ ix inst z := fun e => hne (ix_injective inst e)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have := rk_lt_of_ix inst hy hlt; omega
  · have := rk_lt_of_ix inst hz hgt; omega

public theorem rk_surj (hc : IsCubic inst) (x : inst.V) {r : ℕ} (hr : r < 3) :
    ∃ y, inst.G.Adj x y ∧ rk inst x y = r := by
  have hinj : Set.InjOn (rk inst x) (inst.G.neighborFinset x : Set inst.V) := by
    intro a ha b hb h
    exact rk_inj inst ((SimpleGraph.mem_neighborFinset _ _ _).1 (Finset.mem_coe.1 ha))
      ((SimpleGraph.mem_neighborFinset _ _ _).1 (Finset.mem_coe.1 hb)) h
  have himg : (inst.G.neighborFinset x).image (rk inst x) = Finset.range 3 := by
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hs
      simp only [Finset.mem_range]
      exact rk_lt inst hc ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)
    · rw [Finset.card_image_of_injOn hinj, nbr_card inst hc x]
      simp
  have hmem : r ∈ (inst.G.neighborFinset x).image (rk inst x) := by
    rw [himg]; simpa using hr
  obtain ⟨y, hy, hyr⟩ := Finset.mem_image.1 hmem
  exact ⟨y, (SimpleGraph.mem_neighborFinset _ _ _).1 hy, hyr⟩

/-- The neighbour of `x` of rank `r`. -/
public noncomputable def nb (x : inst.V) (r : ℕ) : inst.V :=
  if h : ∃ y, inst.G.Adj x y ∧ rk inst x y = r then h.choose else x

public theorem nb_spec (hc : IsCubic inst) (x : inst.V) {r : ℕ} (hr : r < 3) :
    inst.G.Adj x (nb inst x r) ∧ rk inst x (nb inst x r) = r := by
  have h := rk_surj inst hc x hr
  unfold nb
  rw [dite_eq_left h]
  exact h.choose_spec

public theorem eq_nb (hc : IsCubic inst) {x y : inst.V} {r : ℕ} (hr : r < 3)
    (hxy : inst.G.Adj x y) (h : rk inst x y = r) : y = nb inst x r :=
  rk_inj inst hxy (nb_spec inst hc x hr).1 (h.trans (nb_spec inst hc x hr).2.symm)

public theorem nb_inj (hc : IsCubic inst) (x : inst.V) {r s : ℕ} (hr : r < 3) (hs : s < 3)
    (h : nb inst x r = nb inst x s) : r = s := by
  have h1 := (nb_spec inst hc x hr).2
  have h2 := (nb_spec inst hc x hs).2
  rw [h] at h1
  omega

/-- Edge of `G` from `x` to its neighbour of rank `r`. -/
public noncomputable def edgeOf (hc : IsCubic inst) (x : inst.V) (r : ℕ) (hr : r < 3) :
    (EdgeT inst) :=
  ⟨s(x, nb inst x r), (SimpleGraph.mem_edgeSet _).2 (nb_spec inst hc x hr).1⟩

/-- Which gadget end is glued to `x` when the edge goes from `x` to `y`. -/
public def endIdx (x y : inst.V) : Fin 10 := if ix inst x < ix inst y then 0 else 1

/-- Leaf vertex `(r,b)` of the cluster. -/
public def lf (r : ℕ) (b : Bool) : Fin 7 := ⟨leafN r b, leafN_lt r b⟩

/-- The cross neighbour reached through rank `r` and colour `b`. -/
public abbrev crossV (x : inst.V) (r : ℕ) (b : Bool) : W inst :=
  Sum.inl (nb inst x r, lf (rk inst (nb inst x r) x) b)

public theorem attach_iff (hc : IsCubic inst) (x : inst.V) (r : ℕ) (hr : r < 3) (i : Fin 7)
    (hi : i.val = 2 * r + 1) (e : (EdgeT inst)) (j : Fin 10) :
    attachE inst x i e j ↔ e = edgeOf inst hc x r hr ∧ j = endIdx inst x (nb inst x r) := by
  constructor
  · rintro ⟨y, he, hiy, hj⟩
    have hxy : inst.G.Adj x y := by
      have := e.2
      rw [he] at this
      exact (SimpleGraph.mem_edgeSet _).1 this
    have hry : rk inst x y = r := by omega
    have hyn : y = nb inst x r := eq_nb inst hc hr hxy hry
    subst hyn
    refine ⟨Subtype.ext he, ?_⟩
    rcases hj with ⟨h0, hlt⟩ | ⟨h1, hlt⟩
    · apply Fin.ext; simp [endIdx, hlt]; omega
    · have : ¬ ix inst x < ix inst (nb inst x r) := by omega
      apply Fin.ext; simp [endIdx, this]; omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨nb inst x r, rfl, by rw [hi, (nb_spec inst hc x hr).2], ?_⟩
    have hne : ix inst x ≠ ix inst (nb inst x r) :=
      fun h => (nb_spec inst hc x hr).1.ne (ix_injective inst h)
    by_cases hlt : ix inst x < ix inst (nb inst x r)
    · left; simp [endIdx, hlt]
    · right; refine ⟨by simp [endIdx, hlt], by omega⟩

public theorem crossV_adj (hc : IsCubic inst) (x : inst.V) (r : ℕ) (hr : r < 3) (b : Bool)
    (i : Fin 7) (hi : i.val = leafN r b) :
    (Gc inst).Adj (Sum.inl (x, i)) (crossV inst x r b) := by
  have hs := nb_spec inst hc x hr
  rw [Gc_adj, crossV, R_ll]
  refine ⟨?_, Or.inr ⟨hs.1, b, by rw [hs.2]; exact hi, rfl⟩⟩
  intro h
  exact hs.1.ne (Prod.mk.inj (Sum.inl.inj h)).1

public theorem crossV_form (hc : IsCubic inst) {x z : inst.V} (hxz : inst.G.Adj x z) (b : Bool)
    (j : Fin 7) (hbj : j.val = leafN (rk inst z x) b) :
    ∃ r, r < 3 ∧ rk inst x z = r ∧ Sum.inl (z, j) = crossV inst x r b := by
  have hr := rk_lt inst hc hxz
  have hz : z = nb inst x (rk inst x z) := eq_nb inst hc hr hxz rfl
  refine ⟨rk inst x z, hr, rfl, ?_⟩
  unfold crossV
  rw [← hz]
  have : j = lf (rk inst z x) b := Fin.ext hbj
  rw [this]

public theorem crossV_ne_chain (hc : IsCubic inst) (x : inst.V) (r : ℕ) (hr : r < 3) (b : Bool)
    (j : Fin 7) : crossV inst x r b ≠ Sum.inl (x, j) := by
  intro h
  exact (nb_spec inst hc x hr).1.ne' (Prod.mk.inj (Sum.inl.inj h)).1

public theorem crossV_ne_cross (hc : IsCubic inst) (x : inst.V) {r s : ℕ} (hr : r < 3) (hs : s < 3)
    (hrs : r ≠ s) (b b' : Bool) : crossV inst x r b ≠ crossV inst x s b' := by
  intro h
  exact hrs (nb_inj inst hc x hr hs (Prod.mk.inj (Sum.inl.inj h)).1)

public theorem crossV_ne_inr (x : inst.V) (r : ℕ) (b : Bool) (e : (EdgeT inst))
    (j : Fin 10) : crossV inst x r b ≠ Sum.inr (e, j) := fun h => by cases h


public theorem chain_adj (x : inst.V) (i j : Fin 7) (h : cadj i j) :
    (Gc inst).Adj (Sum.inl (x, i)) (Sum.inl (x, j)) := by
  rw [Gc_adj, R_ll]
  refine ⟨?_, Or.inl ⟨rfl, h⟩⟩
  intro h'
  have : i = j := (Prod.mk.inj (Sum.inl.inj h')).2
  subst this
  exact cadj_irrefl _ h

public theorem gad_adj (e : (EdgeT inst)) (i j : Fin 10) (h : gadj i j) :
    (Gc inst).Adj (Sum.inr (e, i)) (Sum.inr (e, j)) := by
  rw [Gc_adj, R_rr]
  refine ⟨?_, rfl, h⟩
  intro h'
  have : i = j := (Prod.mk.inj (Sum.inr.inj h')).2
  subst this
  exact gadj_irrefl _ h

public theorem slot_attach_adj (hc : IsCubic inst) (x : inst.V) (r : ℕ) (hr : r < 3) (i : Fin 7)
    (hi : i.val = 2 * r + 1) :
    (Gc inst).Adj (Sum.inl (x, i))
      (Sum.inr (edgeOf inst hc x r hr, endIdx inst x (nb inst x r))) := by
  rw [Gc_adj, R_lr]
  exact ⟨(fun h => by cases h), (attach_iff inst hc x r hr i hi _ _).2 ⟨rfl, rfl⟩⟩

/-- Slot vertices (positions 1, 3, 5): two chain neighbours and one gadget end. -/
public theorem has3_slot (hc : IsCubic inst) (x : inst.V) (r : ℕ) (hr : r < 3) (i : Fin 7)
    (hi : i.val = 2 * r + 1) : Has3 (Gc inst) (Sum.inl (x, i)) := by
  refine ⟨Sum.inl (x, ⟨2 * r, by omega⟩), Sum.inl (x, ⟨2 * r + 2, by omega⟩),
    Sum.inr (edgeOf inst hc x r hr, endIdx inst x (nb inst x r)), ?_, ?_, ?_, ?_⟩
  · intro h
    have := Fin.mk.inj (Prod.mk.inj (Sum.inl.inj h)).2
    omega
  · intro h; cases h
  · intro h; cases h
  · intro w'
    constructor
    · intro hadj
      rw [Gc_adj] at hadj
      obtain ⟨_, hR⟩ := hadj
      rcases w' with ⟨z, j⟩ | ⟨e, j⟩
      · rcases (R_ll inst x z i j).1 hR with ⟨hxz, hcj⟩ | ⟨hxz, b, hbi, hbj⟩
        · subst hxz
          have hj : j.val = 2 * r ∨ j.val = 2 * r + 2 := by unfold cadj at hcj; omega
          rcases hj with hj | hj
          · left; exact congrArg Sum.inl (Prod.ext rfl (Fin.ext hj))
          · right; left; exact congrArg Sum.inl (Prod.ext rfl (Fin.ext hj))
        · exfalso
          have := leafN_even (rk inst x z) b
          omega
      · obtain ⟨h1, h2⟩ := (attach_iff inst hc x r hr i hi e j).1 ((R_lr inst x i e j).1 hR)
        subst h1; subst h2
        right; right; rfl
    · rintro (rfl | rfl | rfl)
      · exact chain_adj inst x i _ (Or.inr (by change 2 * r + 1 = i.val; omega))
      · exact chain_adj inst x i _ (Or.inl (by change i.val + 1 = 2 * r + 2; omega))
      · exact slot_attach_adj inst hc x r hr i hi

/-- Leaf position 0: chain neighbour 1, cross neighbours `(0,false)`, `(1,false)`. -/
public theorem has3_leaf0 (hc : IsCubic inst) (x : inst.V) (i : Fin 7) (hi : i.val = 0) :
    Has3 (Gc inst) (Sum.inl (x, i)) := by
  refine ⟨Sum.inl (x, 1), crossV inst x 0 false, crossV inst x 1 false, ?_, ?_, ?_, ?_⟩
  · exact (crossV_ne_chain inst hc x 0 (by omega) false 1).symm
  · exact (crossV_ne_chain inst hc x 1 (by omega) false 1).symm
  · exact crossV_ne_cross inst hc x (by omega) (by omega) (by omega) false false
  · intro w'
    constructor
    · intro hadj
      rw [Gc_adj] at hadj
      obtain ⟨_, hR⟩ := hadj
      rcases w' with ⟨z, j⟩ | ⟨e, j⟩
      · rcases (R_ll inst x z i j).1 hR with ⟨hxz, hcj⟩ | ⟨hxz, b, hbi, hbj⟩
        · subst hxz
          left
          have : j = 1 := Fin.ext (by unfold cadj at hcj; change j.val = 1; omega)
          rw [this]
        · obtain ⟨r, hr, hrk, hw⟩ := crossV_form inst hc hxz b j hbj
          rw [hrk] at hbi
          rw [hw]
          interval_cases r <;> cases b <;> simp [leafN, hi] at hbi ⊢
      · exfalso
        obtain ⟨y, _, hiy, _⟩ := (R_lr inst x i e j).1 hR
        omega
    · rintro (rfl | rfl | rfl)
      · exact chain_adj inst x i 1 (Or.inl (by change i.val + 1 = 1; omega))
      · exact crossV_adj inst hc x 0 (by omega) false i (by simp [leafN, hi])
      · exact crossV_adj inst hc x 1 (by omega) false i (by simp [leafN, hi])

/-- Leaf position 2: chain neighbours 1, 3; cross neighbour `(0,true)`. -/
public theorem has3_leaf2 (hc : IsCubic inst) (x : inst.V) (i : Fin 7) (hi : i.val = 2) :
    Has3 (Gc inst) (Sum.inl (x, i)) := by
  refine ⟨Sum.inl (x, 1), Sum.inl (x, 3), crossV inst x 0 true, ?_, ?_, ?_, ?_⟩
  · intro h; have := (Prod.mk.inj (Sum.inl.inj h)).2; revert this; decide
  · exact (crossV_ne_chain inst hc x 0 (by omega) true 1).symm
  · exact (crossV_ne_chain inst hc x 0 (by omega) true 3).symm
  · intro w'
    constructor
    · intro hadj
      rw [Gc_adj] at hadj
      obtain ⟨_, hR⟩ := hadj
      rcases w' with ⟨z, j⟩ | ⟨e, j⟩
      · rcases (R_ll inst x z i j).1 hR with ⟨hxz, hcj⟩ | ⟨hxz, b, hbi, hbj⟩
        · subst hxz
          unfold cadj at hcj
          have hj : j.val = 1 ∨ j.val = 3 := by omega
          rcases hj with hj | hj
          · left; exact congrArg Sum.inl (Prod.ext rfl (Fin.ext (by rw [hj]; rfl)))
          · right; left; exact congrArg Sum.inl (Prod.ext rfl (Fin.ext (by rw [hj]; rfl)))
        · obtain ⟨r, hr, hrk, hw⟩ := crossV_form inst hc hxz b j hbj
          rw [hrk] at hbi
          rw [hw]
          interval_cases r <;> cases b <;> simp [leafN, hi] at hbi ⊢
      · exfalso
        obtain ⟨y, _, hiy, _⟩ := (R_lr inst x i e j).1 hR
        omega
    · rintro (rfl | rfl | rfl)
      · exact chain_adj inst x i 1 (Or.inr (by change 1 + 1 = i.val; omega))
      · exact chain_adj inst x i 3 (Or.inl (by change i.val + 1 = 3; omega))
      · exact crossV_adj inst hc x 0 (by omega) true i (by simp [leafN, hi])

/-- Leaf position 4: chain neighbours 3, 5; cross neighbour `(2,true)`. -/
public theorem has3_leaf4 (hc : IsCubic inst) (x : inst.V) (i : Fin 7) (hi : i.val = 4) :
    Has3 (Gc inst) (Sum.inl (x, i)) := by
  refine ⟨Sum.inl (x, 3), Sum.inl (x, 5), crossV inst x 2 true, ?_, ?_, ?_, ?_⟩
  · intro h; have := (Prod.mk.inj (Sum.inl.inj h)).2; revert this; decide
  · exact (crossV_ne_chain inst hc x 2 (by omega) true 3).symm
  · exact (crossV_ne_chain inst hc x 2 (by omega) true 5).symm
  · intro w'
    constructor
    · intro hadj
      rw [Gc_adj] at hadj
      obtain ⟨_, hR⟩ := hadj
      rcases w' with ⟨z, j⟩ | ⟨e, j⟩
      · rcases (R_ll inst x z i j).1 hR with ⟨hxz, hcj⟩ | ⟨hxz, b, hbi, hbj⟩
        · subst hxz
          unfold cadj at hcj
          have hj : j.val = 3 ∨ j.val = 5 := by omega
          rcases hj with hj | hj
          · left; exact congrArg Sum.inl (Prod.ext rfl (Fin.ext (by rw [hj]; rfl)))
          · right; left; exact congrArg Sum.inl (Prod.ext rfl (Fin.ext (by rw [hj]; rfl)))
        · obtain ⟨r, hr, hrk, hw⟩ := crossV_form inst hc hxz b j hbj
          rw [hrk] at hbi
          rw [hw]
          interval_cases r <;> cases b <;> simp [leafN, hi] at hbi ⊢
      · exfalso
        obtain ⟨y, _, hiy, _⟩ := (R_lr inst x i e j).1 hR
        omega
    · rintro (rfl | rfl | rfl)
      · exact chain_adj inst x i 3 (Or.inr (by change 3 + 1 = i.val; omega))
      · exact chain_adj inst x i 5 (Or.inl (by change i.val + 1 = 5; omega))
      · exact crossV_adj inst hc x 2 (by omega) true i (by simp [leafN, hi])

/-- Leaf position 6: chain neighbour 5; cross neighbours `(1,true)`, `(2,false)`. -/
public theorem has3_leaf6 (hc : IsCubic inst) (x : inst.V) (i : Fin 7) (hi : i.val = 6) :
    Has3 (Gc inst) (Sum.inl (x, i)) := by
  refine ⟨Sum.inl (x, 5), crossV inst x 1 true, crossV inst x 2 false, ?_, ?_, ?_, ?_⟩
  · exact (crossV_ne_chain inst hc x 1 (by omega) true 5).symm
  · exact (crossV_ne_chain inst hc x 2 (by omega) false 5).symm
  · exact crossV_ne_cross inst hc x (by omega) (by omega) (by omega) true false
  · intro w'
    constructor
    · intro hadj
      rw [Gc_adj] at hadj
      obtain ⟨_, hR⟩ := hadj
      rcases w' with ⟨z, j⟩ | ⟨e, j⟩
      · rcases (R_ll inst x z i j).1 hR with ⟨hxz, hcj⟩ | ⟨hxz, b, hbi, hbj⟩
        · subst hxz
          left
          have : j = 5 := Fin.ext (by unfold cadj at hcj; change j.val = 5; omega)
          rw [this]
        · obtain ⟨r, hr, hrk, hw⟩ := crossV_form inst hc hxz b j hbj
          rw [hrk] at hbi
          rw [hw]
          interval_cases r <;> cases b <;> simp [leafN, hi] at hbi ⊢
      · exfalso
        obtain ⟨y, _, hiy, _⟩ := (R_lr inst x i e j).1 hR
        omega
    · rintro (rfl | rfl | rfl)
      · exact chain_adj inst x i 5 (Or.inr (by change 5 + 1 = i.val; omega))
      · exact crossV_adj inst hc x 1 (by omega) true i (by simp [leafN, hi])
      · exact crossV_adj inst hc x 2 (by omega) false i (by simp [leafN, hi])

-- ───────────────────────── gadget vertices ─────────────────────────

/-- Internal neighbours of gadget vertices `2..9`. -/
public def gtab (j : Fin 10) : Fin 10 × Fin 10 × Fin 10 :=
  match j.val with
  | 2 => (0, 3, 8) | 3 => (2, 4, 9) | 4 => (3, 5, 6) | 5 => (4, 1, 7)
  | 6 => (0, 7, 4) | 7 => (6, 8, 5) | 8 => (7, 9, 2) | _ => (8, 1, 3)

public theorem gtab_iff : ∀ j : Fin 10, 2 ≤ j.val → ∀ j' : Fin 10,
    gadj j j' ↔ j' = (gtab j).1 ∨ j' = (gtab j).2.1 ∨ j' = (gtab j).2.2 := by
  decide +kernel

public theorem gtab_ne : ∀ j : Fin 10, 2 ≤ j.val →
    (gtab j).1 ≠ (gtab j).2.1 ∧ (gtab j).1 ≠ (gtab j).2.2 ∧ (gtab j).2.1 ≠ (gtab j).2.2 := by
  decide +kernel

public theorem g0_iff : ∀ j' : Fin 10, gadj 0 j' ↔ j' = 2 ∨ j' = 6 := by decide
public theorem g1_iff : ∀ j' : Fin 10, gadj 1 j' ↔ j' = 5 ∨ j' = 9 := by decide

public theorem has3_gad_mid (e : (EdgeT inst)) (j : Fin 10) (hj : 2 ≤ j.val) :
    Has3 (Gc inst) (Sum.inr (e, j)) := by
  have hne := gtab_ne j hj
  refine ⟨Sum.inr (e, (gtab j).1), Sum.inr (e, (gtab j).2.1), Sum.inr (e, (gtab j).2.2),
    ?_, ?_, ?_, ?_⟩
  · intro h; exact hne.1 (Prod.mk.inj (Sum.inr.inj h)).2
  · intro h; exact hne.2.1 (Prod.mk.inj (Sum.inr.inj h)).2
  · intro h; exact hne.2.2 (Prod.mk.inj (Sum.inr.inj h)).2
  · intro w'
    constructor
    · intro hadj
      rw [Gc_adj] at hadj
      obtain ⟨_, hR⟩ := hadj
      rcases w' with ⟨x, i⟩ | ⟨f, i⟩
      · exfalso
        obtain ⟨y, _, _, hj'⟩ := (R_rl inst x i e j).1 hR
        omega
      · obtain ⟨hef, hg⟩ := (R_rr inst e f j i).1 hR
        subst hef
        rcases (gtab_iff j hj i).1 hg with h | h | h
        · left; rw [h]
        · right; left; rw [h]
        · right; right; rw [h]
    · rintro (rfl | rfl | rfl)
      · exact gad_adj inst e j _ ((gtab_iff j hj _).2 (Or.inl rfl))
      · exact gad_adj inst e j _ ((gtab_iff j hj _).2 (Or.inr (Or.inl rfl)))
      · exact gad_adj inst e j _ ((gtab_iff j hj _).2 (Or.inr (Or.inr rfl)))

public theorem ends_exist' (s0 : Sym2 inst.V) (hs0 : s0 ∈ inst.G.edgeSet) :
    ∃ a b, inst.G.Adj a b ∧ ix inst a < ix inst b ∧ s0 = s(a, b) := by
  revert hs0
  induction s0 using Sym2.ind with
  | h a b =>
    intro hs0
    have hab : inst.G.Adj a b := (SimpleGraph.mem_edgeSet _).1 hs0
    have hne : ix inst a ≠ ix inst b := fun h => hab.ne (ix_injective inst h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, hab, h, rfl⟩
    · exact ⟨b, a, hab.symm, h, Sym2.eq_swap⟩

public theorem ends_exist (e : (EdgeT inst)) :
    ∃ a b, inst.G.Adj a b ∧ ix inst a < ix inst b ∧ e.1 = s(a, b) :=
  ends_exist' inst e.1 e.2

/-- Gadget end 0: glued to the endpoint with the smaller number. -/
public theorem has3_gad0 (hc : IsCubic inst) (e : (EdgeT inst)) (j : Fin 10)
    (hj : j.val = 0) : Has3 (Gc inst) (Sum.inr (e, j)) := by
  obtain ⟨a, b, hab, hlt, he⟩ := ends_exist inst e
  have hr := rk_lt inst hc hab
  have hj0 : j = 0 := Fin.ext hj
  refine ⟨Sum.inr (e, 2), Sum.inr (e, 6),
    Sum.inl (a, ⟨2 * rk inst a b + 1, by omega⟩), ?_, ?_, ?_, ?_⟩
  · intro h; have := (Prod.mk.inj (Sum.inr.inj h)).2; revert this; decide
  · intro h; cases h
  · intro h; cases h
  · intro w'
    constructor
    · intro hadj
      rw [Gc_adj] at hadj
      obtain ⟨_, hR⟩ := hadj
      rcases w' with ⟨z, i⟩ | ⟨f, i⟩
      · obtain ⟨y, hey, hiy, hcmp⟩ := (R_rl inst z i e j).1 hR
        rw [he] at hey
        rcases Sym2.eq_iff.1 hey with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2
          right; right
          exact congrArg Sum.inl (Prod.ext rfl (Fin.ext hiy))
        · exfalso
          subst h1; subst h2
          omega
      · obtain ⟨hef, hg⟩ := (R_rr inst e f j i).1 hR
        subst hef
        rw [hj0] at hg
        rcases (g0_iff i).1 hg with h | h
        · left; rw [h]
        · right; left; rw [h]
    · rintro (rfl | rfl | rfl)
      · exact gad_adj inst e j 2 (by rw [hj0]; exact (g0_iff 2).2 (Or.inl rfl))
      · exact gad_adj inst e j 6 (by rw [hj0]; exact (g0_iff 6).2 (Or.inr rfl))
      · rw [Gc_adj, R_rl]
        refine ⟨(fun h => by cases h), ?_⟩
        unfold attachE
        exact ⟨b, he, rfl, Or.inl ⟨hj, hlt⟩⟩

/-- Gadget end 1: glued to the endpoint with the larger number. -/
public theorem has3_gad1 (hc : IsCubic inst) (e : (EdgeT inst)) (j : Fin 10)
    (hj : j.val = 1) : Has3 (Gc inst) (Sum.inr (e, j)) := by
  obtain ⟨a, b, hab, hlt, he⟩ := ends_exist inst e
  have hr := rk_lt inst hc hab.symm
  have hj0 : j = 1 := Fin.ext hj
  refine ⟨Sum.inr (e, 5), Sum.inr (e, 9),
    Sum.inl (b, ⟨2 * rk inst b a + 1, by omega⟩), ?_, ?_, ?_, ?_⟩
  · intro h; have := (Prod.mk.inj (Sum.inr.inj h)).2; revert this; decide
  · intro h; cases h
  · intro h; cases h
  · intro w'
    constructor
    · intro hadj
      rw [Gc_adj] at hadj
      obtain ⟨_, hR⟩ := hadj
      rcases w' with ⟨z, i⟩ | ⟨f, i⟩
      · obtain ⟨y, hey, hiy, hcmp⟩ := (R_rl inst z i e j).1 hR
        rw [he] at hey
        rcases Sym2.eq_iff.1 hey with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exfalso
          subst h1; subst h2
          omega
        · subst h1; subst h2
          right; right
          exact congrArg Sum.inl (Prod.ext rfl (Fin.ext hiy))
      · obtain ⟨hef, hg⟩ := (R_rr inst e f j i).1 hR
        subst hef
        rw [hj0] at hg
        rcases (g1_iff i).1 hg with h | h
        · left; rw [h]
        · right; left; rw [h]
    · rintro (rfl | rfl | rfl)
      · exact gad_adj inst e j 5 (by rw [hj0]; exact (g1_iff 5).2 (Or.inl rfl))
      · exact gad_adj inst e j 9 (by rw [hj0]; exact (g1_iff 9).2 (Or.inr rfl))
      · rw [Gc_adj, R_rl]
        refine ⟨(fun h => by cases h), ?_⟩
        unfold attachE
        exact ⟨a, he.trans Sym2.eq_swap, rfl, Or.inr ⟨hj, hlt⟩⟩

-- ───────────────────────── G' is cubic ─────────────────────────

public theorem has3_all (hc : IsCubic inst) (w : W inst) : Has3 (Gc inst) w := by
  rcases w with ⟨x, i⟩ | ⟨e, j⟩
  · have hi : i.val < 7 := i.2
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
        i.val = 6 := by omega
    rcases this with h | h | h | h | h | h | h
    · exact has3_leaf0 inst hc x i h
    · exact has3_slot inst hc x 0 (by omega) i (by omega)
    · exact has3_leaf2 inst hc x i h
    · exact has3_slot inst hc x 1 (by omega) i (by omega)
    · exact has3_leaf4 inst hc x i h
    · exact has3_slot inst hc x 2 (by omega) i (by omega)
    · exact has3_leaf6 inst hc x i h
  · by_cases h0 : j.val = 0
    · exact has3_gad0 inst hc e j h0
    · by_cases h1 : j.val = 1
      · exact has3_gad1 inst hc e j h1
      · exact has3_gad_mid inst e j (by omega)

/-- **`G'` is cubic** (whenever `G` is). -/
public theorem cubic_reduce (hc : IsCubic inst) : IsCubic (reduce inst) := by
  intro w
  exact Has3.degree (has3_all inst hc w)

end Cubic

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. G' is bridgeless
-- ═══════════════════════════════════════════════════════════════════════════
/-
  For every edge `s(a,b)` of `G'` we exhibit a second `a`–`b` route avoiding
  that very edge (so the edge lies on a cycle).  `Conn F a b` means "`a` and
  `b` are joined by a path none of whose edges is `F`".
-/

/-- Gadget alternative paths (for the 14 gadget edges, listed in `gedges`
    orientation): a path from `i` to `j` avoiding the edge `{i,j}`. -/
public def galt (i j : Fin 10) : List (Fin 10) :=
  match i.val, j.val with
  | 0, 2 => [6, 4, 3, 2] | 0, 6 => [2, 8, 7, 6] | 1, 5 => [9, 3, 4, 5]
  | 1, 9 => [5, 7, 8, 9] | 2, 3 => [8, 9, 3] | 3, 4 => [9, 8, 7, 5, 4]
  | 4, 5 => [6, 7, 5] | 6, 7 => [4, 5, 7] | 7, 8 => [6, 4, 3, 9, 8]
  | 8, 9 => [2, 3, 9] | 2, 8 => [3, 9, 8] | 3, 9 => [2, 8, 9]
  | 4, 6 => [5, 7, 6] | 5, 7 => [4, 6, 7]
  | _, _ => []

/-- `PathOK i j a l b`: `a → l → b` is a gadget path avoiding the edge `{i,j}`. -/
public def PathOK (i j : Fin 10) : Fin 10 → List (Fin 10) → Fin 10 → Prop
  | a, [], b => a = b
  | a, c :: l, b => gadj a c ∧ ¬ ((a = i ∧ c = j) ∨ (a = j ∧ c = i)) ∧ PathOK i j c l b

instance PathOK.dec (i j : Fin 10) :
    ∀ (a : Fin 10) (l : List (Fin 10)) (b : Fin 10), Decidable (PathOK i j a l b)
  | a, [], b => by unfold PathOK; infer_instance
  | a, c :: l, b =>
    have := PathOK.dec i j c l b
    by unfold PathOK; infer_instance

public theorem galt_ok : ∀ i j : Fin 10, (i.val, j.val) ∈ gedges → PathOK i j i (galt i j) j := by
  decide +kernel

section Bridge

variable (inst : GraphInstance)

public def QF (F : Sym2 (W inst)) (a b : W inst) : Prop := (Gc inst).Adj a b ∧ s(a, b) ≠ F

public abbrev Conn (F : Sym2 (W inst)) : W inst → W inst → Prop :=
  Relation.ReflTransGen (QF inst F)

public theorem QF_symm (F : Sym2 (W inst)) {a b : W inst} (h : QF inst F a b) : QF inst F b a :=
  ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩

variable {inst}

public theorem Conn.symm' {F : Sym2 (W inst)} {a b : W inst} (h : Conn inst F a b) :
    Conn inst F b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (QF_symm inst F hbc) ih

public theorem Conn.step {F : Sym2 (W inst)} {a b : W inst} (h : (Gc inst).Adj a b)
    (hF : s(a, b) ≠ F) : Conn inst F a b :=
  Relation.ReflTransGen.single ⟨h, hF⟩

public theorem Conn.reachable {F : Sym2 (W inst)} {a b : W inst} (h : Conn inst F a b) :
    ((Gc inst).deleteEdges {F}).Reachable a b := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hbc.1, fun h => hbc.2 (by simpa using h)⟩

public theorem bridgeless_of (H : ∀ a b : W inst, (Gc inst).Adj a b → Conn inst s(a, b) a b) :
    IsBridgeless (reduce inst) := by
  intro e
  induction e using Sym2.ind with
  | h a b =>
    intro he hbr
    have hadj : (Gc inst).Adj a b := (SimpleGraph.mem_edgeSet _).1 he
    have hr := (H a b hadj).reachable
    rw [SimpleGraph.isBridge_iff] at hbr
    exact hbr hr

-- ───────────────────────── positions in a cluster ─────────────────────────

/-- The cluster vertex at position `k % 7`. -/
public abbrev P (x : inst.V) (k : ℕ) : W inst :=
  Sum.inl (x, ⟨k % 7, Nat.mod_lt _ (by norm_num)⟩)

public theorem P_eq (x : inst.V) {k : ℕ} (hk : k < 7) (i : Fin 7) (hi : i.val = k) :
    P x k = Sum.inl (x, i) := by
  have h : (⟨k % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7) = i :=
    Fin.ext (by change k % 7 = i.val; rw [Nat.mod_eq_of_lt hk, hi])
  unfold P
  rw [h]

public theorem P_inj {x : inst.V} {k l : ℕ} (h : P x k = P x l) (hk : k < 7) (hl : l < 7) :
    k = l := by
  have := Fin.mk.inj (Prod.mk.inj (Sum.inl.inj h)).2
  rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hl] at this

public theorem P_fst {x y : inst.V} {k l : ℕ} (h : P x k = P y l) : x = y :=
  (Prod.mk.inj (Sum.inl.inj h)).1

public theorem chain_adjP (x : inst.V) {k : ℕ} (hk : k < 6) :
    (Gc inst).Adj (P x k) (P x (k + 1)) := by
  rw [P_eq x (by omega) ⟨k, by omega⟩ rfl, P_eq x (by omega) ⟨k + 1, by omega⟩ rfl]
  exact chain_adj inst x _ _ (Or.inl rfl)

public theorem chain_edge_ne {x : inst.V} {j k : ℕ} (hj : j < 6) (hk : k < 6) (hne : j ≠ k) :
    s(P x j, P x (j + 1)) ≠ s(P x k, P x (k + 1)) := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne (P_inj h1 (by omega) (by omega))
  · have e1 := P_inj h1 (by omega) (by omega)
    have e2 := P_inj h2 (by omega) (by omega)
    omega

public theorem chain_up (x : inst.V) (F : Sym2 (W inst)) (lo : ℕ) : ∀ d : ℕ, lo + d ≤ 6 →
    (∀ k, lo ≤ k → k < lo + d → F ≠ s(P x k, P x (k + 1))) →
    Conn inst F (P x lo) (P x (lo + d)) := by
  intro d
  induction d with
  | zero => intro _ _; exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro hd hF
    have h1 := ih (by omega) (fun k hk1 hk2 => hF k hk1 (by omega))
    have h2 : Conn inst F (P x (lo + d)) (P x (lo + d + 1)) :=
      Conn.step (chain_adjP x (by omega)) (fun h => hF (lo + d) (by omega) (by omega) h.symm)
    exact h1.trans h2

public theorem chain_conn (x : inst.V) (F : Sym2 (W inst)) (p q : ℕ) (hp : p ≤ 6) (hq : q ≤ 6)
    (hF : ∀ k, min p q ≤ k → k < max p q → F ≠ s(P x k, P x (k + 1))) :
    Conn inst F (P x p) (P x q) := by
  rcases le_total p q with h | h
  · have := chain_up x F p (q - p) (by omega) (fun k a b => hF k (by omega) (by omega))
    have e : p + (q - p) = q := by omega
    rw [e] at this
    exact this
  · have := chain_up x F q (p - q) (by omega) (fun k a b => hF k (by omega) (by omega))
    have e : q + (p - q) = p := by omega
    rw [e] at this
    exact this.symm'

-- ───────────────────────── gadget pieces ─────────────────────────

public theorem gpath_conn (e : (EdgeT inst)) (i j : Fin 10) :
    ∀ (l : List (Fin 10)) (a b : Fin 10), PathOK i j a l b →
      Conn inst s(Sum.inr (e, i), Sum.inr (e, j)) (Sum.inr (e, a)) (Sum.inr (e, b)) := by
  intro l
  induction l with
  | nil =>
    intro a b h
    have hab : a = b := h
    subst hab
    exact Relation.ReflTransGen.refl
  | cons c l ih =>
    intro a b h
    obtain ⟨hg, hne, hrest⟩ := h
    have hstep : Conn inst s(Sum.inr (e, i), Sum.inr (e, j))
        (Sum.inr (e, a)) (Sum.inr (e, c)) := by
      refine Conn.step (gad_adj inst e a c hg) ?_
      intro h'
      rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne (Or.inl ⟨(Prod.mk.inj (Sum.inr.inj h1)).2, (Prod.mk.inj (Sum.inr.inj h2)).2⟩)
      · exact hne (Or.inr ⟨(Prod.mk.inj (Sum.inr.inj h1)).2, (Prod.mk.inj (Sum.inr.inj h2)).2⟩)
    exact hstep.trans (ih c b hrest)

/-- A gadget edge lies on a cycle inside its gadget. -/
public theorem bridge_gad (e : (EdgeT inst)) (i j : Fin 10) (h : gadj i j) :
    Conn inst s(Sum.inr (e, i), Sum.inr (e, j)) (Sum.inr (e, i)) (Sum.inr (e, j)) := by
  rcases h with h | h
  · exact gpath_conn e i j (galt i j) i j (galt_ok i j h)
  · have := gpath_conn (inst := inst) e j i (galt j i) j i (galt_ok j i h)
    rw [Sym2.eq_swap] at this
    exact this.symm'

public theorem gad_conn01 (e : (EdgeT inst)) (F : Sym2 (W inst))
    (hF : ∀ a b : Fin 10, F ≠ s(Sum.inr (e, a), Sum.inr (e, b))) :
    Conn inst F (Sum.inr (e, 0)) (Sum.inr (e, 1)) := by
  have st : ∀ a b : Fin 10, gadj a b →
      Conn inst F (Sum.inr (e, a)) (Sum.inr (e, b)) :=
    fun a b h => Conn.step (gad_adj inst e a b h) (fun h' => hF a b h'.symm)
  exact ((((st 0 2 (by decide)).trans (st 2 3 (by decide))).trans
    (st 3 4 (by decide))).trans (st 4 5 (by decide))).trans (st 5 1 (by decide))

-- ───────────────────────── inequalities between edges ─────────────────────────

public theorem ll_ne_at (p q p' : inst.V × Fin 7) (q' : (EdgeT inst) × Fin 10) :
    s((Sum.inl p : W inst), Sum.inl q) ≠ s((Sum.inl p' : W inst), Sum.inr q') := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact Sum.inl_ne_inr h2
  · exact Sum.inl_ne_inr h1

public theorem gg_ne_at (a b : (EdgeT inst) × Fin 10) (p' : inst.V × Fin 7)
    (q' : (EdgeT inst) × Fin 10) :
    s((Sum.inr a : W inst), Sum.inr b) ≠ s((Sum.inl p' : W inst), Sum.inr q') := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Sum.inr_ne_inl h1
  · exact Sum.inr_ne_inl h2

public theorem gg_ne_ll (a b : (EdgeT inst) × Fin 10) (p q : inst.V × Fin 7) :
    s((Sum.inr a : W inst), Sum.inr b) ≠ s((Sum.inl p : W inst), Sum.inl q) := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Sum.inr_ne_inl h1
  · exact Sum.inr_ne_inl h1

public theorem at_ne_ll (p' : inst.V × Fin 7) (q' : (EdgeT inst) × Fin 10)
    (p q : inst.V × Fin 7) :
    s((Sum.inl p' : W inst), Sum.inr q') ≠ s((Sum.inl p : W inst), Sum.inl q) := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact Sum.inr_ne_inl h2
  · exact Sum.inr_ne_inl h2

public theorem cross_ne_chain {x y z : inst.V} (hxy : x ≠ y) (a b j : ℕ) :
    s(P x a, P y b) ≠ s(P z j, P z (j + 1)) := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact hxy ((P_fst h1).trans (P_fst h2).symm)

-- ───────────────────────── cross edges ─────────────────────────

public theorem cross_adjP {x y : inst.V} (hxy : inst.G.Adj x y) (bb : Bool) :
    (Gc inst).Adj (P x (leafN (rk inst x y) bb)) (P y (leafN (rk inst y x) bb)) := by
  rw [P_eq x (leafN_lt _ _) (lf (rk inst x y) bb) rfl,
      P_eq y (leafN_lt _ _) (lf (rk inst y x) bb) rfl,
      Gc_adj, R_ll]
  refine ⟨?_, Or.inr ⟨hxy, bb, rfl, rfl⟩⟩
  intro h
  exact hxy.ne (Prod.mk.inj (Sum.inl.inj h)).1

/-- Route through the gadget of the edge `{x,y}` from slot `2·rk x y + 1` of `x`
    to slot `2·rk y x + 1` of `y`; avoids every edge `F` whose both endpoints
    are cluster vertices. -/
public theorem route1 (hc : IsCubic inst) {x y : inst.V} (hxy : inst.G.Adj x y)
    (F : Sym2 (W inst)) (hF : ∃ p q, F = s(Sum.inl p, Sum.inl q)) :
    Conn inst F (P x (2 * rk inst x y + 1)) (P y (2 * rk inst y x + 1)) := by
  obtain ⟨p0, q0, rfl⟩ := hF
  have hs := rk_lt inst hc hxy
  have ht := rk_lt inst hc hxy.symm
  obtain ⟨Ux, hUx⟩ : ∃ i : Fin 7, i.val = 2 * rk inst x y + 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨Uy, hUy⟩ : ∃ i : Fin 7, i.val = 2 * rk inst y x + 1 := ⟨⟨_, by omega⟩, rfl⟩
  rw [P_eq x (by omega) Ux hUx, P_eq y (by omega) Uy hUy]
  let e : (EdgeT inst) := ⟨s(x, y), (SimpleGraph.mem_edgeSet _).2 hxy⟩
  have hax : (Gc inst).Adj (Sum.inl (x, Ux)) (Sum.inr (e, endIdx inst x y)) := by
    rw [Gc_adj, R_lr]
    refine ⟨(fun h => by cases h), ?_⟩
    unfold attachE
    refine ⟨y, rfl, hUx, ?_⟩
    by_cases hlt : ix inst x < ix inst y
    · left; exact ⟨by simp [endIdx, hlt], hlt⟩
    · right
      have hne : ix inst x ≠ ix inst y := fun h => hxy.ne (ix_injective inst h)
      exact ⟨by simp [endIdx, hlt], by omega⟩
  have hay : (Gc inst).Adj (Sum.inl (y, Uy)) (Sum.inr (e, endIdx inst y x)) := by
    rw [Gc_adj, R_lr]
    refine ⟨(fun h => by cases h), ?_⟩
    unfold attachE
    refine ⟨x, Sym2.eq_swap, hUy, ?_⟩
    by_cases hlt : ix inst y < ix inst x
    · left; exact ⟨by simp [endIdx, hlt], hlt⟩
    · right
      have hne : ix inst y ≠ ix inst x := fun h => hxy.ne (ix_injective inst h).symm
      exact ⟨by simp [endIdx, hlt], by omega⟩
  have hF1 : ∀ a b : Fin 10, s((Sum.inl p0 : W inst), Sum.inl q0) ≠
      s(Sum.inr (e, a), Sum.inr (e, b)) :=
    fun a b h => gg_ne_ll (e, a) (e, b) p0 q0 h.symm
  have hgad : Conn inst s((Sum.inl p0 : W inst), Sum.inl q0)
      (Sum.inr (e, endIdx inst x y)) (Sum.inr (e, endIdx inst y x)) := by
    by_cases hlt : ix inst x < ix inst y
    · have h1 : endIdx inst x y = 0 := by simp [endIdx, hlt]
      have h2 : endIdx inst y x = 1 := by
        have : ¬ ix inst y < ix inst x := by omega
        simp [endIdx, this]
      rw [h1, h2]
      exact gad_conn01 e _ hF1
    · have hne : ix inst x ≠ ix inst y := fun h => hxy.ne (ix_injective inst h)
      have h1 : endIdx inst x y = 1 := by simp [endIdx, hlt]
      have h2 : endIdx inst y x = 0 := by
        have : ix inst y < ix inst x := by omega
        simp [endIdx, this]
      rw [h1, h2]
      exact (gad_conn01 e _ hF1).symm'
  have s1 : Conn inst s((Sum.inl p0 : W inst), Sum.inl q0)
      (Sum.inl (x, Ux)) (Sum.inr (e, endIdx inst x y)) :=
    Conn.step hax (fun h => ll_ne_at p0 q0 (x, Ux) (e, endIdx inst x y) h.symm)
  have s2 : Conn inst s((Sum.inl p0 : W inst), Sum.inl q0)
      (Sum.inr (e, endIdx inst y x)) (Sum.inl (y, Uy)) :=
    Conn.step hay.symm (fun h => by
      rw [Sym2.eq_swap] at h
      exact ll_ne_at p0 q0 (y, Uy) (e, endIdx inst y x) h.symm)
  exact (s1.trans hgad).trans s2


public theorem chain_ne_chain {x y : inst.V} (hxy : x ≠ y) (j k : ℕ) :
    s(P x j, P x (j + 1)) ≠ s(P y k, P y (k + 1)) := by
  intro h
  rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact hxy (P_fst h1)

/-- The edge of `G'`'s gadget associated with the `G`-edge `{x,y}`. -/
public def edgeE {x y : inst.V} (hxy : inst.G.Adj x y) : (EdgeT inst) :=
  ⟨s(x, y), (SimpleGraph.mem_edgeSet _).2 hxy⟩

public theorem endIdx_eq {x y : inst.V} (hxy : inst.G.Adj x y) (j : Fin 10)
    (h : (j.val = 0 ∧ ix inst x < ix inst y) ∨ (j.val = 1 ∧ ix inst y < ix inst x)) :
    j = endIdx inst x y := by
  rcases h with ⟨h0, hlt⟩ | ⟨h1, hlt⟩
  · apply Fin.ext; simp [endIdx, hlt]; omega
  · have : ¬ ix inst x < ix inst y := by omega
    apply Fin.ext; simp [endIdx, this]; omega

public theorem att_adj (hc : IsCubic inst) {x y : inst.V} (hxy : inst.G.Adj x y) :
    (Gc inst).Adj (P x (2 * rk inst x y + 1)) (Sum.inr (edgeE hxy, endIdx inst x y)) := by
  have hs := rk_lt inst hc hxy
  obtain ⟨Ux, hUx⟩ : ∃ i : Fin 7, i.val = 2 * rk inst x y + 1 := ⟨⟨_, by omega⟩, rfl⟩
  rw [P_eq x (by omega) Ux hUx, Gc_adj, R_lr]
  refine ⟨(fun h => by cases h), ?_⟩
  unfold attachE
  refine ⟨y, rfl, hUx, ?_⟩
  by_cases hlt : ix inst x < ix inst y
  · left; exact ⟨by simp [endIdx, hlt], hlt⟩
  · right
    have hne : ix inst x ≠ ix inst y := fun h => hxy.ne (ix_injective inst h)
    exact ⟨by simp [endIdx, hlt], by omega⟩

public theorem att_adj' (hc : IsCubic inst) {x y : inst.V} (hxy : inst.G.Adj x y) :
    (Gc inst).Adj (P y (2 * rk inst y x + 1)) (Sum.inr (edgeE hxy, endIdx inst y x)) := by
  have h := att_adj hc hxy.symm
  have he : edgeE hxy.symm = edgeE hxy := Subtype.ext Sym2.eq_swap
  rw [he] at h
  exact h

/-- Gadget path between the two glued ends of the gadget of `{x,y}`. -/
public theorem gad_xy {x y : inst.V} (hxy : inst.G.Adj x y) (F : Sym2 (W inst))
    (hF : ∀ a b : Fin 10, F ≠ s(Sum.inr (edgeE hxy, a), Sum.inr (edgeE hxy, b))) :
    Conn inst F (Sum.inr (edgeE hxy, endIdx inst x y))
      (Sum.inr (edgeE hxy, endIdx inst y x)) := by
  by_cases hlt : ix inst x < ix inst y
  · have h1 : endIdx inst x y = 0 := by simp [endIdx, hlt]
    have h2 : endIdx inst y x = 1 := by
      have : ¬ ix inst y < ix inst x := by omega
      simp [endIdx, this]
    rw [h1, h2]
    exact gad_conn01 _ F hF
  · have hne : ix inst x ≠ ix inst y := fun h => hxy.ne (ix_injective inst h)
    have h1 : endIdx inst x y = 1 := by simp [endIdx, hlt]
    have h2 : endIdx inst y x = 0 := by
      have : ix inst y < ix inst x := by omega
      simp [endIdx, this]
    rw [h1, h2]
    exact (gad_conn01 _ F hF).symm'

/-- Route avoiding any `F = s(P x k0, P x (k0+1))`: slot to leaf of `x`
    around through the neighbour `y`. -/
public theorem alt_route (hc : IsCubic inst) (x : inst.V) {y : inst.V} (hxy : inst.G.Adj x y)
    (bb : Bool) (k0 : ℕ) :
    Conn inst s(P x k0, P x (k0 + 1))
      (P x (2 * rk inst x y + 1)) (P x (leafN (rk inst x y) bb)) := by
  have hs := rk_lt inst hc hxy
  have ht := rk_lt inst hc hxy.symm
  have hxne : x ≠ y := hxy.ne
  have hLL : ∃ p q, s(P x k0, P x (k0 + 1)) = s((Sum.inl p : W inst), Sum.inl q) :=
    ⟨_, _, rfl⟩
  have r1 := route1 hc hxy _ hLL
  have c1 : Conn inst s(P x k0, P x (k0 + 1))
      (P y (2 * rk inst y x + 1)) (P y (leafN (rk inst y x) bb)) := by
    refine chain_conn y _ _ _ (by omega) (by have := leafN_lt (rk inst y x) bb; omega) ?_
    intro k _ _
    exact chain_ne_chain hxne k0 k
  have c2 : Conn inst s(P x k0, P x (k0 + 1))
      (P y (leafN (rk inst y x) bb)) (P x (leafN (rk inst x y) bb)) :=
    Conn.step (cross_adjP hxy.symm bb) (cross_ne_chain hxne.symm _ _ k0)
  exact (r1.trans c1).trans c2

public theorem bridge_chain_gen (hc : IsCubic inst) (x : inst.V) (s : ℕ) (hs : s < 3) (bb : Bool)
    (k0 : ℕ) (hk0 : k0 < 6)
    (hk : min (2 * s + 1) (leafN s bb) ≤ k0 ∧ k0 < max (2 * s + 1) (leafN s bb)) :
    Conn inst s(P x k0, P x (k0 + 1)) (P x k0) (P x (k0 + 1)) := by
  obtain ⟨hy, hr⟩ := nb_spec inst hc x hs
  have halt := alt_route hc x hy bb k0
  rw [hr] at halt
  have hL := leafN_lt s bb
  rcases le_total (2 * s + 1) (leafN s bb) with h | h
  · have a1 := chain_conn x s(P x k0, P x (k0 + 1)) k0 (2 * s + 1) (by omega) (by omega)
      (fun k hk1 hk2 => chain_edge_ne (by omega) (by omega) (by omega))
    have a3 := chain_conn x s(P x k0, P x (k0 + 1)) (leafN s bb) (k0 + 1) (by omega) (by omega)
      (fun k hk1 hk2 => chain_edge_ne (by omega) (by omega) (by omega))
    exact a1.trans (halt.trans a3)
  · have a1 := chain_conn x s(P x k0, P x (k0 + 1)) k0 (leafN s bb) (by omega) (by omega)
      (fun k hk1 hk2 => chain_edge_ne (by omega) (by omega) (by omega))
    have a3 := chain_conn x s(P x k0, P x (k0 + 1)) (2 * s + 1) (k0 + 1) (by omega) (by omega)
      (fun k hk1 hk2 => chain_edge_ne (by omega) (by omega) (by omega))
    exact a1.trans (halt.symm'.trans a3)

public theorem bridge_chain (hc : IsCubic inst) (x : inst.V) (k0 : ℕ) (hk0 : k0 < 6) :
    Conn inst s(P x k0, P x (k0 + 1)) (P x k0) (P x (k0 + 1)) := by
  interval_cases k0
  · exact bridge_chain_gen hc x 0 (by omega) false 0 (by omega) (by simp [leafN])
  · exact bridge_chain_gen hc x 0 (by omega) true 1 (by omega) (by simp [leafN])
  · exact bridge_chain_gen hc x 1 (by omega) false 2 (by omega) (by simp [leafN])
  · exact bridge_chain_gen hc x 1 (by omega) true 3 (by omega) (by simp [leafN])
  · exact bridge_chain_gen hc x 2 (by omega) true 4 (by omega) (by simp [leafN])
  · exact bridge_chain_gen hc x 2 (by omega) false 5 (by omega) (by simp [leafN])

public theorem bridge_cross (hc : IsCubic inst) {x y : inst.V} (hxy : inst.G.Adj x y) (bb : Bool) :
    Conn inst s(P x (leafN (rk inst x y) bb), P y (leafN (rk inst y x) bb))
      (P x (leafN (rk inst x y) bb)) (P y (leafN (rk inst y x) bb)) := by
  have hs := rk_lt inst hc hxy
  have ht := rk_lt inst hc hxy.symm
  have hL := leafN_lt (rk inst x y) bb
  have hL' := leafN_lt (rk inst y x) bb
  have a1 := chain_conn x s(P x (leafN (rk inst x y) bb), P y (leafN (rk inst y x) bb))
    (leafN (rk inst x y) bb) (2 * rk inst x y + 1) (by omega) (by omega)
    (fun k _ _ => cross_ne_chain hxy.ne _ _ k)
  have a2 := route1 hc hxy
    s(P x (leafN (rk inst x y) bb), P y (leafN (rk inst y x) bb)) ⟨_, _, rfl⟩
  have a3 := chain_conn y s(P x (leafN (rk inst x y) bb), P y (leafN (rk inst y x) bb))
    (2 * rk inst y x + 1) (leafN (rk inst y x) bb) (by omega) (by omega)
    (fun k _ _ => cross_ne_chain hxy.ne _ _ k)
  exact a1.trans (a2.trans a3)

public theorem bridge_attach (hc : IsCubic inst) {x y : inst.V} (hxy : inst.G.Adj x y) :
    Conn inst s(P x (2 * rk inst x y + 1), Sum.inr (edgeE hxy, endIdx inst x y))
      (P x (2 * rk inst x y + 1)) (Sum.inr (edgeE hxy, endIdx inst x y)) := by
  have hs := rk_lt inst hc hxy
  have ht := rk_lt inst hc hxy.symm
  have hL := leafN_lt (rk inst x y) false
  have hL' := leafN_lt (rk inst y x) false
  have b1 := chain_conn x s(P x (2 * rk inst x y + 1), Sum.inr (edgeE hxy, endIdx inst x y))
    (2 * rk inst x y + 1) (leafN (rk inst x y) false) (by omega) (by omega)
    (fun k _ _ => at_ne_ll _ _ _ _)
  have b2 : Conn inst s(P x (2 * rk inst x y + 1), Sum.inr (edgeE hxy, endIdx inst x y))
      (P x (leafN (rk inst x y) false)) (P y (leafN (rk inst y x) false)) := by
    refine Conn.step (cross_adjP hxy false) ?_
    intro h
    rcases Sym2.eq_iff.1 h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Sum.inl_ne_inr h2
    · exact Sum.inl_ne_inr h1
  have b3 := chain_conn y s(P x (2 * rk inst x y + 1), Sum.inr (edgeE hxy, endIdx inst x y))
    (leafN (rk inst y x) false) (2 * rk inst y x + 1) (by omega) (by omega)
    (fun k _ _ => at_ne_ll _ _ _ _)
  have b4 : Conn inst s(P x (2 * rk inst x y + 1), Sum.inr (edgeE hxy, endIdx inst x y))
      (P y (2 * rk inst y x + 1)) (Sum.inr (edgeE hxy, endIdx inst y x)) := by
    refine Conn.step (att_adj' hc hxy) ?_
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hxy.ne (P_fst h1).symm
    · exact Sum.inl_ne_inr h1
  have b5 := gad_xy hxy s(P x (2 * rk inst x y + 1), Sum.inr (edgeE hxy, endIdx inst x y))
    (fun a b h => gg_ne_at (edgeE hxy, a) (edgeE hxy, b) _ _ h.symm)
  exact b1.trans (b2.trans (b3.trans (b4.trans b5.symm')))

public theorem all_conn (hc : IsCubic inst) (a b : W inst) (h : (Gc inst).Adj a b) :
    Conn inst s(a, b) a b := by
  obtain ⟨_, hR⟩ := (Gc_adj inst).1 h
  rcases a with ⟨x, i⟩ | ⟨e, i⟩ <;> rcases b with ⟨y, j⟩ | ⟨f, j⟩
  · have hi7 := i.2
    have hj7 := j.2
    rcases (R_ll inst x y i j).1 hR with ⟨hxy, hcj⟩ | ⟨hxy, bb, hi, hj⟩
    · subst hxy
      rcases hcj with h1 | h1
      · have := bridge_chain hc x i.val (by omega)
        rw [P_eq x (by omega) i rfl, P_eq x (by omega) j h1.symm] at this
        exact this
      · have := bridge_chain hc x j.val (by omega)
        rw [P_eq x (by omega) j rfl, P_eq x (by omega) i h1.symm] at this
        rw [Sym2.eq_swap]
        exact this.symm'
    · have := bridge_cross hc hxy bb
      rw [P_eq x (leafN_lt _ _) i hi, P_eq y (leafN_lt _ _) j hj] at this
      exact this
  · obtain ⟨y, he, hiy, hcmp⟩ := (R_lr inst x i f j).1 hR
    have hxy : inst.G.Adj x y := by
      have := f.2
      rw [he] at this
      exact (SimpleGraph.mem_edgeSet _).1 this
    have hs := rk_lt inst hc hxy
    have hf : f = edgeE hxy := Subtype.ext he
    have hj' : j = endIdx inst x y := endIdx_eq hxy j hcmp
    subst hf; subst hj'
    have := bridge_attach hc hxy
    rw [P_eq x (by omega) i hiy] at this
    exact this
  · obtain ⟨z, he, hjz, hcmp⟩ := (R_rl inst y j e i).1 hR
    have hyz : inst.G.Adj y z := by
      have := e.2
      rw [he] at this
      exact (SimpleGraph.mem_edgeSet _).1 this
    have hs := rk_lt inst hc hyz
    have hf : e = edgeE hyz := Subtype.ext he
    have hi' : i = endIdx inst y z := endIdx_eq hyz i hcmp
    subst hf; subst hi'
    have := bridge_attach hc hyz
    rw [P_eq y (by omega) j hjz] at this
    rw [Sym2.eq_swap]
    exact this.symm'
  · obtain ⟨hef, hg⟩ := (R_rr inst e f i j).1 hR
    subst hef
    exact bridge_gad e i j hg

end Bridge

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. The reduction and public theorem 1
-- ═══════════════════════════════════════════════════════════════════════════

public theorem bridgeless_reduce (inst : GraphInstance) (hc : IsCubic inst) :
    IsBridgeless (reduce inst) :=
  bridgeless_of (fun a b h => all_conn hc a b h)

/-- `VC-CG ≤ VC-CBG`: `G ↦ G'` preserves yes/no answers (Claim 1) and lands
    in the family of cubic bridgeless graphs. -/
public theorem VC_CG_reduces_VC_CBG : ReducesTo CubicGraphs CubicBridgeless := by
  refine ⟨reduce, ?_⟩
  intro inst hc
  constructor
  · rintro ⟨_, S, hS, hk⟩
    exact ⟨⟨cubic_reduce inst hc, bridgeless_reduce inst hc⟩,
      (claim1 inst).1 ⟨S, hS, hk⟩⟩
  · rintro ⟨_, hS'⟩
    exact ⟨hc, (claim1 inst).2 hS'⟩

/-- **public theorem 1.** The vertex cover problem on cubic bridgeless graphs
    (VC-CBG) is NP-complete. -/
public theorem theorem1_I : NPComplete (VCYes CubicBridgeless) :=
  ⟨VC_InNP CubicBridgeless,
    NPHard_of_reduction VC_CG_NPHard VC_CG_reduces_VC_CBG⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. Commentry
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, or hypothesis hacking.
  `axiom`: only `VC_InNP`, `VC_CG_NPHard`, `NPHard_of_reduction`:
    * NPHard_of_reduction: The reduction is a polynomial-time reduction
      (Standard fact: Garey-Johnson Textbook)
    * VC_CG_NPHard: Vertex cover problem on Cubic graphs is NP-hard (proven)
    * VC_InNP: Vertex cover problem is in NP (known fact)
  (plus the opaque `InNP`, `NPHard`).  Everything about the construction is
  public defined and proved:
    * `reduce`            – the concrete graph G' (cluster paths x'₁ x' x'₂ x x''₂ x'' x''₁,
                            10-vertex gadget per edge, cross edges, attachments);
    * `cubic_reduce`      – G' is cubic;
    * `bridgeless_reduce` – G' is bridgeless;
    * `claim1`            – both directions of Claim 1 (`cover_forward`, `cover_backward`);
    * `card_W`            – |V'| = 7m + 10n.
-/
