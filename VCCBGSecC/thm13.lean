/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module

public import VCCBGSecC.thm13_lemma9
public import VCCBGSecC.thm13_lemma10

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Theorem 13**: Algorithm A returns "Yes" if and only if the given instance of
    VC-CBG is a "Yes" instance, combining Lemma 9 (forward direction)
    and Lemma 10 (reverse direction). -/
public theorem Theorem13
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (k : ℕ)
    {S₀ S : Finset V} (hS₀ : VCover G S₀)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {M : Finset (Sym2 V)} (hM : IsPerfectMatching M)
    {n : ℕ} (hfp : FixedPointCover'' G S₀ nbrOrder hOrder M n)
    (hSeq : S = algB_run'' G nbrOrder hOrder (seedsOf M) n S₀)
    (hSbound : S.card ≤ Fintype.card V - 1) :
    (S.card ≤ k → YesInstance G k) ∧ (YesInstance G k → AlgA_Yes G k) := by
  constructor
  · -- (⇒) Lemma 10: Algorithm A returns Yes ⟹ Yes instance
    intro hSk
    have hMin : MinVCover G S :=
      Lemma10'' hcubic hbridgeless hS₀ hOrder hlen hM hfp hSeq hSbound
    exact ⟨S, hMin.1, hSk⟩
  · -- (⇐) Lemma 9: Yes instance ⟹ Algorithm A returns Yes
    intro hYes
    exact Lemma9 hcubic hbridgeless k hYes
