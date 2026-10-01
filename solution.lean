module

public import VCCBGMain

set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Proved solution — Theorem 1, Theorem 2, and Theorem 13

**Theorem 1** — "VC − CBG is NP-complete." — obtained from Theorem 11 by
   "proof by restriction" (`thm1.lean`).

**Theorem 2** — "VC − CBG is in P." — the paper's headline complexity-class
   result, obtained from Theorem 8 (Algorithm 1 is correct) together with
   Theorem 9 (Algorithm 1 runs in O(m^5) time).

**Theorem 13** — "Algorithm A returns Yes iff the given instance of VC − CBG
   is a Yes instance" — obtained from Lemma 9 and Lemma 10 (`thm13.lean`).

Unlike `challenge.lean` (which re-derives every definition from
Mathlib alone so that `Theorem*_wrapper`'s statement type-checks with no
outside help), this file imports the real, already-proved development
and discharges the identical statement by directly invoking the real
`Theorem1` (`thm1.lean`) / `Theorem2` (`thm2.lean`) / `Theorem13`
(`thm13.lean`) with the supplied arguments.
-/
open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] [Inhabited V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Goal accomplished: `Theorem1_wrapper` is literally `Theorem1`. -/
public theorem VCCBGSecB.Theorem1_wrapper
    (hNPbridgeless : InNP (VCYes CubicPlanarBridgeless)) :
    NPComplete (VCYes CubicBridgeless) :=
  Theorem1 hNPbridgeless

/-- Goal accomplished: `Theorem2_wrapper` is literally `Theorem2`. -/
public theorem VCCBGPartII.Theorem2_wrapper
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool)
    -- Theorem 8's own standing hypotheses (see thm8.lean §1 for
    -- what each one means; none of them mention k, so a single bundle
    -- serves every k below).
    (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (hrow_pair : ∀ ⦃u v : V⦄, (matchingSubgraph (G := G) M hMadj).Adj u v →
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = u ∨ rc.2 = u) =
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = v ∨ rc.2 = v))
    (htwo : TwoPerRow ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hedges : RowsAreEdges ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hrows_half :
      (RowsOf ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)).card
        = Fintype.card V / 2)
    (hmatchingEdges_card :
      ∀ k : ℕ, (Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)).length
        = Fintype.card V / 2)
    (hV_pos : 0 < Fintype.card V)
    (hRowsCoverAll : ∀ w : V,
      ∃ rc ∈ ({ RT0Of (G := G) adj0 Vs M with score := fun _ => negInf } : RTable G).rows.reverse,
        w = rc.1 ∨ w = rc.2)
    (hRemoveInv0 : RemoveInvariant
      (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).1.toTableState)
    (hFS0 : FrozenSet (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).1.toTableState
        = (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).2)
    (hNoAdjAll : ∀ (Rx : RTable G) (Sx lamx : Finset V) (w : V),
      NoAdjacentDoubleRemoval ((Fintype.card V) ^ 2) Rx Sx lamx w)
    (hphase_eq : PhaseMatchesAlgState ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)
      ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hSseq_step : ∀ n,
      (∃ _ : DiminishingHop ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)
              (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n), True) →
        (FrozenSet (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) (n + 1))).card
          < (FrozenSet (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n)).card)
    (hstationary : ∀ n,
      ¬ (∃ _ : DiminishingHop ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)
              (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n), True) →
        SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) (n + 1)
          = SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n) :
    InP G :=
  Theorem2 hcubic hbridgeless adj0 Vs M lt hMinv hMadj hrow_pair htwo hedges
    hrows_half hmatchingEdges_card hV_pos hRowsCoverAll hRemoveInv0 hFS0 hNoAdjAll
    hphase_eq hSseq_step hstationary

/-- Goal accomplished: `Theorem13_wrapper` is literally `Theorem13`. -/
public theorem VCCBGSecC.Theorem13_wrapper
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
    (S.card ≤ k → YesInstance G k) ∧ (YesInstance G k → AlgA_Yes G k) :=
  Theorem13 hcubic hbridgeless k hS₀ hOrder hlen hM hfp hSeq hSbound
