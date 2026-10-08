module
public import Mathlib
/-! we define vertex cover and minimum vertex cover. -/
/-- `VCover G S`: every edge of G has at least one endpoint in S.
    Only common thread between proof of Np-completeness and polynomial time. -/
public abbrev VCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ S ∨ v ∈ S

/-- `MinVCover G S`: S is a vertex cover of minimum cardinality. -/
public abbrev MinVCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  VCover G S ∧ ∀ T : Finset V, VCover G T → S.card ≤ T.card

/-- **VC − CBG, "Yes instance."** `G` together with a bound `k` is a Yes
    instance of the vertex-cover decision problem iff `G` has a vertex
    cover of size at most `k`. -/
public abbrev YesInstance (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, VCover G S ∧ S.card ≤ k


-- ═══════════════════════════════════════════════════════════════════════════
-- definitions for NP-completeness proofs
-- ═══════════════════════════════════════════════════════════════════════════

/-- A single instance of a vertex-cover decision problem: a finite simple
    graph on some (existentially bundled) vertex type, together with a
    bound `k`. `GraphInstance : Type 1` (it bundles a `Type` field). -/
public structure GraphInstance where
  V : Type
  fV : Fintype V
  dV : DecidableEq V
  G : SimpleGraph V
  dAdj : DecidableRel G.Adj
  k : ℕ

attribute [instance] GraphInstance.fV GraphInstance.dV GraphInstance.dAdj

/-- **Cubic**, stated directly on a `GraphInstance` so its own bundled
    instances are automatically in scope. -/
public abbrev IsCubic (inst : GraphInstance) : Prop := ∀ v : inst.V, inst.G.degree v = 3

/-- **Bridgeless**. -/
public abbrev IsBridgeless (inst : GraphInstance) : Prop :=
  ∀ ⦃e : Sym2 inst.V⦄, e ∈ inst.G.edgeSet → ¬ inst.G.IsBridge e


/-- Membership in NP — left `opaque`. Universe-polymorphic in `Inst`'s
    own universe `u` only. -/
public opaque InNP {Inst : Type u} (Yes : Inst → Prop) : Prop

/-- **NP-hardness** — left `opaque` -/
public opaque NPHard {Inst : Type u} (Yes : Inst → Prop) : Prop

/-- **NP-completeness**: in NP, and NP-hard. -/
public abbrev NPComplete {Inst : Type u} (Yes : Inst → Prop) : Prop :=
  InNP Yes ∧ NPHard Yes

/-- The Yes-instances of "vertex cover, restricted to graphs satisfying
    the family predicate `P`". -/
public abbrev VCYes (P : GraphInstance → Prop) (inst : GraphInstance) : Prop :=
  P inst ∧ ∃ S : Finset inst.V, VCover inst.G S ∧ S.card ≤ inst.k

public abbrev CubicBridgeless (inst : GraphInstance) : Prop :=
  IsCubic inst ∧ IsBridgeless inst
