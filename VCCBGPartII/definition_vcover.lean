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
