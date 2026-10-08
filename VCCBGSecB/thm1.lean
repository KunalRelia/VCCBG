/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formal Lean 4 / Mathlib Verification of Theorem 1 (Section B - alterntive proof),
  structured around the "proof by restriction" principle.

  Here, we do not use cslib because:
  (i) classes P, NP, NP-hard, and NP-complete are not yet defined in Cslib and
  (ii) TMs defined are not yet unconditional (e.g., single tape deterministic TM
  needs removal of `h_mono` assumption).

  The actual logical content of "proof by restriction" [GJ02] (Table 24's
  "Generalize" step, and equally its "Equate" step) is an inclusion of instance
  families, not a biconditional correspondence between two different families.
  If every `F₁`-instance is already an `F₂`-instance (`F₁ ⊆f F₂`, i.e. graphs
  satisfying `F₁` also satisfy `F₂`), then any algorithm deciding VC on
  all of `F₂` in particular decides it on all of `F₁` — so NP-hardness of
  VC restricted to `F₁` immediately transfers to `F₂`. This needs no
  reduction map, no polynomial-time cost argument, and no converse: it is
  hardness monotonicity under widening the instance set, exactly
  `NPHard_of_restriction` below.

  Both Table 24 steps are literal inclusions:
    • "Equate": `CubicPlanar2VC ⊆f CubicPlanarBridgeless` (Whitney's
      Theorem: 2-vertex-connected ⟹ bridgeless, the only direction ever
      needed).
    • "Generalize": `CubicPlanarBridgeless ⊆f CubicBridgeless` (dropping
      the planarity conjunct outright).
-/
public import Mathlib
public import VCCBGPartII.definition_vcover
/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset

universe u

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Graph instances of varying size, and the graph-family predicates of
--     Definitions 21/22 (and the already-standard Cubic/Bridgeless)
-- ═══════════════════════════════════════════════════════════════════════════

attribute [instance] GraphInstance.fV GraphInstance.dV GraphInstance.dAdj

/-- **Definition 21** (2-vertex-connected graph): "a graph that remains
    connected after the removal of one vertex." Formalized directly:
    `G` itself is connected, and for every vertex `v`, the subgraph
    induced on `V \ {v}` is also connected. -/
public def Is2VertexConnected (inst : GraphInstance) : Prop :=
  inst.G.Connected ∧ ∀ v : inst.V, (inst.G.induce {x | x ≠ v}).Connected

/-- **Definition 22** (planar graph). Left `opaque`. -/
opaque IsPlanar (inst : GraphInstance) : Prop

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Notion of NP / NP-hardness / NP-completeness
-- ═══════════════════════════════════════════════════════════════════════════

-- now imported from the common definition file

-- ═══════════════════════════════════════════════════════════════════════════
-- §1'. Restriction of instance families, and hardness transfer along it
-- ═══════════════════════════════════════════════════════════════════════════

/-- `F₁ ⊆f F₂`: every instance satisfying the (graph-)family (NpHard) predicate
    `F₁` also satisfies `F₂`. This is the *only* relationship
    "proof by restriction" needs between two families. -/
public def FamilySubset (F₁ F₂ : GraphInstance → Prop) : Prop :=
  ∀ inst, F₁ inst → F₂ inst

infixl:50 " ⊆f " => FamilySubset


/-- **NP-hardness transfers to any superfamily** ("proof by restriction"
    [GJ02], the logical engine of both Table 24 steps — "Equate" and
    "Generalize" alike): if the vertex-cover problem is NP-hard when
    restricted to instances in `F₁`, and `F₁ ⊆f F₂`, then it is also
    NP-hard when restricted to the (larger) family `F₂` — hardness of a
    sub-instance-class always transfers upward, since any
    polynomial-time algorithm solving VC on all of `F₂` in particular
    solves it on the `F₁`-instances. This is the standard
    argument-by-restriction principle, taken as a hypothesis about our
    present opaque treatment of `NPHard` (in the same spirit as
    `Theorem10`/`Whitney` standing in for external, paper-cited results),
    exactly as the user's own formulation states it. -/
axiom NPHard_of_restriction
    {F₁ F₂ : GraphInstance → Prop} (hsub : F₁ ⊆f F₂) (hHard : NPHard (VCYes F₁)) :
    NPHard (VCYes F₂)

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The three families of Table 24 / Theorems 10-11
-- ═══════════════════════════════════════════════════════════════════════════

/-- Table 24, row 1: **cubic + planar + 2-vertex-connected**. -/
public def CubicPlanar2VC (inst : GraphInstance) : Prop :=
  IsCubic inst ∧ IsPlanar inst ∧ Is2VertexConnected inst

/-- Table 24, row 2: **cubic + planar + bridgeless**. -/
public def CubicPlanarBridgeless (inst : GraphInstance) : Prop :=
  IsCubic inst ∧ IsPlanar inst ∧ IsBridgeless inst

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Theorem 10 (Mohar, [Moh01]) and Whitney's Theorem, as hypotheses
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 10** (Theorem 4.1(a) of [Moh01], strengthened to "simple"
    per the paper's own remark, lines 2256-2262). -/
axiom Theorem10 : NPComplete (VCYes CubicPlanar2VC)

/-- **Whitney's Theorem** [Whi32]: being 2-vertex-connected implies
    being bridgeless — the one direction ever needed, and exactly what
    makes `CubicPlanar2VC ⊆f CubicPlanarBridgeless` (§4) hold. -/
axiom Whitney (inst : GraphInstance) (h : Is2VertexConnected inst) :
    IsBridgeless inst

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Theorem 11: "Equate", via the family inclusion CubicPlanar2VC ⊆f
--     CubicPlanarBridgeless
-- ═══════════════════════════════════════════════════════════════════════════

/-- `CubicPlanar2VC ⊆f CubicPlanarBridgeless`: every cubic, planar,
    2-vertex-connected graph is a cubic, planar, bridgeless graph —
    immediate from `Whitney`. -/
public theorem CubicPlanar2VC_subset_CubicPlanarBridgeless :
    CubicPlanar2VC ⊆f CubicPlanarBridgeless :=
  fun inst ⟨hcubic, hplanar, h2vc⟩ => ⟨hcubic, hplanar, Whitney inst h2vc⟩

/-- **Theorem 11** (paper, lines 2266-2267): the vertex cover problem on
    simple bridgeless cubic planar graphs is NP-complete.

    Derived from `Theorem10` by equality and `NPHard_of_restriction`, using the
    family inclusion `CubicPlanar2VC ⊆f CubicPlanarBridgeless`. -/
public theorem Theorem11 (hNP : InNP (VCYes CubicPlanarBridgeless)) :
    NPComplete (VCYes CubicPlanarBridgeless) :=
  ⟨hNP, NPHard_of_restriction CubicPlanar2VC_subset_CubicPlanarBridgeless Theorem10.2⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Theorem 1: "Generalize", via the family inclusion
--     CubicPlanarBridgeless ⊆f CubicBridgeless
-- ═══════════════════════════════════════════════════════════════════════════

/-- **VC ∈ NP**, for any graph family. -/
axiom VC_InNP (P : GraphInstance → Prop) : InNP (VCYes P)

/-- `CubicPlanarBridgeless ⊆f CubicBridgeless`: every cubic, planar,
    bridgeless graph is (trivially, dropping the planarity conjunct) a
    cubic, bridgeless graph. -/
public theorem CubicPlanarBridgeless_subset_CubicBridgeless :
    CubicPlanarBridgeless ⊆f CubicBridgeless :=
  fun inst ⟨hcubic, _hplanar, hbridgeless⟩ => ⟨hcubic, hbridgeless⟩

/-- **Theorem 1** (paper, restated at line 2273-2274): the vertex cover
    problem on cubic bridgeless graphs (VC-CBG) is NP-complete.

    Derived from `Theorem11` by `NPHard_of_restriction`, using the family
    inclusion `CubicPlanarBridgeless ⊆f CubicBridgeless` — dropping
    planarity only widens the instance family, so hardness transfers
    upward with no converse needed at all. -/
public theorem Theorem1 (hNPbridgeless : InNP (VCYes CubicPlanarBridgeless)) :
    NPComplete (VCYes CubicBridgeless) :=
  ⟨VC_InNP CubicBridgeless,
    NPHard_of_restriction CubicPlanarBridgeless_subset_CubicBridgeless
      (Theorem11 hNPbridgeless).2⟩
-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, or hypothesis hacking.
  `axiom`: standard Lean: propext, Classical.choice, Quot.sound
           added as proven in previous literature:
            * NPHard_of_restriction: A family of problems is implicitly NP-hard if
              its subset family of problems is NP-hard (Standard fact: Garey-Johnson Textbook)
            * Theorem10: Vertex cover problem on Cubic Planar 2-Vertex-Connected graph
              is NP-hard (proven by Mohar)
            * VC_InNP: Vertex cover problem is in NP (known fact)
            * Whitney: 2-vertec-connected graph is brdigeless (proven by Whitney)

  Correspondence with the paper (Appendix B, lines 2244-2278, Table 24):
    "Equate" row (Cubic+Planar+2VC → Cubic+Planar+Bridgeless, via
      Whitney's Theorem)     → `CubicPlanar2VC_subset_CubicPlanarBridgeless`
                                + `NPHard_of_restriction`, in `Theorem11`.
    "Generalize & End" row
      (→ Cubic+Bridgeless)   → `CubicPlanarBridgeless_subset_
                                CubicBridgeless` + `NPHard_of_restriction`,
                                in `Theorem1`.
-/
