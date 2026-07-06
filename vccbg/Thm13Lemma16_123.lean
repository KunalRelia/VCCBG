/-
  Lean 4 / Mathlib — Lemma 16, Points 1–3, assuming the prior files are
  imported.

  "Given a cubic bridgeless graph G and a vertex cover S, if Algorithm C
   is executed by seeding on each vertex in S and no smaller vertex
   cover S' is derived by the end of execution of Algorithm B, it
   implies that there is no S-diminishing bipartite graph in graph G."

  Source: paper §C.2.2, lines 2659–2725. THIS FILE covers exactly the
  three numbered points of the proof's setup, lines 2664–2683:
    Point 1 (lines 2665–2668): unique 2-coloring for a given seed
    Point 2 (lines 2669–2672): each vertex of G is a seed
    Point 3 (lines 2673–2683): the per-seed chain
        (a) unique coloring (L12) ⟹ unique bipartite graph (L13)
        (b) unique bipartite graph ⟹ unique alternating graph (L14)
        (c) alternating + |U|>|W| ⟹ diminishing (L15)

  These points are the "natural progression" of Lemma 12 → 13 → 14 → 15
  already proved, restated per-seed, together with the seed-coverage
  fact (Petersen's theorem + Algorithm B's perfect-matching loop). This
  file's content is the assembly of already-proved results into the
  single combined statement the paper calls "Points 1–3." The remaining
  contrapositive argument of Lemma 16 (lines 2684–2725: "if NO smaller
  S' is found for ANY seed, then NO DimBip exists at all") is NOT
  attempted here.

  ═══════════════════════════════════════════════════════════════════════════
  WHAT IS PROVIDED, AND FROM WHERE
  ═══════════════════════════════════════════════════════════════════════════

  Defined LOCALLY in this file (§1):
    seedsOf                         — the list of seed vertices from a
                                       matching's edges
    mem_seedsOf_of_perfect          — every vertex appears in `seedsOf M`
                                       when `M` is a perfect matching
                                       [Point 2's content]

  From Lemma12 Part1:
    AltReachActive                  — active-walk reachability
    Lemma12_Part1                   — any two valid colorings agree
                                       along active walks [Point 1]

  From Lemma14:
    reachU, reachW                  — the reachable blue/red Finsets
    Lemma14_witness                 — the AltBip term [Points 3(a)+(b)]

  From Lemma15:
    Lemma15                         — AltBip + |W|<|U| ⟹ DimBip
                                       [Point 3(c)]

  From Theorem12:
    DimBip G S                      — Definition 25

  AXIOM COUNT:  0 introduced in this file (PetersenMatching axiom imported from Lemma 9)
  SORRY COUNT:  0
  ═══════════════════════════════════════════════════════════════════════════
-/

import Mathlib
/-
 Lean requires files to sit within an established workspace managed by Lake
 (Lean's build system) for imports to function correctly. Hence, please ensure
 that the following import statement is modified to follow the structure where
 the file being imported sits within your project.
-/
import MyGraphProject.vccbg.Thm13Lemma9
import MyGraphProject.vccbg.Thm13Lemma15

open Color

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Matching-related properties defined here
-- ═══════════════════════════════════════════════════════════════════════════

/-- The seed list: all endpoints of edges in `M` (every vertex appears
    when `M` is a perfect matching — see `mem_seedsOf_of_perfect`). -/
noncomputable def seedsOf (M : Finset (Sym2 V)) : List V :=
  M.toList.flatMap (fun e => [e.out.1, e.out.2])
-- noncomputable def seedsOf (M : Finset (Sym2 V)) : Finset V :=
--     M.biUnion (fun e => Finset.univ.filter (· ∈ e))

/-- Every vertex appears in `seedsOf M` when `M` is a perfect matching.

    Paper (lines 2669–2672): "A cubic bridgeless graph has a perfect
    matching (Theorem 3). Hence, each vertex of the given graph G is an
    endpoint of an edge in the perfect matching." -/
theorem mem_seedsOf_of_perfect
    {M : Finset (Sym2 V)} (hM : IsPerfectMatching M) (v : V) :
    v ∈ seedsOf M := by
  obtain ⟨e, heM, hve⟩ := hM.2 v
  simp only [seedsOf, List.mem_flatMap, Finset.mem_toList]
  refine ⟨e, heM, ?_⟩
  rw [← Quot.out_eq e] at hve
  -- simpa using hve
  -- have h : v ∈ [e.out.1, e.out.2] := by simpa using hve
  rw [Sym2.mem_iff] at hve
  rcases hve with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Point 1 — unique 2-coloring for a given seed
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Point 1**: Algorithm C's coloring, for a fixed `(G, S, v)`, is
    unique — any two valid colorings agree on every actively-reachable
    vertex.

    Paper (lines 2665–2668): "Algorithm C results in a unique 2-coloring
    of the given graph for a given vertex cover and a given seed
    vertex. Formally, by Lemma 12, there is only one way to 2-color a
    given graph G w.r.t. a given vertex cover S and seed vertex v ∈ S."

    This is exactly `Lemma12_Part1`, imported directly — no new proof. -/
theorem Lemma16_Point1
    {S : Finset V} {v : V} (hS : VCover G S)
    {C₁ C₂ : Coloring V}
    (hVC₁ : ValidColoring G S v C₁) (hVC₂ : ValidColoring G S v C₂) :
    ∀ ⦃w : V⦄, AltReachActive G S C₁ v w → C₁ w = C₂ w :=
  fun _ hreach => Lemma12_Part1 hS hVC₁ hVC₂ hreach

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Point 2 — each vertex of G is a seed
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Point 2**: every vertex of `G` is a seed — i.e. appears in
    `seedsOf M` for the perfect matching `M` given by Petersen's
    theorem.

    Paper (lines 2669–2672): "...Algorithm B iterates over each edge in
    the perfect matching. Consequently, this implies that Algorithm B
    implicitly iterates over each vertex." -/
theorem Lemma16_Point2
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e) :
    ∃ M : Finset (Sym2 V), IsPerfectMatching M ∧ ∀ v : V, v ∈ seedsOf M := by
  obtain ⟨M, hM_perf, _⟩ := PetersenMatching hcubic hbridgeless
  exact ⟨M, hM_perf, fun v => mem_seedsOf_of_perfect hM_perf v⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Point 3 — the per-seed chain (a)+(b)+(c)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Point 3**: for a single seed `v`, the chain (a)–(c) holds:
    a unique coloring's induced bipartite graph (a) is alternating (b),
    and is diminishing whenever `|W| < |U|` (c).

    Paper (lines 2673–2683):
    "(a) A unique 2-coloring (Lemma 12) implies a unique induced
    bipartite graph (Lemma 13). (b) A unique induced bipartite graph
    implies a unique S-alternating bipartite graph (Lemma 14). (c) If
    an S-alternating bipartite graph is not an S-diminishing bipartite
    graph (Lemma 15), then it implies there is no S-diminishing
    bipartite graph."

    Formalized positively: given `ValidColoring G S v C` and `v ∈ S`,
    `Lemma14_witness` packages the unique induced bipartite graph
    (Lemma 13's facts, baked into its construction) as an
    S-alternating bipartite graph [(a)+(b)]; `Lemma15` upgrades it to a
    full `DimBip G S` whenever `|reachW v| < |reachU v|` [(c)]. -/
theorem Lemma16_Point3
    {S : Finset V} {v : V} {C : Coloring V}
    (hS : VCover G S) (hVC : ValidColoring G S v C) (hv : v ∈ S) :
    (∃ A : AltBip G S,
      A.toBipSub.U = reachU G S C v ∧ A.toBipSub.W = reachW G S C v)
    ∧
    ((reachW G S C v).card < (reachU G S C v).card →
      ∃ D : DimBip G S,
        D.toAltBip.toBipSub.U = reachU G S C v ∧
        D.toAltBip.toBipSub.W = reachW G S C v) :=
  ⟨⟨Lemma14_witness hVC hv, rfl, rfl⟩,
   fun hgt => Lemma15 hS hVC hv hgt⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Lemma 16, Points 1–3 — the full assembly
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 16, Points 1–3** (paper lines 2664–2683): the complete setup
    for Lemma 16's proof, gathering Points 1, 2, and 3 into one
    statement. -/
theorem Lemma16_Points1to3
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    {S : Finset V} (hS : VCover G S) :
    (∃ M : Finset (Sym2 V), IsPerfectMatching M ∧ ∀ v : V, v ∈ seedsOf M)
    ∧
    (∀ ⦃v : V⦄, v ∈ S → ∀ ⦃C₁ C₂ : Coloring V⦄,
        ValidColoring G S v C₁ → ValidColoring G S v C₂ →
        (∀ ⦃w : V⦄, AltReachActive G S C₁ v w → C₁ w = C₂ w) ∧
        ((∃ A : AltBip G S,
            A.toBipSub.U = reachU G S C₁ v ∧
            A.toBipSub.W = reachW G S C₁ v) ∧
         ((reachW G S C₁ v).card < (reachU G S C₁ v).card →
            ∃ D : DimBip G S,
              D.toAltBip.toBipSub.U = reachU G S C₁ v ∧
              D.toAltBip.toBipSub.W = reachW G S C₁ v))) :=
  ⟨Lemma16_Point2 hcubic hbridgeless,
   fun _ hv _ _ hVC₁ hVC₂ =>
     ⟨Lemma16_Point1 hS hVC₁ hVC₂, Lemma16_Point3 hS hVC₁ hv⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  AXIOM COUNT:  0 introduced in this file (PetersenMatching is imported)
  SORRY COUNT:  0

  Proof map:
    mem_seedsOf_of_perfect ← local, copied verbatim from its prior
                              location (the proof itself is unchanged;
                              only its IMPORT SOURCE changed — it is
                              now declared directly in this file)
    Lemma16_Point1   ← Lemma12_Part1             (Lemma12_Part1_Bipartite)
    Lemma16_Point2   ← PetersenMatching + mem_seedsOf_of_perfect (local, §1)
    Lemma16_Point3   ← Lemma14_witness            (Lemma14_Alternating)
                      + Lemma15                    (Lemma15_Diminishing)
    Lemma16_Points1to3 ← packages the above three theorems into the
                          single conjunction matching the paper's
                          three-point proof setup (lines 2664–2683)
-/
