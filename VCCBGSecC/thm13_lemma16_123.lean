/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 16, Points 1–3

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

  ═══════════════════════════════════════════════════════════════════════════
  WHAT IS PROVIDED, AND FROM WHERE
  ═══════════════════════════════════════════════════════════════════════════

  Defined LOCALLY in this file:
    seedsOf                         — the list of seed vertices from a
                                       matching's edges
    mem_seedsOf_of_perfect          — every vertex appears in `seedsOf M`
                                       when `M` is a perfect matching
                                       [Point 2's content]

  From `thm13_lemma12_1` (via the import chain):
    Color (5 constructors), Coloring, VCover  — shared vocabulary
    AlgC, runAlgC, initColoring, fuelBound     — the recursive algorithm
                                                  model (five colors,
                                                  seed-yellowing built in)
    ValidColoring G S nbrOrder v fuel C        — `C = runAlgC ...`
    Lemma12_Part1                              — two valid colorings for
                                                  the SAME run parameters
                                                  are literally equal
                                                  [Point 1]

  From `thm13_lemma12_2a`:
    OrderMatchesAdj G nbrOrder                  — bridges `nbrOrder`'s
                                                  traversal to `G.Adj`

  From `thm13_lemma14`:
    reachU, reachW                              — the blue/red Finsets
    Lemma14_witness                             — the AltBip term
                                                  [Points 3(a)+(b)]

  From `thm13_lemma15`:
    Lemma15                                     — AltBip + |W|<|U| ⟹
                                                  DimBip [Point 3(c)]

  From `thm13_lemma9` (imported separately, for Petersen's
  theorem/perfect matchings — untouched by the Algorithm-C model change):
    IsPerfectMatching, PetersenMatching

  From Theorem12 (`thm12`, imported transitively):
    DimBip G S                                  — Definition 25

  ═══════════════════════════════════════════════════════════════════════════
-/

public import VCCBGSecC.thm13_lemma9
public import VCCBGSecC.thm13_lemma15

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Color

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Matching-related properties defined here
-- ═══════════════════════════════════════════════════════════════════════════

/-- The seed list: all endpoints of edges in `M` (every vertex appears
    when `M` is a perfect matching — see `mem_seedsOf_of_perfect`). -/
public noncomputable def seedsOf (M : Finset (Sym2 V)) : List V :=
  M.toList.flatMap (fun e => [e.out.1, e.out.2])

/-- Every vertex appears in `seedsOf M` when `M` is a perfect matching.

    Paper (lines 2669–2672): "A cubic bridgeless graph has a perfect
    matching (Theorem 3). Hence, each vertex of the given graph G is an
    endpoint of an edge in the perfect matching." -/
public theorem mem_seedsOf_of_perfect
    {M : Finset (Sym2 V)} (hM : IsPerfectMatching M) (v : V) :
    v ∈ seedsOf M := by
  obtain ⟨e, heM, hve⟩ := hM.2 v
  simp only [seedsOf, List.mem_flatMap, Finset.mem_toList]
  refine ⟨e, heM, ?_⟩
  rw [← Quot.out_eq e] at hve
  rw [Sym2.mem_iff] at hve
  rcases hve with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Point 1 — unique 2-coloring for a given seed
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Point 1**: Algorithm C's coloring, for a fixed set of run
    parameters `(G, S, nbrOrder, v, fuel)`, is unique — any two valid
    colorings are literally equal as functions.

    Paper (lines 2665–2668): "Algorithm C results in a unique 2-coloring
    of the given graph for a given vertex cover and a given seed
    vertex. Formally, by Lemma 12, there is only one way to 2-color a
    given graph G w.r.t. a given vertex cover S and seed vertex v ∈ S."

    This is exactly `Lemma12_Part1`, imported directly — no new proof,
    and no change from any earlier version: `ValidColoring`'s
    definitional shape (`C = runAlgC ...`) has been stable across the
    four-color and five-color models alike. -/
public theorem Lemma16_Point1
    {S : Finset V} {nbrOrder : V → List V} {v : V} {fuel : ℕ}
    {C₁ C₂ : Coloring V}
    (hVC₁ : ValidColoring G S nbrOrder v fuel C₁)
    (hVC₂ : ValidColoring G S nbrOrder v fuel C₂) :
    C₁ = C₂ :=
  Lemma12_Part1 hVC₁ hVC₂

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Point 2 — each vertex of G is a seed
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Point 2**: every vertex of `G` is a seed — i.e. appears in
    `seedsOf M` for the perfect matching `M` given by Petersen's
    theorem.

    Paper (lines 2669–2672): "...Algorithm B iterates over each edge in
    the perfect matching. Consequently, this implies that Algorithm B
    implicitly iterates over each vertex." -/
public theorem Lemma16_Point2
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e) :
    ∃ M : Finset (Sym2 V), IsPerfectMatching M ∧ ∀ v : V, v ∈ seedsOf M := by
  obtain ⟨M, hM_perf, _⟩ := PetersenMatching hcubic hbridgeless
  exact ⟨M, hM_perf, fun v => mem_seedsOf_of_perfect hM_perf v⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Point 3 — the per-seed chain (a)+(b)+(c)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Point 3**: for a single seed `v0`, the chain (a)–(c) holds:
    a unique coloring's induced bipartite graph (a) is alternating (b),
    and is diminishing whenever `|W| < |U|` (c).

    Paper (lines 2673–2683):
    "(a) A unique 2-coloring (Lemma 12) implies a unique induced
    bipartite graph (Lemma 13). (b) A unique induced bipartite graph
    implies a unique S-alternating bipartite graph (Lemma 14). (c) If
    an S-alternating bipartite graph is not an S-diminishing bipartite
    graph (Lemma 15), then it implies there is no S-diminishing
    bipartite graph."

    `Lemma14_witness` (`_lemma14`) packages the induced bipartite graph as
    an S-alternating bipartite graph [(a)+(b)] — its signature no longer
    takes `hlen`/`hfuel` at all, since `reachU`/`reachW` under the
    current fully-deterministic model are simply "the blue/red
    vertices," with no reachability-restriction argument needed.
    `Lemma15` (`_15`) upgrades it to a full `DimBip G S` whenever
    `|reachW v0| < |reachU v0|` [(c)] — it still needs `hlen`/`hfuel`,
    since `Lemma15_flip_vc`'s vertex-cover proof genuinely requires
    per-call blue-neighbor resolution. -/
public theorem Lemma16_Point3
    {S : Finset V} {v0 : V} (hv0 : v0 ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ}
    (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S) :
    (∃ A : AltBip G S,
      A.toBipSub.U = reachU G S C v0 ∧ A.toBipSub.W = reachW G S C v0)
    ∧
    ((reachW G S C v0).card < (reachU G S C v0).card →
      ∃ D : DimBip G S,
        D.toAltBip.toBipSub.U = reachU G S C v0 ∧
        D.toAltBip.toBipSub.W = reachW G S C v0) :=
  ⟨⟨Lemma14_witness G S nbrOrder hv0 hOrder hVC hSVC, rfl, rfl⟩,
   fun hgt => Lemma15 hv0 hOrder hlen hfuel hVC hSVC hgt⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Lemma 16, Points 1–3 — the full assembly
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 16, Points 1–3** (paper lines 2664–2683): the complete setup
    for Lemma 16's proof, gathering Points 1, 2, and 3 into one
    statement, under the CURRENT five-color recursive Algorithm-C model.
    No `hCv0`/seed-color hypothesis anywhere (never load-bearing, per
    `_15`'s own predecessors' analysis): `Lemma15`'s `U_ne` field
    follows purely from the cardinality hypothesis `hgt`, independent of
    which specific vertex ends up witnessing `U`'s nonemptiness. -/
public theorem Lemma16_Points1to3
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    {S : Finset V} (hSVC : VCover G S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) :
    (∃ M : Finset (Sym2 V), IsPerfectMatching M ∧ ∀ v : V, v ∈ seedsOf M)
    ∧
    (∀ ⦃v0 : V⦄, v0 ∈ S → ∀ {fuel : ℕ},
        fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel →
        ∀ ⦃C₁ C₂ : Coloring V⦄,
        ValidColoring G S nbrOrder v0 fuel C₁ →
        ValidColoring G S nbrOrder v0 fuel C₂ →
        (C₁ = C₂) ∧
        ((∃ A : AltBip G S,
            A.toBipSub.U = reachU G S C₁ v0 ∧
            A.toBipSub.W = reachW G S C₁ v0) ∧
         ((reachW G S C₁ v0).card < (reachU G S C₁ v0).card →
            ∃ D : DimBip G S,
              D.toAltBip.toBipSub.U = reachU G S C₁ v0 ∧
              D.toAltBip.toBipSub.W = reachW G S C₁ v0))) :=
  ⟨Lemma16_Point2 hcubic hbridgeless,
   fun _ hv0 _ hfuel _ _ hVC₁ hVC₂ =>
     ⟨Lemma16_Point1 hVC₁ hVC₂,
      Lemma16_Point3 hv0 hOrder hlen hfuel hVC₁ hSVC⟩⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking. (Petersen Matching axiom imported.)

  Proof map:
    mem_seedsOf_of_perfect ← local, unchanged — pure Finset/matching
                              fact, independent of the Algorithm-C model
    Lemma16_Point1   ← Lemma12_Part1  (thm13_lemma12_1) —
                        UNCHANGED
    Lemma16_Point2   ← PetersenMatching (thm13_lemma9) +
                        mem_seedsOf_of_perfect (local, §1) — UNCHANGED
    Lemma16_Point3   ← Lemma14_witness (thm13_lemma14)
                      + Lemma15         (thm13_lemma15)
                        PORTED: `Lemma14_witness`'s call site is now
                        shorter (no `hlen`/`hfuel`); `Lemma15`'s call
                        site is unchanged in shape.
    Lemma16_Points1to3 ← packages the above three theorems into the
                          single conjunction matching the paper's
                          three-point proof setup (lines 2664–2683)
-/
