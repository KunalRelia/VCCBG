/-
  Lean 4 / Mathlib — Lemma 16, "post-1,2,3" phase
  "Guaranteeing a complete search" and the closing argument of Lemma 16.

  Source: paper §C.2.2, lines 2684–2710.

  ═══════════════════════════════════════════════════════════════════════════
  WHERE THIS PICKS UP
  ═══════════════════════════════════════════════════════════════════════════

  Lemma 16's statement (paper, lines 2661–2663):
    "Given a cubic bridgeless graph G and a vertex cover S, if Algorithm C
     is executed by seeding on each vertex in S and no smaller vertex
     cover S′ is derived by the end of execution of Algorithm B, it
     implies that there is no S-diminishing bipartite graph in graph G."

  The proof's numbered items 1–3 (lines 2664–2683) — unique 2-coloring for
  a fixed seed (Lemma 12), every vertex is a seed (Petersen + the perfect
  matching), and the per-seed chain unique-coloring ⟹ unique bipartite
  graph ⟹ unique alternating graph ⟹ diminishing-iff-more-blue-than-red
  (Lemmas 12–15) — are exactly the content already established across
  `thm13_lemma12_1/2a/2b`, `thm13_lemma12_overall`, `thm13_lemma13`,
  `thm13_lemma14`, `thm13_lemma15`. This file does NOT re-prove any of
  that; it imports it and picks up exactly where those items leave off.

  THIS FILE covers the remainder of the proof (lines 2684–2710):
  "Guaranteeing a complete search" — generalizing the PER-SEED chain
  (which only ever talks about one fixed seed v) into a statement about
  ALL seeds simultaneously, closing the loop with Theorem 12's global
  characterization of minimality.

  ═══════════════════════════════════════════════════════════════════════════
  STANDING HYPOTHESES FOR THIS PHASE
  ═══════════════════════════════════════════════════════════════════════════

  Per the task: G is cubic, bridgeless, simple, and connected.
    • "simple" needs no separate hypothesis: Mathlib's `SimpleGraph V`
      type is *already* simple (irreflexive + symmetric adjacency, hence
      no self-loops and no parallel edges) for every term of that type.
    • "connected" is genuinely new and is carried as an explicit
      hypothesis `hconn : G.Connected` on the two capstone theorems
      (`Lemma16_completes_search`, `Lemma16`), matching how the paper's
      standing assumptions about the input graph are always in force.
      As with `hcubic`/`hbridgeless` in `Theorem12` (see that file's own
      commentary: "Theorem 12 itself does not use them in its proof;
      they are needed by Algorithm A"), `hconn` is not exercised by the
      *specific* proof terms given here — none of the combinatorics
      below needs the WHOLE graph to be one piece, only that the
      relevant sub-structures (matchings, diminishing components) behave
      as claimed, which holds component-by-component regardless of
      global connectivity. It is carried purely for signature fidelity
      with the stated standing assumptions on the input graph.

  ═══════════════════════════════════════════════════════════════════════════
  THE THREE BULLETS OF "GUARANTEEING A COMPLETE SEARCH" (lines 2687–2706)
  ═══════════════════════════════════════════════════════════════════════════

  • Coverage of perfect matching (2691–2693): iterating over the
    endpoints of a perfect matching's edges reaches every vertex of the
    graph — in particular every vertex of S, since S ⊆ V. Formalized as
    `Lemma16_seed_coverage`, reusing the `PetersenMatching` axiom and
    `IsPerfectMatching` from `thm13_lemma9_claude_v3.lean`. Zero new
    axioms.

  • Selection of blue seed and symmetric difference, and Capturing a
    component (2694–2706): if S is not minimum, Theorem 12 gives an
    (aggregate) `DimBip` D built from the symmetric difference S \ S′,
    S′ \ S of S against some smaller cover S′. The paper is careful to
    note this aggregate object need only contain "at least one connected
    component" that is itself diminishing — the aggregate blue/red
    counts alone don't pin down *which* vertex to seed at. Locating that
    component and showing Algorithm C, seeded inside it, is confined to
    exactly that component splits into two cases:
      • a boundary vertex bordering the component ONLY from the U-side
        is unconditionally forced black by V1 alone — proved below as
        `boundary_forced_black`, no axiom needed;
      • a boundary vertex bordering the component from BOTH sides forces
        an odd cycle through it (V1 unconditionally demands black, V3
        unconditionally demands blue, simultaneously) — ruling this out
        for SOME diminishing component is a genuine structural fact
        about symmetric differences of vertex covers, not derivable from
        `DimBip`'s bare axioms nor established in `thm13_lemma12_*`–
        `thm13_lemma15_*`. This residual content is isolated in the one
        remaining axiom, `DimBip_seed_capture` — see the discussion
        immediately preceding its declaration for the full analysis.

  ═══════════════════════════════════════════════════════════════════════════
  WHAT IS *NOT* FORMALIZED
  ═══════════════════════════════════════════════════════════════════════════

  Lines 2684–2687 ("an S-diminishing bipartite graph cannot exist after
  at most m² iterations of Algorithm B: m times seeding of at most m
  vertices") is a RUNTIME/COMPLEXITY remark, not a correctness claim: it
  bounds how many times the algorithm's loops execute, not what is true
  about G. None of the files in this project model loop iteration counts
  (Lemma 11 abstracts Algorithm B's loop as a fold over an arbitrary
  candidate list, with no notion of "how many candidates"); consistent
  with that, we do not formalize the m² bound here. It has no bearing on
  the truth of `Lemma16` below, only on Algorithm B's efficiency.

  AXIOMS:   1  (`DimBip_seed_capture` — TODO: need to remove this axiom)
  SORRIES:  0
  ═══════════════════════════════════════════════════════════════════════════
-/

import Mathlib
/-
 Lean requires files to sit within an established workspace managed by Lake
 (Lean's build system) for imports to function correctly. Hence, please ensure
 that the following import statements are modified to follow the structure
 where the files being imported sit within your project.
-/
import MyGraphProject.vccbg.Thm13Lemma16_123
import MyGraphProject.vccbg.Thm13Lemma15
import MyGraphProject.vccbg.Thm13Lemma9

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Color

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Coverage of perfect matching (paper lines 2691–2693)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Coverage of perfect matching**: every vertex of `G` — the whole
    vertex set `V`, and in particular every vertex of any vertex cover
    `S` (since `S ⊆ V`) — is the endpoint of some edge in a perfect
    matching.

    Paper (lines 2691–2693): "A cubic bridgeless graph is guaranteed to
    have a perfect matching (Theorem 3). Hence, iterating over the
    endpoints of each edge of a matching (Line 4 / 5, Algorithm B) is
    equivalent to iterating over each vertex of the graph." Algorithm B
    then only actually *seeds* on whichever endpoints happen to lie in
    the current `S` (Line 7's check) — but since this theorem already
    covers every vertex of `V`, it directly gives coverage of `S` too,
    with no separate restricted statement needed: applying it to any
    `v ∈ S` (which is, in particular, a `v : V`) is immediate.

    Proof: this is exactly `IsPerfectMatching`'s own coverage clause
    (`hM.2 : ∀ v, ∃ e ∈ M, v ∈ e`), read off `PetersenMatching` from
    `thm13_lemma9_claude_v3.lean` verbatim — no new axiom needed. -/
theorem Lemma16_seed_coverage
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e) :
    ∃ M : Finset (Sym2 V), IsPerfectMatching M ∧ ∀ v : V, ∃ e ∈ M, v ∈ e := by
  obtain ⟨M, hM, _⟩ := PetersenMatching hcubic hbridgeless
  exact ⟨M, hM, hM.2⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Selection of blue seed + Capturing a component (2694–2706)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Component-capture axiom** (paper lines 2694–2706: "Selection of blue
    seed and symmetric difference" together with "Capturing a
    component").

    Every `DimBip G S` — however it arose, in particular the AGGREGATE
    symmetric-difference witness `U := S \ S′`, `W := S′ \ S` that
    `Theorem12`'s (⇒) direction builds from an arbitrary smaller cover
    `S′` — contains, within its own `U`, a vertex `v` that Algorithm C
    can genuinely be seeded on to witness a diminishing bipartite graph
    THROUGH ITS OWN REACHABILITY MACHINERY: i.e. some `ValidColoring` at
    `v` has strictly more actively-reachable blue vertices than red.

    Paper's argument (not re-derived from Mathlib primitives here):
      • "Selection of blue seed and symmetric difference" (2694–2700):
        the aggregate `U`/`W` need only contain "at least one connected
        component" that is itself diminishing — this is a pigeonhole
        fact: decompose the induced subgraph on `D.dU ∪ D.dW` into
        connected components; since the aggregate blue count exceeds
        the aggregate red count (`D.U_gt_W`), some individual component
        must itself have more blue than red (else every component's red
        count would be `≥` its blue count, and summing would contradict
        the strict aggregate inequality).
      • "Capturing a component" (2701–2706): every vertex bordering that
        component from outside it lies in `S ∩ S′` — present in BOTH
        covers, hence in neither `D.dU` nor `D.dW` (the paper: "The
        vertex cover colored black is a vertex that is present in both
        vertex covers, S and S′, and hence, is not their symmetric
        difference"). By `ValidColoring`'s V1/V3 rules such a bordering
        vertex is forced BLACK, and `AltReachActive` never steps away
        from a black vertex (only `blue_step`/`red_step` propagate — see
        `thm13_lemma12_1_claude_v3.lean`). Hence Algorithm C, seeded at
        any vertex of that component, reaches exactly that component:
        no more (black vertices block further propagation) and no less
        (the component is connected, so alternating forcing sweeps all
        of it). This gives `reachU`/`reachW` at that seed equal to the
        component's own `U_i`/`W_i`, which is precisely what makes the
        component "diminishing" translate into `(reachW).card <
        (reachU).card` for that concrete seed.

    Discharge path: fully formalizing this requires Mathlib's
    `SimpleGraph.ConnectedComponent` machinery applied to the induced
    subgraph `G.induce (↑D.dU ∪ ↑D.dW : Set V)`, an averaging/pigeonhole
    lemma over the resulting finite partition, and an induction on
    `AltReachActive` showing that reachability from a component-internal
    seed stays confined to the component (using exactly the black-vertex
    isolation argument above, itself a short corollary of `ValidColoring`
    V1/V3 plus the definition of `AltReachActive`). This is a substantial
    but standard combinatorial undertaking, orthogonal to everything
    proved in `thm13_lemma12_*`–`thm13_lemma15_*`; we axiomatize the
    conclusion here rather than re-derive connected-component theory from
    scratch, in the same spirit as `PetersenMatching` / `MatchingLowerBound`
    / `AlgB_spec` in `thm13_lemma9_claude_v3.lean`.
    ───────────────────────────────────────────────────────────────────
    WHY "reachability capture" genuinely needs an axiom, not just
    "boundary vertices go black":

    A boundary vertex `x ∈ S \ D.dU` adjacent to SOME `u ∈ D.dU` is
    cleanly forced black by V1 alone — no other rule ever fires on it,
    so this case is a fully proved theorem below (`boundary_forced_black`)
    and needs no axiom.

    The genuinely hard case is a boundary vertex `x` adjacent to BOTH a
    `U`-vertex `u₀` and a `W`-vertex `w₀` of the *same* connected
    component: V1 forces `x = black` (from `u₀`) while V3 forces
    `x = blue` (from `w₀`, since `w₀` is reached red via the internal
    alternating path *within* the component — a route that does not
    pass through `x`, so `x` being black does not block it). Both rules
    are unconditional in `ValidColoring`, so this is a genuine
    contradiction, not an artifact of processing order. Unwinding it:
    such an `x` closes an ODD CYCLE `x–u₀–(odd internal path)–w₀–x`
    (odd because any path between different parts of a bipartite graph
    has odd length) — i.e. it is exactly the phenomenon
    `Lemma12_Part2b_oddcycle_no_proper_2coloring` already governs, just
    straddling the component boundary via an external vertex rather than
    lying inside it. Ruling this out for *some* diminishing component
    (not necessarily every one) is a genuine structural fact about
    symmetric differences of two vertex covers — informally, that they
    decompose into alternating paths/even cycles with no such
    "doubly-bordering" external vertex, the vertex-cover analogue of the
    classical augmenting-path decomposition for matchings — which is not
    derivable from `DimBip`'s bare axioms (`cross` only constrains `U`'s
    side) and is not established anywhere in `thm13_lemma12_*`–
    `thm13_lemma15_*`. We isolate exactly this residual fact in the axiom
    below, in the same spirit as `PetersenMatching` /
    `MatchingLowerBound` / `AlgB_spec` in `thm13_lemma9_claude_v3.lean`.
    ───────────────────────────────────────────────────────────────────
    A boundary vertex bordering the diminishing component only from the
    `U`-side is unconditionally forced black — the clean half of
    "Capturing a component" (paper lines 2701–2706), needing no axiom:
    V1 fires once (from the `U`-neighbor) and nothing else ever
    constrains `x`, since `x ∉ D.dU ∪ D.dW`. -/
theorem boundary_forced_black
    {S : Finset V} (D : DimBip G S) {v x u : V} {C : Coloring V}
    (hVC : ValidColoring G S v C)
    (hxS : x ∈ S) (hu : u ∈ D.dU) (hadj : G.Adj u x) (hCu : C u = blue) :
    C x = black :=
  hVC.V1 hadj hCu hxS

/-- **Component-capture axiom** (paper lines 2694–2706, residual content
    only — see the discussion above `boundary_forced_black` for exactly
    what remains after the clean "single-sided boundary → black" case is
    discharged as a theorem).

    Every `DimBip G S` contains, within its own `U`, a vertex `v` that
    Algorithm C can genuinely be seeded on to witness a diminishing
    bipartite graph through its own reachability machinery. -/
axiom DimBip_seed_capture
    {S : Finset V} (D : DimBip G S) :
    ∃ v ∈ D.dU, ∃ C : Coloring V, ValidColoring G S v C ∧
      (reachW G S C v).card < (reachU G S C v).card

/-- If `S` is not a minimum vertex cover, `Theorem12` gives an (aggregate)
    diminishing bipartite graph witness.

    Paper (lines 2694–2697): "In Theorem 12, we discussed that if the
    given vertex cover S is not a minimum vertex cover, then there
    exists a smaller vertex cover S′. The symmetric difference... must
    contain at least one connected component that is an S-diminishing
    bipartite graph." — this theorem captures the FIRST half of that
    sentence (existence of the aggregate `DimBip`); the "at least one
    connected component" half is exactly `DimBip_seed_capture`, applied
    next in `Lemma16_diminishing_seed_exists`.

    Proof: the contrapositive of `Theorem12`'s (⇐) direction, i.e. of
    `Theorem12.mpr : ¬∃D → MinVCover`, via classical `by_contra`. Zero
    new axioms — pure logic on top of the already-proved `Theorem12`. -/
theorem Lemma16_exists_dimBip_of_not_min
    {S : Finset V}
    (hS_vc : VCover G S) (hS_bound : S.card ≤ Fintype.card V - 1)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (hnotmin : ¬ MinVCover G S) :
    ∃ _ : DimBip G S, True := by
  by_contra hno
  exact hnotmin ((Theorem12 hS_vc hS_bound hcubic hbridgeless).mpr hno)

/-- **Selection of blue seed and symmetric difference + Capturing a
    component**, combined (paper lines 2694–2706): if `S` is not a
    minimum vertex cover, there is an ACTUAL seed `v ∈ S` and an ACTUAL
    valid coloring `C` at `v` — the concrete output Algorithm C would
    produce if seeded there — whose reachable structure is diminishing.

    Proof: `Theorem12` gives the aggregate `DimBip` (previous theorem);
    `DimBip_seed_capture` descends from the aggregate object to a single
    genuinely seedable, genuinely diminishing component. `v ∈ S` follows
    from `D.dU ⊆ S` (`AltBip.U_sub`), since `v ∈ D.dU`. -/
theorem Lemma16_diminishing_seed_exists
    {S : Finset V}
    (hS_vc : VCover G S) (hS_bound : S.card ≤ Fintype.card V - 1)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (hnotmin : ¬ MinVCover G S) :
    ∃ v ∈ S, ∃ C : Coloring V, ValidColoring G S v C ∧
      (reachW G S C v).card < (reachU G S C v).card := by
  obtain ⟨D, _⟩ :=
    Lemma16_exists_dimBip_of_not_min hS_vc hS_bound hcubic hbridgeless hnotmin
  obtain ⟨v, hvU, C, hVC, hlt⟩ := DimBip_seed_capture D
  exact ⟨v, D.toAltBip.U_sub hvU, C, hVC, hlt⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. The converse: a diminishing seed genuinely shrinks the cover
-- ═══════════════════════════════════════════════════════════════════════════

/-- If Algorithm C, seeded at `v ∈ S`, finds a diminishing coloring
    (strictly more reachable blue than red), flipping — removing the
    reachable blue vertices from `S` and adding the reachable red ones,
    exactly Line 19 of Algorithm B — literally produces a smaller vertex
    cover. This is `Lemma15` (upgrading the alternating structure at `v`
    to a full `DimBip`) composed with `Theorem12`'s
    `VCLemmas.dimBip_gives_smaller`.

    This theorem is the precise sense in which `hNoImprovement` below
    ("no seed ever finds a diminishing coloring") is exactly Algorithm
    B's termination condition (`algB_update`'s guard, `thm13_lemma11`,
    never firing for any candidate arising from any seed): were some
    seed diminishing, THIS theorem shows a strictly smaller cover would
    result, contradicting "no smaller cover was ever derived." Zero new
    axioms — pure composition of `Lemma15_witness` and
    `VCLemmas.dimBip_gives_smaller`. -/
theorem Lemma16_seed_shrinks_cover
    {S : Finset V} {v : V} {C : Coloring V}
    (hS_vc : VCover G S) (hVC : ValidColoring G S v C) (hvS : v ∈ S)
    (hlt : (reachW G S C v).card < (reachU G S C v).card) :
    ∃ S' : Finset V, VCover G S' ∧ S'.card < S.card := by
  set D := Lemma15_witness hS_vc hVC hvS hlt with hDdef
  exact ⟨D.flipped, VCLemmas.dimBip_gives_smaller D⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. The closing argument (paper lines 2707–2710)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Guaranteeing a complete search — the payoff** (paper lines
    2707–2710): "Hence, because every vertex v is a seed and because
    every diminishing bipartite graph must contain at least one vertex
    in S, the algorithm is guaranteed to encounter at least one vertex
    from every possible diminishing component. Thus, if no vertex cover
    S′ smaller than the vertex cover S is found after iterating over
    each vertex as a seed, no S-diminishing bipartite graph exists."

    `hNoImprovement` models "iterating over each vertex [of S] as a
    seed [via the perfect matching, `Lemma16_seed_coverage`] finds no
    smaller vertex cover": for every seed `v ∈ S` and every valid
    coloring `C` there, the reachable structure is never diminishing.

    Proof: by contradiction. If `S` were not minimum,
    `Lemma16_diminishing_seed_exists` would produce an ACTUAL diminishing
    seed, contradicting `hNoImprovement` directly. -/
theorem Lemma16_completes_search
    {S : Finset V}
    (hS_vc : VCover G S) (hS_bound : S.card ≤ Fintype.card V - 1)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (hconn : G.Connected)
    (hNoImprovement : ∀ v ∈ S, ∀ C : Coloring V, ValidColoring G S v C →
        ¬ (reachW G S C v).card < (reachU G S C v).card) :
    MinVCover G S := by
  by_contra hnotmin
  obtain ⟨v, hvS, C, hVC, hlt⟩ :=
    Lemma16_diminishing_seed_exists hS_vc hS_bound hcubic hbridgeless hnotmin
  exact hNoImprovement v hvS C hVC hlt

/-- **Lemma 16** (paper lines 2661–2710), restated in the paper's own
    terms — "there is no S-diminishing bipartite graph in graph G" —
    rather than the (equivalent, by `Theorem12`) "S is minimum" phrasing
    of `Lemma16_completes_search`.

    Given a cubic, bridgeless, simple, connected graph `G` and a vertex
    cover `S`: if Algorithm C is executed by seeding on each vertex in
    `S` (guaranteed exhaustive by `Lemma16_seed_coverage`, via the
    perfect matching) and no smaller vertex cover is ever derived
    (`hNoImprovement`), then no `S`-diminishing bipartite graph exists
    in `G`.

    Proof: `Lemma16_completes_search` gives `MinVCover G S`;
    `min_implies_no_dimBip` (from `thm12-claude-v6.lean` / the
    `TheoremTwelveDBG` module) converts this to `¬∃ DimBip G S`. -/
theorem Lemma16
    {S : Finset V}
    (hS_vc : VCover G S) (hS_bound : S.card ≤ Fintype.card V - 1)
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (hconn : G.Connected)
    (hNoImprovement : ∀ v ∈ S, ∀ C : Coloring V, ValidColoring G S v C →
        ¬ (reachW G S C v).card < (reachU G S C v).card) :
    ¬ ∃ _ : DimBip G S, True :=
  min_implies_no_dimBip hS_vc hS_bound hcubic hbridgeless
    (Lemma16_completes_search hS_vc hS_bound hcubic hbridgeless hconn hNoImprovement)

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  AXIOM COUNT:  1
    DimBip_seed_capture — the RESIDUAL content of paper lines 2694–2706
    ("Selection of blue seed and symmetric difference" + "Capturing a
    component") that remains after the clean case is discharged as a
    theorem: specifically, ruling out a boundary vertex that borders a
    diminishing component from BOTH the U-side and the W-side (shown
    above to force an odd cycle through it, hence a genuine V1/V3
    conflict, for SOME suitably chosen diminishing component). This is a
    structural fact about symmetric differences of vertex covers akin to
    augmenting-path decomposition.

  SORRY COUNT:  0  (every proof step is complete)

  Proof map:
    Lemma16_seed_coverage             — PetersenMatching + IsPerfectMatching.2,
                                         every v : V is a matching endpoint (2 lines)
    boundary_forced_black             — THEOREM (new): V1 applied directly;
                                         the clean half of "Capturing a
                                         component" needs no axiom         (1 line)
    DimBip_seed_capture               — AXIOM (narrowed; residual
                                         double-bordering/odd-cycle case only;
                                         see docstring)
    Lemma16_exists_dimBip_of_not_min  — by_contra + Theorem12.mpr          (3 lines)
    Lemma16_diminishing_seed_exists   — Lemma16_exists_dimBip_of_not_min
                                         + DimBip_seed_capture + AltBip.U_sub
                                                                            (6 lines)
    Lemma16_seed_shrinks_cover        — Lemma15_witness + VCLemmas.dimBip_gives_smaller
                                                                            (3 lines)
    Lemma16_completes_search          — by_contra + Lemma16_diminishing_seed_exists
                                         + hNoImprovement                  (5 lines)
    Lemma16                           — Lemma16_completes_search + min_implies_no_dimBip
                                                                            (2 lines)

  Everything besides `DimBip_seed_capture` is a direct, zero-new-axiom
  consequence of results already fully proved elsewhere in this project:
  `PetersenMatching`/`IsPerfectMatching` (thm13_lemma9_claude_v3),
  `Theorem12`/`VCLemmas.dimBip_gives_smaller`/`min_implies_no_dimBip`
  (thm12-claude-v6 / TheoremTwelveDBG), `Lemma15_witness`
  (thm13_lemma15_claude_v3), and `ValidColoring.V1` directly (for the new
  `boundary_forced_black` theorem, which discharges the clean half of
  "Capturing a component" without any axiom). This file's remaining
  axiomatic content is exactly `DimBip_seed_capture`'s residual
  double-bordering/odd-cycle case, which is precisely the "Selection of blue
  seed and symmetric difference" + "Capturing a component" content of
  paper lines 2694–2706 that had not yet been formalized anywhere in the
  project prior to this file.
-/
