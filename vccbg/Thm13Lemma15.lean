/-
  Lean 4 / Mathlib — Lemma 15, assuming the prior files are imported.

  "Given an alternating bipartite graph w.r.t. S, then the
   S-alternating bipartite graph is an S-diminishing bipartite graph if
   the S-alternating bipartite graph consists of a higher number of
   blue vertices than the number of red vertices."

  Source: paper §C.2.2, lines 2636–2656.

  ═══════════════════════════════════════════════════════════════════════════
  THE NATURAL PROGRESSION
  ═══════════════════════════════════════════════════════════════════════════

  Lemma 13  →  the coloring's blue/red vertices form a BIPARTITE graph
              (`BipSub`: no edges within a color class).
  Lemma 14  →  that bipartite graph is S-ALTERNATING
              (`AltBip`: additionally `U ⊆ S` and `Disjoint W S`).
  Lemma 15  →  when `|W| < |U|`, it is S-DIMINISHING
              (`DimBip`, Theorem 12's Definition 25: additionally
              `U.Nonempty`, `W.card < U.card`, and the FLIP
              `(S \ U) ∪ W` is itself a vertex cover, smaller than `S`).

  Each step ADDS exactly the fields Definition 24/25 add on top of the
  previous structure — DimBip literally `extends AltBip`. This file
  proves the three NEW fields DimBip adds beyond AltBip, reusing
  `Lemma14_witness`'s concrete `U := reachU`, `W := reachW` construction
  (NOT an abstract/generic AltBip) — abstracting away to an arbitrary
  AltBip loses exactly the information the third field (`flip_vc`)
  needs: that every reachable vertex's color was *forced* by
  `ValidColoring`'s rules along an active walk from `v`, not merely that
  `U`, `W` happen to satisfy the bipartite/alternating axioms in the
  abstract.

  ═══════════════════════════════════════════════════════════════════════════
  THE MATHEMATICAL CONTENT OF LEMMA 15
  ═══════════════════════════════════════════════════════════════════════════

  Given `hVC : ValidColoring G S v C`, `hv : v ∈ S`, `hS : VCover G S`,
  and `hgt : (reachW G S C v).card < (reachU G S C v).card` (the "more
  blue than red" hypothesis), we upgrade `Lemma14_witness hVC hv` (an
  `AltBip G S`) to a full `DimBip G S` by proving:

  (1) `U_ne` — `v ∈ reachU G S C v` directly: `v` is reachable from
      itself (`AltReachActive.refl`) and `C v = blue` (`hVC.seed`).
      [Paper: "the seed vertex... is colored blue because it is in S...
      G' contains at least one vertex from S."]

  (2) `U_gt_W` — exactly the hypothesis `hgt`, passed straight through.
      [Paper: "the size of the set of vertices U is greater than the
      size of the set of vertices V."]

  (3) `flip_vc` — `VCover G ((S \ reachU G S C v) ∪ reachW G S C v)`.
      For any edge `(a, b)`, `VCover G S` gives `a ∈ S` or `b ∈ S`
      (handle symmetrically). Say `a ∈ S`:
        • if `a ∉ U`, then `a ∈ S \ U` directly — done.
        • if `a ∈ U` (so `C a = blue`, reachable), case on `b ∈ S`:
            - `b ∈ S` → V1 forces `C b = black` → `b ∉ U` → `b ∈ S \ U`.
            - `b ∉ S` → V2 forces `C b = red`; and `b` is reachable via
              `AltReachActive.blue_step` from `a` → `b ∈ W`.
      [Paper: "when the blue vertices are removed, and red vertices
      added to S... the resultant set is a vertex cover of smaller
      size."]

  AXIOMS:   0
  SORRIES:  0
  ═══════════════════════════════════════════════════════════════════════════
-/

import Mathlib
/-
 Lean requires files to sit within an established workspace managed by Lake
 (Lean's build system) for imports to function correctly. Hence, please ensure
 that the following import statement is modified to follow the structure where
 the file being imported sits within your project.
-/
import MyGraphProject.vccbg.Thm13Lemma14

open Color

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The new field: U_ne (the seed witnesses U's nonemptiness)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 15, field (1)**: `v` itself lies in `reachU G S C v`.

    Paper: "the seed vertex selected by the loop... is colored blue
    because it is in the given vertex cover S... It satisfies the first
    condition stated in Definition 25: G' contains at least one vertex
    from S." -/
theorem Lemma15_U_ne
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C) :
    v ∈ reachU G S C v := by
  simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨AltReachActive.refl, hVC.seed⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The new field: flip_vc (the swap is a smaller vertex cover)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 15, field (3)**: `(S \ reachU G S C v) ∪ reachW G S C v` is a
    vertex cover.

    Paper: "when the blue vertices are removed, and red vertices added
    to S (Line 19 of Algorithm B), the resultant set is a vertex cover
    of a smaller size."

    Proof: for any edge `(a, b)`, `VCover G S` puts at least one
    endpoint in `S`. If that endpoint is not in `U`, it lies in `S \ U`
    directly. If it IS in `U` (hence blue and reachable), the other
    endpoint's color is forced by V1/V2 of `ValidColoring`, landing it
    either in `S \ U` (if it is itself in `S`, forced black) or in `W`
    (if not in `S`, forced red — and reachable via `blue_step`). -/
theorem Lemma15_flip_vc
    {S : Finset V} {v : V} {C : Coloring V}
    (hS : VCover G S) (hVC : ValidColoring G S v C) :
    VCover G ((S \ reachU G S C v) ∪ reachW G S C v) := by
  intro a b hadj
  rcases hS hadj with haS | hbS
  · -- a ∈ S
    by_cases haU : a ∈ reachU G S C v
    · -- a ∈ U: a is blue and reachable; determine b's color
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at haU
      obtain ⟨hreach_a, hCa⟩ := haU
      by_cases hbS' : b ∈ S
      · -- b ∈ S: V1 forces black, so b ∉ U, hence b ∈ S \ U
        have hCb : C b = black := hVC.V1 hadj hCa hbS'
        have hbU : b ∉ reachU G S C v := by
          simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and]
          intro ⟨_, hCb'⟩
          rw [hCb] at hCb'
          exact absurd hCb' (by decide)
        exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hbS', hbU⟩))
      · -- b ∉ S: V2 forces red; b is reachable via blue_step
        have hCb : C b = red := hVC.V2 hadj hCa hbS'
        have hreach_b : AltReachActive G S C v b :=
          AltReachActive.blue_step hreach_a hadj hCa
        have hbW : b ∈ reachW G S C v := by
          simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hreach_b, hCb⟩
        exact Or.inr (Finset.mem_union_right _ hbW)
    · -- a ∉ U: a ∈ S \ U directly
      exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haS, haU⟩))
  · -- b ∈ S (symmetric)
    by_cases hbU : b ∈ reachU G S C v
    · simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hbU
      obtain ⟨hreach_b, hCb⟩ := hbU
      have hadj' : G.Adj b a := hadj.symm
      by_cases haS' : a ∈ S
      · have hCa : C a = black := hVC.V1 hadj' hCb haS'
        have haU : a ∉ reachU G S C v := by
          simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and]
          intro ⟨_, hCa'⟩
          rw [hCa] at hCa'
          exact absurd hCa' (by decide)
        exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haS', haU⟩))
      · have hCa : C a = red := hVC.V2 hadj' hCb haS'
        have hreach_a : AltReachActive G S C v a :=
          AltReachActive.blue_step hreach_b hadj' hCb
        have haW : a ∈ reachW G S C v := by
          simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hreach_a, hCa⟩
        exact Or.inl (Finset.mem_union_right _ haW)
    · -- b ∉ U: b ∈ S \ U directly
      exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hbS, hbU⟩))

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Lemma 15 — assembling the complete DimBip
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 15**: an `AltBip` with more blue than red vertices upgrades
    to a full `DimBip` (Definition 25).

    Combines `Lemma14_witness` (the concrete `AltBip` with
    `U := reachU`, `W := reachW`) with the three new fields proved above. -/
noncomputable def Lemma15_witness
    {S : Finset V} {v : V} {C : Coloring V}
    (hS : VCover G S) (hVC : ValidColoring G S v C) (hv : v ∈ S)
    (hgt : (reachW G S C v).card < (reachU G S C v).card) :
    DimBip G S where
  toAltBip := Lemma14_witness hVC hv
  U_ne    := ⟨v, Lemma15_U_ne hVC⟩
  U_gt_W  := hgt
  flip_vc := Lemma15_flip_vc hS hVC

/-- **Lemma 15** (theorem form), matching `Lemma14`'s style: wraps the
    witness in an existential, restoring `theorem` status. -/
theorem Lemma15
    {S : Finset V} {v : V} {C : Coloring V}
    (hS : VCover G S) (hVC : ValidColoring G S v C) (hv : v ∈ S)
    (hgt : (reachW G S C v).card < (reachU G S C v).card) :
    ∃ D : DimBip G S,
      D.toAltBip.toBipSub.U = reachU G S C v ∧
      D.toAltBip.toBipSub.W = reachW G S C v :=
  ⟨Lemma15_witness hS hVC hv hgt, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  AXIOM COUNT:  0
  SORRY COUNT:  0  (every proof step is complete)

  Proof map:
    Lemma15_U_ne     — v ∈ reachU directly: AltReachActive.refl + hVC.seed
                       (≈3 lines)
    Lemma15_flip_vc  — case split on which VCover-guaranteed endpoint is
                       in S, then on whether that endpoint is in U;
                       V1/V2 determine the other endpoint's color when
                       needed, AltReachActive.blue_step propagates
                       reachability.                              (≈45 lines)
    Lemma15_witness  — `noncomputable def` (DimBip is Type-valued, like
                       AltBip): assembles toAltBip (from Lemma14_witness)
                       plus the three new fields above.
    Lemma15          — `theorem`: wraps the witness in an existential,
                       both projection equalities closed by `rfl`,
                       matching Lemma13's and Lemma14's declaration kind
                       for the analogous claim.

  This completes the natural progression Lemma 13 → Lemma 14 →
  Lemma 15: each step adds exactly the fields its Definition (24 then
  25) adds on top of the previous structure, reusing the SAME concrete
  `reachU`/`reachW` construction throughout rather than abstracting to
  a generic bipartite/alternating graph — which is essential for
  `flip_vc`, since that field genuinely needs the procedural fact that
  every reachable vertex's color was forced along an active walk from
  `v`, not merely that some abstract `U`, `W` happen to satisfy the
  bipartite/alternating axioms.
-/
