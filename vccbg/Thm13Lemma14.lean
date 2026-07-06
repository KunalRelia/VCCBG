/-
  Lean 4 / Mathlib — Lemma 14.

  "Given a cubic bridgeless graph G that is colored using Algorithm C
   and a vertex v from the vertex cover S, the resultant bipartite
   graph is an S-alternating bipartite graph."

  Source: paper §C.2.2, lines 2615–2631.

  ═══════════════════════════════════════════════════════════════════════════
  WHAT IMPORTED FILES PROVIDE
  ═══════════════════════════════════════════════════════════════════════════


    Color, Coloring, VCover, ValidColoring   — shared vocabulary
    AltReachActive G S C v w                 — active-walk reachability


    Lemma13_no_blue_blue   — no two adjacent vertices are both blue
    Lemma13_no_red_red     — no two adjacent vertices are both red


    BipSub G                — induced bipartite subgraph (U, W bipartition)
    AltBip G S               — Definition 24, S-alternating bipartite graph
                               (extends BipSub with U_sub : U ⊆ S and
                               W_disj : Disjoint W S)

  ═══════════════════════════════════════════════════════════════════════════
  THE MATHEMATICAL CONTENT OF LEMMA 14
  ═══════════════════════════════════════════════════════════════════════════

  Definition 24 (`AltBip`) requires a `BipSub` to ADDITIONALLY satisfy:
    U_sub  : U ⊆ S         (every U-vertex lies in the cover)
    W_disj : Disjoint W S   (no W-vertex lies in the cover)

  A SUBTLETY: these two conditions do NOT follow from the flat
  `ValidColoring` constraints V1–V4 alone (unlike Lemma 13's
  bipartiteness facts, which DO). V1–V4 only constrain a vertex's color
  GIVEN an already-colored NEIGHBOR; they say nothing about an isolated
  vertex's color in general. What Lemma 14 actually needs is the
  PROCEDURAL fact that every non-white vertex got its color through a
  *chain* of V1/V2/V3 applications starting at the seed `v` — i.e.
  exactly the `AltReachActive` reachability relation already built in
  `Lemma12_Part1_Bipartite`. So Lemma 14 is proved by an induction that
  mirrors `Lemma12_Part1`'s case structure exactly (refl / blue_step /
  red_step), concluding "blue → in S" / "red → not in S" instead of
  "C w = C₂ w".

  The bipartite-graph component itself ("U", "W" of Definition 24) is
  therefore taken to be the set of vertices REACHABLE from `v` via an
  active alternating walk that are blue (resp. red) — matching the
  paper's own framing: "we prove each lemma for one component of the
  induced bipartite graph" (line 2620).

  STRUCTURE:
    §1  `Lemma14_membership` — the per-vertex induction (the genuinely
        new content): for any `w` reachable from `v`,
        (C w = blue → w ∈ S) ∧ (C w = red → w ∉ S).
    §2  `reachU`, `reachW` — the Finsets of reachable blue/red vertices.
    §3  `Lemma14` — assembles a complete `AltBip G S` term, reusing
        `Lemma13_no_blue_blue` / `Lemma13_no_red_red` VERBATIM (via
        import) for the `noU`/`noW` fields, and `Lemma14_membership`
        for the new `U_sub`/`W_disj` fields.

  AXIOMS:   0
  SORRIES:  0
  ═══════════════════════════════════════════════════════════════════════════
-/

import Mathlib
/-
 Lean requires files to sit within an established workspace managed by Lake
 (Lean's build system) for imports to function correctly. Hence, please ensure
 that the following import statement is modified to follow the structure where
 the imported file sits within your project.
-/
import MyGraphProject.vccbg.Thm13Lemma13

open Color

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The new content: S-membership along an active walk
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 14 — core induction**:
    every vertex `w` reachable from `v` by an active alternating walk
    satisfies: if `w` ends up blue, `w ∈ S`; if `w` ends up red, `w ∉ S`.

    Paper (lines 2622–2630): "A seed vertex, which is colored blue, is
    always in the vertex cover S. ... a neighboring red vertex is not
    in S as it would be colored 'black' if it were in the vertex cover
    S. ... The neighbors of a red vertex must be in the given vertex
    cover and be colored blue."

    Proof: induction on `AltReachActive` (imported from
    `Lemma12_Part1_Bipartite`), mirroring `Lemma12_Part1`'s case
    structure exactly.
    • `refl`: `w = v`; `w ∈ S` is given directly by hypothesis `hv`.
    • `blue_step` (predecessor `u` blue, `u ∈ S` by IH): case on `w ∈ S`.
        – `w ∈ S` → V1 forces `black`; so any hypothetical `C w = red`
          contradicts (black ≠ red), making "`red → ∉S`" vacuous, while
          "`blue → ∈S`" holds directly since `w ∈ S` is the case
          hypothesis.
        – `w ∉ S` → V2 forces `red`; symmetric reasoning.
    • `red_step` (predecessor `u` red, `u ∉ S` by IH): V4 forces
      `w ∈ S` (else immediate False); V3 then forces `C w = blue`. -/
theorem Lemma14_membership
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C) (hv : v ∈ S) :
    ∀ {w : V}, AltReachActive G S C v w →
      (C w = blue → w ∈ S) ∧ (C w = red → w ∉ S) := by
  intro w hreach
  induction hreach with
  | refl =>
      refine ⟨fun _ => hv, fun hCred => ?_⟩
      have := hVC.seed
      rw [this] at hCred
      exact absurd hCred (by decide)
  | @blue_step u w hprev hadj hCu ih =>
      have huS : u ∈ S := ih.1 hCu
      by_cases hwS : w ∈ S
      · have hblack : C w = black := hVC.V1 hadj hCu hwS
        refine ⟨fun _ => hwS, fun hCred => ?_⟩
        rw [hCred] at hblack
        exact absurd hblack (by decide)
      · have hred : C w = red := hVC.V2 hadj hCu hwS
        refine ⟨fun hCblue => ?_, fun _ => hwS⟩
        rw [hCblue] at hred
        exact absurd hred (by decide)
  | @red_step u w hprev hadj hCu ih =>
      have huS : u ∉ S := ih.2 hCu
      have hwS : w ∈ S := by
        by_contra hwS'
        exact hVC.V4 hadj hCu hwS'
      have hblue : C w = blue := hVC.V3 hadj hCu hwS
      refine ⟨fun _ => hwS, fun hCred => ?_⟩
      rw [hCred] at hblue
      exact absurd hblue (by decide)

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The reachable blue/red Finsets
-- ═══════════════════════════════════════════════════════════════════════════
open Classical in
/-- The Finset of vertices reachable from `v` (via an active walk) that
    are colored blue — the "U" set of Definition 24. -/
noncomputable def reachU (G : SimpleGraph V) (S : Finset V) (C : Coloring V)
    (v : V) : Finset V :=
  Finset.univ.filter (fun w => AltReachActive G S C v w ∧ C w = blue)

open Classical in
/-- The Finset of vertices reachable from `v` (via an active walk) that
    are colored red — the "W" set of Definition 24. -/
noncomputable def reachW (G : SimpleGraph V) (S : Finset V) (C : Coloring V)
    (v : V) : Finset V :=
  Finset.univ.filter (fun w => AltReachActive G S C v w ∧ C w = red)

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Lemma 14 — the complete S-alternating bipartite graph
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 14**: the bipartite graph induced by Algorithm C's coloring
    (restricted to the component reachable from the seed `v`) is an
    S-alternating bipartite graph, in the precise sense of Definition 24
    (`AltBip`, imported from `Theorem12_DiminishingBipartiteGraph`).

    Paper: "Overall, we have: 1. a set U of blue vertices. It satisfies
    the first condition stated in Definition 24: U ⊆ S. 2. a set V of
    red vertices. It satisfies the second and the only remaining
    condition stated in Definition 24: V ∩ S = ∅. Thus, we can conclude
    that the induced bipartite graph is an S-alternating bipartite
    graph."

    NOTE on declaration kind: `AltBip G S` is Type-valued (its parent
    `BipSub` carries data fields `U W : Finset V`, not just proofs), so
    it cannot be the conclusion of a `theorem` directly. We therefore
    split this into two declarations:
    `Lemma14_witness` (`def`) constructs the explicit `AltBip` term;
    `Lemma14` (`theorem`, below) wraps that witness in an existential —
    `∃ A : AltBip G S, ...` is Prop-valued regardless of the witness
    type — restoring the SAME declaration kind (`theorem`) that
    `Lemma13` uses for its (Prop-valued) bipartiteness conclusion, since
    both lemmas assert structurally the same kind of claim about the
    same coloring. -/
noncomputable def Lemma14_witness
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C) (hv : v ∈ S) :
    AltBip G S where
  toBipSub :=
  { U := reachU G S C v
    W := reachW G S C v
    disj := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      rw [hx.2] at hx'
      exact absurd hx'.2 (by decide)
    noU := by
      intro u w hadj hu hw
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
      exact Lemma13_no_blue_blue hVC hadj hu.2 hw.2
    noW := by
      intro u w hadj hu hw
      simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
      exact Lemma13_no_red_red hVC hadj hu.2 hw.2
    cross := by
      intro u w hadj hu hwUW
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases Finset.mem_union.mp hwUW with hwU | hwW
      · simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hwU
        exact absurd hwU.2 (fun hCwb => Lemma13_no_blue_blue hVC hadj hu.2 hCwb)
      · exact hwW }
  U_sub := by
    intro x hx
    simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact (Lemma14_membership hVC hv hx.1).1 hx.2
  W_disj := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact (Lemma14_membership hVC hv hx.1).2 hx.2

/-- **Lemma 14** (theorem form): the bipartite graph induced by
    Algorithm C's coloring, restricted to the component reachable from
    the seed `v`, IS an S-alternating bipartite graph — i.e. an `AltBip
    G S` exists whose `U`/`W` are exactly the reachable blue/red
    vertices.

    This is the Prop-valued statement of Lemma 14, mirroring exactly how
    `Theorem12` itself states facts about its own Type-valued `DimBip`
    (e.g. `MinVCover G S ↔ ¬ ∃ _ : DimBip G S, True`): the witness
    `AltBip` term lives in `Type`, but wrapping it in `∃` produces a
    genuine `Prop`, since `Exists` is Prop-valued regardless of the
    witness's own universe. This restores `Lemma14` to a `theorem` —
    the same declaration kind as `Lemma13` — for what is conceptually
    the same kind of claim (Lemma 13: bipartite; Lemma 14: alternating
    bipartite) about the same coloring. -/
theorem Lemma14
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C) (hv : v ∈ S) :
    ∃ A : AltBip G S,
      A.toBipSub.U = reachU G S C v ∧ A.toBipSub.W = reachW G S C v :=
  ⟨Lemma14_witness hVC hv, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  AXIOM COUNT:  0
  SORRY COUNT:  0  (every proof step is complete)

  Proof map:
    Lemma14_membership — induction on (imported) AltReachActive,
                          mirroring Lemma12_Part1's case structure
                          exactly, deriving S-membership facts instead
                          of color-equality facts.                 (~25 lines)
    reachU, reachW      — Finset.univ.filter over the reachability ∧
                          color predicate (`open Classical in`, scoped
                          to each definition only — no blanket
                          `open Classical` for the whole file)
    Lemma14_witness     — `def` (not `theorem`): assembles a complete
                          (imported) AltBip G S term with explicit
                          U := reachU, W := reachW:
                            disj/noU/noW/cross — reuse (imported)
                              Lemma13_no_blue_blue / Lemma13_no_red_red
                              directly, no new color-clash reasoning
                            U_sub/W_disj — directly from
                              Lemma14_membership
    Lemma14             — `theorem`: wraps `Lemma14_witness` in
                          `∃ A : AltBip G S, A.toBipSub.U = reachU ... ∧
                          A.toBipSub.W = reachW ...`, both equalities
                          closed by `rfl`. Restores `theorem` status —
                          matching `Lemma13`'s declaration kind for the
                          analogous claim — since `Exists` is always
                          Prop-valued even though its witness type
                          (`AltBip G S`) is not.

  The genuinely new mathematical content of Lemma 14, beyond what the
  imported file already establishes, is exactly
  `Lemma14_membership`: the fact that "blue ⊆ S" and "red ∩ S = ∅"
  require tracking HOW a vertex came to be colored (via the active-walk
  reachability relation), not merely the flat forcing rules V1–V4. This
  distinguishes Lemma 14 from Lemma 13, whose two claims (no blue-blue,
  no red-red) follow directly from V1–V4 with no reachability argument
  at all.
-/
