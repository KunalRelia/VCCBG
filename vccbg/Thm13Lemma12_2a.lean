/-
  Lean 4 / Mathlib — Lemma 12, Part 2(a)
  "When a black vertex is not in an odd cycle"

  Source: paper §C.2.2, lines 2527–2545.

  ═══════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE PROVES
  ═══════════════════════════════════════════════════════════════════════════

  Setup recalled from Part 1: a blue vertex v has its neighbors forced by
  the rules
    (V1) neighbor w ∈ S  → colored black
    (V2) neighbor w ∉ S  → colored red

  Part 2(a) studies what happens at a black vertex that is NOT part of an
  odd cycle — i.e. a black vertex that arises purely from the STRUCTURAL
  fact that G is cubic (every vertex has exactly 3 neighbors) together
  with the partition of v's neighborhood into S / not-S, rather than from
  a genuine odd-cycle conflict (that is Part 2(b), a separate file).

  The paper enumerates three textual sub-cases, according to how many of
  v's three neighbors lie in S:
    (i)   exactly 1 neighbor in S  → 1 black, 2 red
    (ii)  exactly 2 neighbors in S → 2 black, 1 red
    (iii) all 3 neighbors in S     → 3 black, 0 red
  (The remaining case, 0 neighbors in S, is the bipartite case of Part 1.)

  The mathematical content is that V1/V2, applied independently to each of
  v's (at most 3) neighbors, never conflict with each other — coloring
  several neighbors black simultaneously introduces no extra freedom or
  contradiction. We prove this as ONE uniform theorem covering all three
  textual sub-cases, then state (i)-(iii) explicitly as corollaries to
  match the paper's structure, and finally restate the Part-1-style
  uniqueness conclusion for v's whole neighborhood.

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
import MyGraphProject.vccbg.Thm13Lemma12_1


set_option linter.style.openClassical false

open Classical   -- discharges all Decidable / DecidablePred obligations
                  -- on G.Adj-based predicates non-constructively

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false


variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Colors, vertex cover, valid colorings (importeed from Part 1)
-- ═══════════════════════════════════════════════════════════════════════════

open Color

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The neighborhood split: black neighbors vs red neighbors of a blue v
--     Defined via Finset.univ.filter under `open Classical`.
-- ═══════════════════════════════════════════════════════════════════════════

/-- All neighbors of `v` (as a Finset). -/
noncomputable def nbrs (G : SimpleGraph V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w)

/-- The neighbors of `v` that lie in `S` (forced to black by V1). -/
noncomputable def blackNbrs (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w ∧ w ∈ S)

/-- The neighbors of `v` that do not lie in `S` (forced to red by V2). -/
noncomputable def redNbrs (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w ∧ w ∉ S)

/-- `blackNbrs` and `redNbrs` partition `v`'s neighborhood: every neighbor
    is in exactly one of the two sets. -/
theorem blackNbrs_union_redNbrs (S : Finset V) (v : V) :
    blackNbrs G S v ∪ redNbrs G S v = nbrs G v := by
  unfold blackNbrs redNbrs nbrs
  ext w
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- `blackNbrs` and `redNbrs` are disjoint: no neighbor is both in `S` and
    not in `S`. -/
theorem blackNbrs_disjoint_redNbrs (S : Finset V) (v : V) :
    Disjoint (blackNbrs G S v) (redNbrs G S v) := by
  unfold blackNbrs redNbrs
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hw'.2 hw.2

/-- The two parts add up to the full neighbor count:
    `|blackNbrs| + |redNbrs| = |nbrs|`. -/
theorem card_blackNbrs_add_redNbrs (S : Finset V) (v : V) :
    (blackNbrs G S v).card + (redNbrs G S v).card = (nbrs G v).card := by
  rw [← Finset.card_union_of_disjoint (blackNbrs_disjoint_redNbrs (G := G) S v),
      blackNbrs_union_redNbrs]

/-- **Cubic specialization**: when `v` has exactly 3 neighbors, the
    black/red split of `v`'s neighborhood sums to exactly 3. This is the
    structural fact underlying the paper's three numbered sub-cases
    (i)/(ii)/(iii). -/
theorem card_blackNbrs_add_redNbrs_cubic
    {v : V} (hcubic : (nbrs G v).card = 3) (S : Finset V) :
    (blackNbrs G S v).card + (redNbrs G S v).card = 3 := by
  rw [card_blackNbrs_add_redNbrs]; exact hcubic

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. The forcing rules applied to the whole neighborhood at once
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Main forcing theorem (Part 2(a))**:
    Given a blue vertex `v`, every neighbor in `blackNbrs` is colored black
    and every neighbor in `redNbrs` is colored red — REGARDLESS of how many
    neighbors fall into each part. No conflict ever arises from coloring
    several neighbors black simultaneously: each application of V1 (resp.
    V2) is independent of the others.

    Paper (lines 2530–2545): cases (i), (ii), (iii) are simply the
    instances of this single uniform statement for `|blackNbrs| = 1, 2, 3`. -/
theorem Lemma12_Part2a_forcing
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C) (hCv : C v = blue) :
    (∀ w ∈ blackNbrs G S v, C w = black) ∧
    (∀ w ∈ redNbrs G S v, C w = red) := by
  constructor
  · intro w hw
    simp only [blackNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact hVC.V1 hw.1 hCv hw.2
  · intro w hw
    simp only [redNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact hVC.V2 hw.1 hCv hw.2

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. The three named sub-cases of the paper
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Case (i)**: exactly one neighbor of `v` lies in `S`.
    Then exactly that one neighbor is colored black, and the other two
    (forced by cubic degree 3) are colored red.

    Paper: "When one neighbor of the given vertex v is colored black, it
    implies the other two neighbors... are colored red... Hence, this
    will be a unique coloring." -/
theorem Lemma12_Part2a_case_i
    {v : V} (hcubic : (nbrs G v).card = 3)
    {S : Finset V} {C : Coloring V}
    (hVC : ValidColoring G S v C) (hCv : C v = blue)
    (h1 : (blackNbrs G S v).card = 1) :
    (redNbrs G S v).card = 2 ∧
    (∀ w ∈ blackNbrs G S v, C w = black) ∧
    (∀ w ∈ redNbrs G S v, C w = red) := by
  have hsum := card_blackNbrs_add_redNbrs_cubic hcubic S
  obtain ⟨hblack, hred⟩ := Lemma12_Part2a_forcing hVC hCv
  exact ⟨by omega, hblack, hred⟩

/-- **Case (ii)**: exactly two neighbors of `v` lie in `S`.
    Then exactly those two neighbors are colored black, and the remaining
    one (forced by cubic degree 3) is colored red.

    Paper: "When two neighbors of the given vertex v are colored black, it
    implies the remaining neighbor... is colored red. Hence, this will be
    a unique coloring." -/
theorem Lemma12_Part2a_case_ii
    {v : V} (hcubic : (nbrs G v).card = 3)
    {S : Finset V} {C : Coloring V}
    (hVC : ValidColoring G S v C) (hCv : C v = blue)
    (h2 : (blackNbrs G S v).card = 2) :
    (redNbrs G S v).card = 1 ∧
    (∀ w ∈ blackNbrs G S v, C w = black) ∧
    (∀ w ∈ redNbrs G S v, C w = red) := by
  have hsum := card_blackNbrs_add_redNbrs_cubic hcubic S
  obtain ⟨hblack, hred⟩ := Lemma12_Part2a_forcing hVC hCv
  exact ⟨by omega, hblack, hred⟩

/-- **Case (iii)**: all three neighbors of `v` lie in `S`.
    Then all three are colored black, and there are no red neighbors.

    Paper: "This case is unique because the given vertex v is in the given
    vertex cover S and is surrounded by all... vertices that are also in
    the given vertex cover S. There can be no other way to color the
    graph." -/
theorem Lemma12_Part2a_case_iii
    {v : V} (hcubic : (nbrs G v).card = 3)
    {S : Finset V} {C : Coloring V}
    (hVC : ValidColoring G S v C) (hCv : C v = blue)
    (h3 : (blackNbrs G S v).card = 3) :
    (redNbrs G S v).card = 0 ∧
    (∀ w ∈ blackNbrs G S v, C w = black) := by
  have hsum := card_blackNbrs_add_redNbrs_cubic hcubic S
  obtain ⟨hblack, _⟩ := Lemma12_Part2a_forcing hVC hCv
  exact ⟨by omega, hblack⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Uniqueness across the whole neighborhood (any two valid colorings agree)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Uniqueness for Part 2(a)**: any two valid colorings (both seeded by
    the SAME blue vertex `v`) assign IDENTICAL colors to every neighbor of
    `v`, no matter how the neighborhood splits between black and red.

    Paper: "Hence, this will be a unique coloring" — stated for each of
    cases (i), (ii), (iii) individually; this theorem subsumes all three
    (and the bipartite case |blackNbrs| = 0) in one statement, since the
    forcing rules V1/V2 do not depend on how many neighbors precede or
    follow in S-membership — only on the membership of EACH neighbor
    individually. -/
theorem Lemma12_Part2a_unique
    {S : Finset V} {v : V} {C₁ C₂ : Coloring V}
    (hVC₁ : ValidColoring G S v C₁) (hVC₂ : ValidColoring G S v C₂)
    (hC₁v : C₁ v = blue) (hC₂v : C₂ v = blue) :
    ∀ w ∈ nbrs G v, C₁ w = C₂ w := by
  intro w hw
  simp only [nbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  by_cases hwS : w ∈ S
  · rw [hVC₁.V1 hw hC₁v hwS, hVC₂.V1 hw hC₂v hwS]
  · rw [hVC₁.V2 hw hC₁v hwS, hVC₂.V2 hw hC₂v hwS]

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  AXIOM COUNT:  0
  SORRY COUNT:  0  (every proof step is complete)

  Proof map:
    blackNbrs_union_redNbrs        — ext + Finset.mem_filter + tauto    (4 lines)
    blackNbrs_disjoint_redNbrs     — Finset.disjoint_left unfold        (5 lines)
    card_blackNbrs_add_redNbrs     — card_union_of_disjoint             (2 lines)
    card_blackNbrs_add_redNbrs_cubic — direct rewrite with hcubic       (1 line)
    Lemma12_Part2a_forcing         — V1 / V2 applied per-neighbor       (8 lines)
    Lemma12_Part2a_case_i/ii/iii   — omega on the cubic sum + forcing   (5 lines each)
    Lemma12_Part2a_unique          — case split on w ∈ S, V1/V2 in both (6 lines)

  This file establishes that the THREE numbered textual cases in the
  paper's Part 2(a) are all instances of a single uniform fact: applying
  V1 and V2 independently to each neighbor of a cubic blue vertex `v` is
  always consistent, regardless of how many of `v`'s three neighbors lie
  in S. No conflict, no extra freedom, no case-specific argument is
  actually needed beyond the cubic-degree counting identity
  `|blackNbrs| + |redNbrs| = 3`, which is what distinguishes Part 2(a)
  ("not in an odd cycle") from Part 2(b), where an odd cycle forces a
  genuine conflict requiring a different vertex to be selected as black.
-/
