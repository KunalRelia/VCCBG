/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 12, Part 2(a)

  "When a black vertex is not in an odd cycle"

  Source: paper §C.2.2, lines 2527–2545.
-/


public import VCCBGSecC.thm13_lemma12_1

/-! setting linters. -/
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false

open Classical   -- discharges all Decidable / DecidablePred obligations
                  -- on G.Adj-based predicates non-constructively

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false


variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Colors, vertex cover, valid colorings (imported)
-- ═══════════════════════════════════════════════════════════════════════════

open Color

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The neighborhood split: black neighbors vs red neighbors of a blue v
--     Defined via Finset.univ.filter under `open Classical`.
-- ═══════════════════════════════════════════════════════════════════════════

/-- All neighbors of `v` (as a Finset). -/
public noncomputable def nbrs (G : SimpleGraph V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w)

/-- The neighbors of `v` that lie in `S` (forced to black, unconditionally
    — see this file's header for why the `blue` possibility is ruled
    out for the seed's own direct neighbors). -/
public noncomputable def blackNbrs (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w ∧ w ∈ S)

/-- The neighbors of `v` that do not lie in `S` (forced to red). -/
public noncomputable def redNbrs (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w ∧ w ∉ S)

/-- `blackNbrs` and `redNbrs` partition `v`'s neighborhood. -/
public theorem blackNbrs_union_redNbrs (S : Finset V) (v : V) :
    blackNbrs G S v ∪ redNbrs G S v = nbrs G v := by
  unfold blackNbrs redNbrs nbrs
  ext w
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- `blackNbrs` and `redNbrs` are disjoint. -/
public theorem blackNbrs_disjoint_redNbrs (S : Finset V) (v : V) :
    Disjoint (blackNbrs G S v) (redNbrs G S v) := by
  unfold blackNbrs redNbrs
  rw [Finset.disjoint_left]
  intro w hw hw'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
  exact hw'.2 hw.2

/-- The two parts add up to the full neighbor count. -/
public theorem card_blackNbrs_add_redNbrs (S : Finset V) (v : V) :
    (blackNbrs G S v).card + (redNbrs G S v).card = (nbrs G v).card := by
  rw [← Finset.card_union_of_disjoint (blackNbrs_disjoint_redNbrs (G := G) S v),
      blackNbrs_union_redNbrs]

/-- **Cubic specialization**: when `v` has exactly 3 neighbors, the
    black/red split sums to exactly 3. -/
public theorem card_blackNbrs_add_redNbrs_cubic
    {v : V} (hcubic : (nbrs G v).card = 3) (S : Finset V) :
    (blackNbrs G S v).card + (redNbrs G S v).card = 3 := by
  rw [card_blackNbrs_add_redNbrs]; exact hcubic

-- ═══════════════════════════════════════════════════════════════════════════
-- §2.5. Bridging hypothesis: `nbrOrder` faithfully enumerates `G.Adj`.
--       UNCHANGED from v5.
-- ═══════════════════════════════════════════════════════════════════════════

/-- The natural well-formedness condition tying the algorithmic traversal
    order `nbrOrder` to the actual graph adjacency `G.Adj`. -/
public abbrev OrderMatchesAdj (G : SimpleGraph V) (nbrOrder : V → List V) : Prop :=
  ∀ x y, y ∈ nbrOrder x ↔ G.Adj x y

/-- `OrderMatchesAdj` implies the `hirrefl` fact needed by every theorem
    in `thm13_lemma12_1`. -/
public theorem OrderMatchesAdj.irrefl
    {nbrOrder : V → List V} (h : OrderMatchesAdj G nbrOrder) :
    ∀ x y, y ∈ nbrOrder x → y ≠ x := by
  intro x y hy heq
  subst heq
  exact G.loopless.irrefl y ((h y y).mp hy)
-- ═══════════════════════════════════════════════════════════════════════════
-- §2.6. yellow-or-black is a forward-preserved invariant under ANY further
--       `AlgC` processing, at any single vertex — the fact that lets us rule
--        out the `blue` disjunct for the seed's own `S`-neighbors.
--
--       Checked against every branch of `AlgC`: blue is ONLY ever
--       assigned by the red-branch's and black-branch's `u ∈ S ∧ white`
--       rules, both of which REQUIRE the target to currently be white.
--       A vertex that is currently yellow or black therefore can never
--       be freshly blued by the step that processes it; the only
--       transition available to a yellow vertex is yellow → black
--       (blue-branch's and red-branch's `u ∈ S ∧ yellow` rules), and
--       black is already absorbing (`AlgC_black_preserved`).
-- ═══════════════════════════════════════════════════════════════════════════

variable (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)

/-- **Yellow-or-black is preserved (never becomes blue)**: if a vertex
    `x` is currently `yellow` or `black`, then after ANY further amount
    of `AlgC` processing (any fuel, seed, or remaining neighbor list),
    `x` is still `yellow` or `black` — in particular, never `blue`. -/
public theorem AlgC_yellow_or_black_preserved (x : V) :
    ∀ n C v us, (C x = yellow ∨ C x = black) →
      (AlgC G S nbrOrder n C v us x = yellow ∨ AlgC G S nbrOrder n C v us x = black) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hx
    cases n with
    | zero => rw [AlgC_zero]; exact hx
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil]; exact hx
      | cons u rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u ∉ S ∧ C u = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1]
            have hxu : x ≠ u := by
              rintro rfl
              rcases hx with h | h <;> rw [hu1.2] at h <;> exact absurd h (by decide)
            set C1 := Function.update C u red with hC1def
            have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
            have hx1 : C1 x = yellow ∨ C1 x = black := by rw [hC1x]; exact hx
            set C2 := AlgC G S nbrOrder m C1 u (nbrOrder u) with hC2def
            have hx2 := ih m (by omega) C1 u (nbrOrder u) hx1
            exact ih m (by omega) C2 v rest hx2
          · by_cases hu2 : u ∈ S ∧ C u = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2]
              set C1 := Function.update C u black with hC1def
              have hx1 : C1 x = yellow ∨ C1 x = black := by
                by_cases hxu : x = u
                · right; rw [hC1def, hxu, Function.update_apply, ite_eq_left rfl]
                · rw [hC1def, Function.update_apply, ite_eq_right hxu]; exact hx
              set C2 := AlgC G S nbrOrder m C1 u (nbrOrder u) with hC2def
              have hx2 := ih m (by omega) C1 u (nbrOrder u) hx1
              exact ih m (by omega) C2 v rest hx2
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2]
              exact ih m (by omega) C v rest hx
        · by_cases hvr : C v = red
          · by_cases hu1 : u ∈ S ∧ C u = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu1]
              have hxu : x ≠ u := by
                rintro rfl
                rcases hx with h | h <;> rw [hu1.2] at h <;> exact absurd h (by decide)
              set C1 := Function.update C u blue with hC1def
              have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
              have hC1x_nonwhite : C1 x ≠ white := by
                rw [hC1x]; rcases hx with h | h <;> rw [h] <;> decide
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
              have hC1'x : C1' x = C1 x :=
                yellowRest_preserves_nonwhite S (nbrOrder u) C1 x hC1x_nonwhite
              have hx1 : C1' x = yellow ∨ C1' x = black := by
                rw [hC1'x, hC1x]; exact hx
              set C2 := AlgC G S nbrOrder m C1' u (nbrOrder u) with hC2def
              have hx2 := ih m (by omega) C1' u (nbrOrder u) hx1
              exact ih m (by omega) C2 v rest hx2
            · by_cases hu2 : u ∈ S ∧ C u = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu1 hu2]
                set C1 := Function.update C u black with hC1def
                have hx1 : C1 x = yellow ∨ C1 x = black := by
                  by_cases hxu : x = u
                  · right; rw [hC1def, hxu, Function.update_apply, ite_eq_left rfl]
                  · rw [hC1def, Function.update_apply, ite_eq_right hxu]; exact hx
                set C2 := AlgC G S nbrOrder m C1 u (nbrOrder u) with hC2def
                have hx2 := ih m (by omega) C1 u (nbrOrder u) hx1
                exact ih m (by omega) C2 v rest hx2
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu1 hu2]
                exact ih m (by omega) C v rest hx
          · by_cases hvk : C v = black
            · by_cases hu1 : u ∉ S ∧ C u = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu1]
                have hxu : x ≠ u := by
                  rintro rfl
                  rcases hx with h | h <;> rw [hu1.2] at h <;> exact absurd h (by decide)
                set C1 := Function.update C u red with hC1def
                have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
                have hx1 : C1 x = yellow ∨ C1 x = black := by rw [hC1x]; exact hx
                set C2 := AlgC G S nbrOrder m C1 u (nbrOrder u) with hC2def
                have hx2 := ih m (by omega) C1 u (nbrOrder u) hx1
                exact ih m (by omega) C2 v rest hx2
              · by_cases hu2 : u ∈ S ∧ C u = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu1 hu2]
                  have hxu : x ≠ u := by
                    rintro rfl
                    rcases hx with h | h <;> rw [hu2.2] at h <;> exact absurd h (by decide)
                  set C1 := Function.update C u blue with hC1def
                  have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
                  have hC1x_nonwhite : C1 x ≠ white := by
                    rw [hC1x]; rcases hx with h | h <;> rw [h] <;> decide
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
                  have hC1'x : C1' x = C1 x :=
                    yellowRest_preserves_nonwhite S (nbrOrder u) C1 x hC1x_nonwhite
                  have hx1 : C1' x = yellow ∨ C1' x = black := by
                    rw [hC1'x, hC1x]; exact hx
                  set C2 := AlgC G S nbrOrder m C1' u (nbrOrder u) with hC2def
                  have hx2 := ih m (by omega) C1' u (nbrOrder u) hx1
                  exact ih m (by omega) C2 v rest hx2
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu1 hu2]
                  exact ih m (by omega) C v rest hx
            · rw [AlgC_other G S nbrOrder hvb hvr hvk]
              exact ih m (by omega) C v rest hx

/-- **Corollary**: a vertex that is `yellow` (or `black`) at any point is
    NEVER `blue` after further processing. -/
public theorem AlgC_yellow_or_black_ne_blue (x : V) :
    ∀ n C v us, (C x = yellow ∨ C x = black) → AlgC G S nbrOrder n C v us x ≠ blue := by
  intro n C v us hx
  rcases AlgC_yellow_or_black_preserved G S nbrOrder x n C v us hx with h | h <;>
    rw [h] <;> decide

/-- **A seed's own direct `S`-neighbor is `yellow` immediately after
    `initColoring`**: this is exactly the side effect of the seed's own
    blue-assignment.

    Proof: before the fold, an `S`-neighbor `w ≠ v0` of the seed
    is `white`; the fold either leaves it `white` or turns it `yellow`
    (`yellowRest_white_stays_white_or_yellow`), and since `w` lies in
    `S` and in the very list being folded over, `yellowRest_resolves_own_list`
    guarantees it does NOT stay `white` — so it must be `yellow`. -/
public theorem initColoring_seed_Snbr_yellow
    {v0 w : V} (hwS : w ∈ S) (hw_nbr : w ∈ nbrOrder v0) (hwv0 : w ≠ v0) :
    initColoring G S nbrOrder v0 w = yellow := by
  unfold initColoring
  set C0 := Function.update (fun _ : V => white) v0 blue with hC0def
  have hC0w : C0 w = white := by
    rw [hC0def, Function.update_apply, ite_eq_right hwv0]
  rcases yellowRest_white_stays_white_or_yellow S (nbrOrder v0) C0 w hC0w with h | h
  · exact absurd h (yellowRest_resolves_own_list S (nbrOrder v0) C0 w hw_nbr hwS)
  · exact h

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. The forcing rules applied to the whole neighborhood at once,
--     re-derived from `runAlgC_seed_neighbors_resolved` (Lemma 12
--     Part 1) PLUS the yellow-or-black confinement machinery just
--     established, to restore the unconditional `black` conclusion.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Main forcing theorem (Part 2(a)), v6**:
    Given the SEED vertex `v` (`v ∈ S`) with `C` the actual output of
    running Algorithm C from `v`, every neighbor of `v` in `blackNbrs`
    is colored black — UNCONDITIONALLY, with no hypothesis needed about
    the seed's own eventual color — and every neighbor in `redNbrs` is
    colored red.

    Paper (lines 2530–2545): cases (i), (ii), (iii) are simply the
    instances of this single uniform statement for
    `|blackNbrs| = 1, 2, 3`.
-/
public theorem Lemma12_Part2a_forcing
    {S : Finset V} {v : V} (hvS : v ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v) (nbrOrder v) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v fuel C) :
    (∀ w ∈ blackNbrs G S v, C w = black) ∧
    (∀ w ∈ redNbrs G S v, C w = red) := by
  unfold ValidColoring at hVC
  have hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x := hOrder.irrefl
  have key := runAlgC_seed_neighbors_resolved G S nbrOrder hirrefl hlen hvS hfuel
  constructor
  · intro w hw
    simp only [blackNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hwOrder : w ∈ nbrOrder v := (hOrder v w).mpr hw.1
    have hwv : w ≠ v := hirrefl v w hwOrder
    have hwYellow : initColoring G S nbrOrder v w = yellow :=
      initColoring_seed_Snbr_yellow G S nbrOrder hw.2 hwOrder hwv
    have hne_blue : runAlgC G S nbrOrder fuel v w ≠ blue := by
      unfold runAlgC
      exact AlgC_yellow_or_black_ne_blue G S nbrOrder w fuel
        (initColoring G S nbrOrder v) v (nbrOrder v) (Or.inl hwYellow)
    have hbb := (key w hwOrder).1 hw.2
    have hresolved : runAlgC G S nbrOrder fuel v w = black := by
      rcases hbb with h | h
      · exact h
      · exact absurd h hne_blue
    rw [hVC]; exact hresolved
  · intro w hw
    simp only [redNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hwOrder : w ∈ nbrOrder v := (hOrder v w).mpr hw.1
    have := (key w hwOrder).2 hw.2
    rw [hVC]; exact this

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. The three named sub-cases of the paper — pure cardinality
--     arithmetic on top of the re-derived forcing fact.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Case (i)**: exactly one neighbor of `v` lies in `S`. -/
public theorem Lemma12_Part2a_case_i
    {v : V} (hcubic : (nbrs G v).card = 3)
    {S : Finset V} (hvS : v ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v) (nbrOrder v) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v fuel C)
    (h1 : (blackNbrs G S v).card = 1) :
    (redNbrs G S v).card = 2 ∧
    (∀ w ∈ blackNbrs G S v, C w = black) ∧
    (∀ w ∈ redNbrs G S v, C w = red) := by
  have hsum := card_blackNbrs_add_redNbrs_cubic hcubic S
  --#print Lemma12_Part2a_forcing
  obtain ⟨hblack, hred⟩ := Lemma12_Part2a_forcing
    (hvS := hvS)
    (hOrder := hOrder)
    (hlen := hlen)
    (hfuel := hfuel)
    (hVC := hVC) --hvS hOrder hlen hfuel hVC
  exact ⟨by omega, hblack, hred⟩

/-- **Case (ii)**: exactly two neighbors of `v` lie in `S`. -/
public theorem Lemma12_Part2a_case_ii
    {v : V} (hcubic : (nbrs G v).card = 3)
    {S : Finset V} (hvS : v ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v) (nbrOrder v) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v fuel C)
    (h2 : (blackNbrs G S v).card = 2) :
    (redNbrs G S v).card = 1 ∧
    (∀ w ∈ blackNbrs G S v, C w = black) ∧
    (∀ w ∈ redNbrs G S v, C w = red) := by
  have hsum := card_blackNbrs_add_redNbrs_cubic hcubic S
  obtain ⟨hblack, hred⟩ := Lemma12_Part2a_forcing
    (hvS := hvS)
    (hOrder := hOrder)
    (hlen := hlen)
    (hfuel := hfuel)
    (hVC := hVC)--hvS hOrder hlen hfuel hVC
  exact ⟨by omega, hblack, hred⟩

/-- **Case (iii)**: all three neighbors of `v` lie in `S`. -/
public theorem Lemma12_Part2a_case_iii
    {v : V} (hcubic : (nbrs G v).card = 3)
    {S : Finset V} (hvS : v ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v) (nbrOrder v) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v fuel C)
    (h3 : (blackNbrs G S v).card = 3) :
    (redNbrs G S v).card = 0 ∧
    (∀ w ∈ blackNbrs G S v, C w = black) := by
  have hsum := card_blackNbrs_add_redNbrs_cubic hcubic S
  obtain ⟨hblack, _⟩ := Lemma12_Part2a_forcing
    (hvS := hvS)
    (hOrder := hOrder)
    (hlen := hlen)
    (hfuel := hfuel)
    (hVC := hVC) --hvS hOrder hlen hfuel hVC
  exact ⟨by omega, hblack⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Uniqueness across the whole neighborhood — UNCHANGED from v5.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Uniqueness for Part 2(a)**: with `ValidColoring` DEFINED as
    `C = runAlgC G S nbrOrder fuel v`, "any two valid colorings for the
    SAME `(G, S, nbrOrder, v, fuel)` agree everywhere" is immediate from
    `Lemma12_Part1`. -/
public theorem Lemma12_Part2a_unique
    {S : Finset V} {v : V} {nbrOrder : V → List V} {fuel : ℕ}
    {C₁ C₂ : Coloring V}
    (hVC₁ : ValidColoring G S nbrOrder v fuel C₁)
    (hVC₂ : ValidColoring G S nbrOrder v fuel C₂) :
    ∀ w ∈ nbrs G v, C₁ w = C₂ w := by
  intro w _
  exact Lemma12_Part1_apply hVC₁ hVC₂ w

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Proof map:

    AlgC_yellow_or_black_preserved  — NEW: nine-branch strong induction
                                      on fuel, mirroring lemma12_1's own
                                      `AlgC_preserved_of_ne_white_yellow`
                                      case structure; shows {yellow,
                                      black} is forward-closed, since no
                                      branch ever re-blues a target that
                                      isn't currently white.
    AlgC_yellow_or_black_ne_blue    — one-line corollary via `decide`.
    initColoring_seed_Snbr_yellow   — NEW: an S-neighbor of the seed
                                      (≠ the seed itself) is exactly
                                      `yellow` right after
                                      `initColoring`, via
                                      `yellowRest_white_stays_white_or_yellow`
                                      + `yellowRest_resolves_own_list`
                                      (both lemma12_1 exports).
    Lemma12_Part2a_forcing          — combines
                                      `runAlgC_seed_neighbors_resolved`'s
                                      `black ∨ blue` bound with the above
                                      two facts to rule out `blue`,
                                      restoring the single, unconditional
                                      `C w = black` conclusion (no
                                      `hend` hypothesis needed).
    Lemma12_Part2a_case_i/ii/iii    — unchanged cardinality arithmetic
                                      via `omega`, now against the
                                      restored `black`-only conclusion.

  The file proves the paper's claim: applying the blue-vertex forcing rule
  independently to each of a cubic seed's (at most 3) neighbors never
  conflicts — every `S`-neighbor ends up black, every non-`S`-neighbor
  ends up red, unconditionally — grounded in the concrete recursive
  Algorithm C (`thm13_lemma12_1`) plus the new yellow-
  confinement lemma needed to rule out the spurious `blue` possibility
  that a naive reading of `runAlgC_seed_neighbors_resolved` alone would
  leave open.
-/
