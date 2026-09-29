/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 12, Part 1 (Bipartite Case), and formalization of Alg C
  and some of its properties needed for later steps in proof of correctness.

  AXIOMS:   0
  SORRIES:  0
-/

public import Mathlib
public import VCCBGSecC.thm13_lemma11

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Colors — five constructors: white, blue, red, black, yellow.
-- ═══════════════════════════════════════════════════════════════════════════

/-- The five colors used by the NEW Algorithm C.
    `yellow` : "a vertex that is colored black when visited, and hence
    not flipped and remains in S — a black vertex that is unvisited." -/
public inductive Color : Type where
  | white | blue | red | black | yellow
  deriving DecidableEq, Repr

open Color

public abbrev Coloring V := V → Color

/-- Count of still-white vertices. Kept for potential future
    fuel-sufficiency work; not needed by any theorem proved in this
    file. -/
public abbrev whiteCount (C : Coloring V) : ℕ :=
  (Finset.univ.filter (fun x => C x = white)).card

public theorem whiteCount_update_lt {C : Coloring V} {u : V} {c : Color}
    (h : C u = white) (hc : c ≠ white) :
    whiteCount (Function.update C u c) < whiteCount C := by
  unfold whiteCount
  have hnotmem : u ∉ Finset.univ.filter (fun x => Function.update C u c x = white) := by
    simp [Function.update_apply, hc]
  have heq : Finset.univ.filter (fun x => C x = white) =
      insert u (Finset.univ.filter (fun x => Function.update C u c x = white)) := by
    ext x
    by_cases hxu : x = u
    · subst hxu; simp [h, hnotmem]
    · simp [Function.update_apply, hxu]
  rw [heq]
  exact Finset.card_lt_card (Finset.ssubset_insert hnotmem)

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The "yellow the rest of u's white S-neighbors" side effect, PLUS
--     the four helper lemmas about it that everything downstream needs.
-- ═══════════════════════════════════════════════════════════════════════════

/-- Given a coloring `C` and a vertex `u`, apply the "yellow the rest"
    side effect (new pseudocode, lines 13, 26): every neighbor of `u`
    (per the traversal order `nbrOrder u`) that lies in `S` and is
    currently `white` gets recolored `yellow`. A single left fold over
    `nbrOrder u`, applied AFTER `u` itself has already been set to
    `blue` by the caller. -/
public abbrev yellowRestOfWhiteSNbrs (S : Finset V) (C : Coloring V) (nbrs : List V) :
    Coloring V :=
  nbrs.foldl
    (fun C' w => if w ∈ S ∧ C' w = white then Function.update C' w yellow else C')
    C

/-- Definitional unfolding, `nil` case. -/
public theorem yellowRestOfWhiteSNbrs_nil (S : Finset V) (C0 : Coloring V) :
    yellowRestOfWhiteSNbrs S C0 [] = C0 :=
  rfl

/-- Definitional unfolding, `cons` case — this is the ONLY unfolding fact
    used by every proof below; stating it once, up front, as an equation
    lemma (rather than repeatedly `unfold`-ing) keeps all later `rw`s
    syntactically matching `yellowRestOfWhiteSNbrs`'s own head symbol. -/
public theorem yellowRestOfWhiteSNbrs_cons (S : Finset V) (C0 : Coloring V) (w : V) (ws : List V) :
    yellowRestOfWhiteSNbrs S C0 (w :: ws) =
      yellowRestOfWhiteSNbrs S
        (if w ∈ S ∧ C0 w = white then Function.update C0 w yellow else C0) ws :=
  rfl

/-- **Helper 1**: the fold never touches a vertex that is already
    non-white. -/
public theorem yellowRest_preserves_nonwhite (S : Finset V) :
    ∀ (nbrs : List V) (C0 : Coloring V) (x : V), C0 x ≠ white →
      yellowRestOfWhiteSNbrs S C0 nbrs x = C0 x := by
  intro nbrs
  induction nbrs with
  | nil => intro C0 x _; rw [yellowRestOfWhiteSNbrs_nil]
  | cons w ws ih =>
      intro C0 x hx
      rw [yellowRestOfWhiteSNbrs_cons]
      set C1 := if w ∈ S ∧ C0 w = white then Function.update C0 w yellow else C0 with hC1def
      have hC1x : C1 x = C0 x := by
        by_cases hw : w ∈ S ∧ C0 w = white
        · rw [hC1def, ite_eq_left hw]
          have hxw : x ≠ w := by rintro rfl; exact hx hw.2
          rw [Function.update_apply, ite_eq_right hxw]
        · rw [hC1def, ite_eq_right hw]
      have hC1x' : C1 x ≠ white := by rw [hC1x]; exact hx
      rw [ih C1 x hC1x', hC1x]

/-- **Helper 2**: a vertex that starts white either stays white, or
    becomes yellow — nothing else — under the fold. -/
public theorem yellowRest_white_stays_white_or_yellow (S : Finset V) :
    ∀ (nbrs : List V) (C0 : Coloring V) (y : V), C0 y = white →
      yellowRestOfWhiteSNbrs S C0 nbrs y = white ∨
      yellowRestOfWhiteSNbrs S C0 nbrs y = yellow := by
  intro nbrs
  induction nbrs with
  | nil => intro C0 y hy; left; rw [yellowRestOfWhiteSNbrs_nil]; exact hy
  | cons w ws ih =>
      intro C0 y hy
      rw [yellowRestOfWhiteSNbrs_cons]
      set C1 := if w ∈ S ∧ C0 w = white then Function.update C0 w yellow else C0 with hC1def
      have hC1y : C1 y = white ∨ C1 y = yellow := by
        by_cases hw : w ∈ S ∧ C0 w = white
        · rw [hC1def, ite_eq_left hw]
          by_cases hyw : y = w
          · right; rw [hyw, Function.update_apply, ite_eq_left rfl]
          · left; rw [Function.update_apply, ite_eq_right hyw]; exact hy
        · rw [hC1def, ite_eq_right hw]; left; exact hy
      rcases hC1y with h | h
      · exact ih C1 y h
      · right
        have hne : C1 y ≠ white := by rw [h]; decide
        rw [yellowRest_preserves_nonwhite S ws C1 y hne, h]

/-- **Helper 3**: for ANY target color `c` that is not `white` and not
    `yellow` (e.g. `red`, `blue`, `black`), the fold's output at `y`
    equals `c` iff the STARTING coloring's value at `y` was already `c`
    — i.e. the fold can never manufacture a fresh `red`/`blue`/`black`,
    it only ever produces `yellow` (or leaves things unchanged). Both
    directions packaged as separate one-line theorems below. -/
public theorem yellowRest_ne_c_of_ne_c (S : Finset V) (nbrs : List V) (C0 : Coloring V) (y : V)
    {c : Color} (hcw : c ≠ white) (hcy : c ≠ yellow) (hy : C0 y ≠ c) :
    yellowRestOfWhiteSNbrs S C0 nbrs y ≠ c := by
  by_cases hw : C0 y = white
  · rcases yellowRest_white_stays_white_or_yellow S nbrs C0 y hw with h | h
    · rw [h]; exact fun heq => hcw heq.symm
    · rw [h]; exact fun heq => hcy heq.symm
  · rw [yellowRest_preserves_nonwhite S nbrs C0 y hw]; exact hy

public theorem yellowRest_eq_c_imp (S : Finset V) (nbrs : List V) (C0 : Coloring V) (y : V)
    {c : Color} (hcw : c ≠ white) (hcy : c ≠ yellow)
    (hy : yellowRestOfWhiteSNbrs S C0 nbrs y = c) : C0 y = c := by
  by_contra hne
  exact (yellowRest_ne_c_of_ne_c S nbrs C0 y hcw hcy hne) hy

/-- **Helper 4**: if `y` ends up `yellow` after the fold, either it was
    already `yellow` beforehand (invariant `hinv` applies directly), or
    it was freshly yellowed, in which case `y` itself was the neighbor
    `w` being processed, and the fold's own guard already gives `y ∈ S`
    directly. This is the one fact needed to show "yellow implies `∈ S`"
    is preserved across the side effect. -/
public theorem yellowRest_yellow_imp_S (S : Finset V) (nbrs : List V) :
    ∀ (C0 : Coloring V) (y : V), (C0 y = yellow → y ∈ S) →
      yellowRestOfWhiteSNbrs S C0 nbrs y = yellow → y ∈ S := by
  induction nbrs with
  | nil => intro C0 y hinv hy; rw [yellowRestOfWhiteSNbrs_nil] at hy; exact hinv hy
  | cons w ws ih =>
      intro C0 y hinv hy
      rw [yellowRestOfWhiteSNbrs_cons] at hy
      set C1 := if w ∈ S ∧ C0 w = white then Function.update C0 w yellow else C0 with hC1def
      have hinv1 : C1 y = yellow → y ∈ S := by
        intro hC1y
        by_cases hw : w ∈ S ∧ C0 w = white
        · rw [hC1def, ite_eq_left hw] at hC1y
          by_cases hyw : y = w
          · rw [hyw]; exact hw.1
          · rw [Function.update_apply, ite_eq_right hyw] at hC1y; exact hinv hC1y
        · rw [hC1def, ite_eq_right hw] at hC1y; exact hinv hC1y
      exact ih C1 y hinv1 hy

/-- **Helper 5**: the fold never INCREASES `whiteCount` — every touched
    vertex goes from `white` to `yellow` (a strict per-vertex decrease),
    and every untouched vertex is unaffected. Needed for any future
    fuel-sufficiency argument about a call that includes this side
    effect (the seed's own initialization, or the red/black-branch's
    blue-assignment step). -/
public theorem yellowRest_whiteCount_le (S : Finset V) :
    ∀ (nbrs : List V) (C0 : Coloring V),
      whiteCount (yellowRestOfWhiteSNbrs S C0 nbrs) ≤ whiteCount C0 := by
  intro nbrs
  induction nbrs with
  | nil => intro C0; rw [yellowRestOfWhiteSNbrs_nil]
  | cons w ws ih =>
      intro C0
      rw [yellowRestOfWhiteSNbrs_cons]
      set C1 := if w ∈ S ∧ C0 w = white then Function.update C0 w yellow else C0 with hC1def
      have hC1le : whiteCount C1 ≤ whiteCount C0 := by
        by_cases hw : w ∈ S ∧ C0 w = white
        · rw [hC1def, ite_eq_left hw]
          exact le_of_lt (whiteCount_update_lt hw.2 (c := yellow) (by decide))
        · rw [hC1def, ite_eq_right hw]
      exact le_trans (ih C1) hC1le

/-- **The correct fuel-decrease measure**: `whiteCount` alone is NOT
    enough, because a `yellow → black` transition (blue/red-branch's
    "already-yellow" rule) consumes a recursive call without decreasing
    `whiteCount` — the vertex was yellow, not white, so it was never
    counted. `resolvedMeasure` counts vertices that are NOT YET
    finalized — `white` or `yellow` — and EVERY genuine color-assignment
    site in `AlgC` (white→red, white→blue, yellow→black) strictly
    decreases it, while the `yellowRestOfWhiteSNbrs` side effect leaves
    it EXACTLY unchanged (it only moves vertices between the two counted
    buckets). This is the measure `fuelBound` is built on, below. -/
public abbrev resolvedMeasure (C : Coloring V) : ℕ :=
  (Finset.univ.filter (fun x => C x = white ∨ C x = yellow)).card

public theorem resolvedMeasure_update_lt {C : Coloring V} {u : V} {c : Color}
    (h : C u = white ∨ C u = yellow) (hc : c ≠ white ∧ c ≠ yellow) :
    resolvedMeasure (Function.update C u c) < resolvedMeasure C := by
  unfold resolvedMeasure
  have hnotmem : u ∉ Finset.univ.filter
      (fun x => Function.update C u c x = white ∨ Function.update C u c x = yellow) := by
    simp [Function.update_apply, hc.1, hc.2]
  have heq : Finset.univ.filter (fun x => C x = white ∨ C x = yellow) =
      insert u (Finset.univ.filter
        (fun x => Function.update C u c x = white ∨ Function.update C u c x = yellow)) := by
    ext x
    by_cases hxu : x = u
    · subst hxu; simp [h, hnotmem]
    · simp [Function.update_apply, hxu]
  rw [heq]
  exact Finset.card_lt_card (Finset.ssubset_insert hnotmem)

/-- The `yellowRestOfWhiteSNbrs` side effect only ever moves vertices
    BETWEEN the two counted buckets (`white ↔ yellow`), never in or out
    of them, so it leaves `resolvedMeasure` exactly unchanged — proved
    here as `≤`, which is all that's needed downstream. -/
public theorem yellowRest_resolvedMeasure_le (S : Finset V) :
    ∀ (nbrs : List V) (C0 : Coloring V),
      resolvedMeasure (yellowRestOfWhiteSNbrs S C0 nbrs) ≤ resolvedMeasure C0 := by
  intro nbrs
  induction nbrs with
  | nil => intro C0; rw [yellowRestOfWhiteSNbrs_nil]
  | cons w ws ih =>
      intro C0
      rw [yellowRestOfWhiteSNbrs_cons]
      set C1 := if w ∈ S ∧ C0 w = white then Function.update C0 w yellow else C0 with hC1def
      have hC1eq : resolvedMeasure C1 = resolvedMeasure C0 := by
        by_cases hw : w ∈ S ∧ C0 w = white
        · rw [hC1def, ite_eq_left hw]
          unfold resolvedMeasure
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hxw : x = w
          · subst hxw
            rw [Function.update_apply, ite_eq_left rfl]
            constructor
            · intro _; exact Or.inl hw.2
            · intro _; exact Or.inr rfl
          · rw [Function.update_apply, ite_eq_right hxw]
        · rw [hC1def, ite_eq_right hw]
      have h := ih C1
      rw [hC1eq] at h
      exact h

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Algorithm C, rewritten against the NEW pseudocode.
-- ═══════════════════════════════════════════════════════════════════════════

/-- `AlgC G S nbrOrder fuel C v us`: run the NEW Algorithm C, "currently
    at" vertex `v`, with `us` the remaining neighbors of `v` still to be
    processed. Direct transcription of the new pseudocode: blue/red both
    keep their old white-triggered rule PLUS a new yellow-triggered
    blackening rule; black additionally propagates using the same two
    target-color rules a blue vertex would use. -/
public abbrev AlgC (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V) :
    ℕ → Coloring V → V → List V → Coloring V
  | 0, C, _, _ => C
  | _+1, C, _, [] => C
  | n+1, C, v, u :: us =>
      if C v = blue then
        if u ∉ S ∧ C u = white then
          let C1 := Function.update C u red
          let C2 := AlgC G S nbrOrder n C1 u (nbrOrder u)
          AlgC G S nbrOrder n C2 v us
        else if u ∈ S ∧ C u = yellow then
          let C1 := Function.update C u black
          let C2 := AlgC G S nbrOrder n C1 u (nbrOrder u)
          AlgC G S nbrOrder n C2 v us
        else
          AlgC G S nbrOrder n C v us
      else if C v = red then
        if u ∈ S ∧ C u = white then
          let C1 := Function.update C u blue
          let C2 := yellowRestOfWhiteSNbrs S C1 (nbrOrder u)
          let C3 := AlgC G S nbrOrder n C2 u (nbrOrder u)
          AlgC G S nbrOrder n C3 v us
        else if u ∈ S ∧ C u = yellow then
          let C1 := Function.update C u black
          let C2 := AlgC G S nbrOrder n C1 u (nbrOrder u)
          AlgC G S nbrOrder n C2 v us
        else
          AlgC G S nbrOrder n C v us
      else if C v = black then
        if u ∉ S ∧ C u = white then
          let C1 := Function.update C u red
          let C2 := AlgC G S nbrOrder n C1 u (nbrOrder u)
          AlgC G S nbrOrder n C2 v us
        else if u ∈ S ∧ C u = white then
          let C1 := Function.update C u blue
          let C2 := yellowRestOfWhiteSNbrs S C1 (nbrOrder u)
          let C3 := AlgC G S nbrOrder n C2 u (nbrOrder u)
          AlgC G S nbrOrder n C3 v us
        else
          AlgC G S nbrOrder n C v us
      else
        AlgC G S nbrOrder n C v us

/-- The initial coloring, CORRECTED: matching Algorithm B's own behavior,
    the seed `v` is set blue AND — in the very same initialization step,
    exactly as every other blue-assignment does — its white `S`-neighbors
    are simultaneously colored `yellow`. Without this, the seed would be
    the ONE blue vertex in the whole run whose own white `S`-neighbors
    are not pre-yellowed, breaking the invariant every other blue vertex
    satisfies by construction (see `AlgC_blue_red_recurse` /
    `AlgC_black_blue_recurse`'s own `yellowRestOfWhiteSNbrs` step). With
    this fix, EVERY blue vertex — seed or not — has the property that its
    white-at-creation-time `S`-neighbors are already `yellow` by the time
    its own neighbor-list traversal begins, with no special-casing of the
    seed needed anywhere downstream. -/
public abbrev initColoring (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)
    (v : V) : Coloring V :=
  yellowRestOfWhiteSNbrs S (Function.update (fun _ => white) v blue) (nbrOrder v)

/-- The full run of Algorithm C from seed `v`. -/
public abbrev runAlgC (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)
    (fuel : ℕ) (v : V) : Coloring V :=
  AlgC G S nbrOrder fuel (initColoring G S nbrOrder v) v (nbrOrder v)

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. ValidColoring — still "is the output of this run".
-- ═══════════════════════════════════════════════════════════════════════════

public abbrev ValidColoring (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)
    (v : V) (fuel : ℕ) (C : Coloring V) : Prop :=
  C = runAlgC G S nbrOrder fuel v

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Lemma 12, Part 1 — still essentially definitional.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem Lemma12_Part1
    {G : SimpleGraph V} {S : Finset V} {nbrOrder : V → List V}
    {v : V} {fuel : ℕ} {C₁ C₂ : Coloring V}
    (hVC₁ : ValidColoring G S nbrOrder v fuel C₁)
    (hVC₂ : ValidColoring G S nbrOrder v fuel C₂) :
    C₁ = C₂ := by
  unfold ValidColoring at hVC₁ hVC₂
  rw [hVC₁, hVC₂]

public theorem Lemma12_Part1_apply
    {G : SimpleGraph V} {S : Finset V} {nbrOrder : V → List V}
    {v : V} {fuel : ℕ} {C₁ C₂ : Coloring V}
    (hVC₁ : ValidColoring G S nbrOrder v fuel C₁)
    (hVC₂ : ValidColoring G S nbrOrder v fuel C₂)
    (w : V) :
    C₁ w = C₂ w := by
  rw [Lemma12_Part1 hVC₁ hVC₂]

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Unfolding lemmas — one per reachable leaf-branch of `AlgC`.
-- ═══════════════════════════════════════════════════════════════════════════
variable (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)

public theorem AlgC_blue_red_recurse {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hv : C v = blue) (hu : u ∉ S ∧ C u = white) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) =
      AlgC G S nbrOrder m
        (AlgC G S nbrOrder m (Function.update C u red) u (nbrOrder u)) v rest := by
  simp only [AlgC]
  rw [ite_eq_left hv, ite_eq_left hu]

public theorem AlgC_blue_black_recurse {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hv : C v = blue) (hu1 : ¬ (u ∉ S ∧ C u = white)) (hu2 : u ∈ S ∧ C u = yellow) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) =
      AlgC G S nbrOrder m
        (AlgC G S nbrOrder m (Function.update C u black) u (nbrOrder u)) v rest := by
  simp only [AlgC]
  rw [ite_eq_left hv, ite_eq_right hu1, ite_eq_left hu2]

public theorem AlgC_blue_noop {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hv : C v = blue) (hu1 : ¬ (u ∉ S ∧ C u = white)) (hu2 : ¬ (u ∈ S ∧ C u = yellow)) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) = AlgC G S nbrOrder m C v rest := by
  simp only [AlgC]
  rw [ite_eq_left hv, ite_eq_right hu1, ite_eq_right hu2]

public theorem AlgC_red_blue_recurse {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hvb : ¬ C v = blue) (hv : C v = red) (hu : u ∈ S ∧ C u = white) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) =
      AlgC G S nbrOrder m
        (AlgC G S nbrOrder m (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u))
          u (nbrOrder u)) v rest := by
  simp only [AlgC]
  rw [ite_eq_right hvb, ite_eq_left hv, ite_eq_left hu]

public theorem AlgC_red_black_recurse {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hvb : ¬ C v = blue) (hv : C v = red) (hu1 : ¬ (u ∈ S ∧ C u = white))
    (hu2 : u ∈ S ∧ C u = yellow) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) =
      AlgC G S nbrOrder m
        (AlgC G S nbrOrder m (Function.update C u black) u (nbrOrder u)) v rest := by
  simp only [AlgC]
  rw [ite_eq_right hvb, ite_eq_left hv, ite_eq_right hu1, ite_eq_left hu2]

public theorem AlgC_red_noop {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hvb : ¬ C v = blue) (hv : C v = red) (hu1 : ¬ (u ∈ S ∧ C u = white))
    (hu2 : ¬ (u ∈ S ∧ C u = yellow)) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) = AlgC G S nbrOrder m C v rest := by
  simp only [AlgC]
  rw [ite_eq_right hvb, ite_eq_left hv, ite_eq_right hu1, ite_eq_right hu2]

public theorem AlgC_black_red_recurse {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hvb : ¬ C v = blue) (hvr : ¬ C v = red) (hv : C v = black)
    (hu : u ∉ S ∧ C u = white) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) =
      AlgC G S nbrOrder m
        (AlgC G S nbrOrder m (Function.update C u red) u (nbrOrder u)) v rest := by
  simp only [AlgC]
  rw [ite_eq_right hvb, ite_eq_right hvr, ite_eq_left hv, ite_eq_left hu]

public theorem AlgC_black_blue_recurse {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hvb : ¬ C v = blue) (hvr : ¬ C v = red) (hv : C v = black)
    (hu1 : ¬ (u ∉ S ∧ C u = white)) (hu2 : u ∈ S ∧ C u = white) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) =
      AlgC G S nbrOrder m
        (AlgC G S nbrOrder m (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u))
          u (nbrOrder u)) v rest := by
  simp only [AlgC]
  rw [ite_eq_right hvb, ite_eq_right hvr, ite_eq_left hv, ite_eq_right hu1, ite_eq_left hu2]

public theorem AlgC_black_noop {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hvb : ¬ C v = blue) (hvr : ¬ C v = red) (hv : C v = black)
    (hu1 : ¬ (u ∉ S ∧ C u = white)) (hu2 : ¬ (u ∈ S ∧ C u = white)) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) = AlgC G S nbrOrder m C v rest := by
  simp only [AlgC]
  rw [ite_eq_right hvb, ite_eq_right hvr, ite_eq_left hv, ite_eq_right hu1, ite_eq_right hu2]

public theorem AlgC_other {m : ℕ} {C : Coloring V} {v u : V} {rest : List V}
    (hvb : ¬ C v = blue) (hvr : ¬ C v = red) (hvk : ¬ C v = black) :
    AlgC G S nbrOrder (m + 1) C v (u :: rest) = AlgC G S nbrOrder m C v rest := by
  simp only [AlgC]
  rw [ite_eq_right hvb, ite_eq_right hvr, ite_eq_right hvk]

public theorem AlgC_nil {n : ℕ} {C : Coloring V} {v : V} :
    AlgC G S nbrOrder n C v [] = C := by
  cases n <;> simp only [AlgC]

public theorem AlgC_zero {C : Coloring V} {v : V} {us : List V} :
    AlgC G S nbrOrder 0 C v us = C := by
  simp only [AlgC]

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. THE ABSORBING-COLORS LEMMA (the core new machinery of v21).
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Absorbing colors**: any vertex `x` whose CURRENT color is neither
    `white` nor `yellow` is left completely untouched by any further
    amount of `AlgC` processing, for ANY fuel, seed, or remaining
    neighbor list. This is the single fact underlying all of
    {red, blue, black} being "terminal" under the new rules: every
    color-assignment site in `AlgC` — and the `yellowRestOfWhiteSNbrs`
    side effect — requires its target to presently be `white` or
    `yellow`. -/
public theorem AlgC_preserved_of_ne_white_yellow :
    ∀ n C v us x, C x ≠ white → C x ≠ yellow →
      AlgC G S nbrOrder n C v us x = C x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us x hxw hxy
    cases n with
    | zero => rw [AlgC_zero]
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil]
      | cons u rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u ∉ S ∧ C u = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1]
            set C1 := Function.update C u red with hC1def
            have hxu : x ≠ u := by rintro rfl; exact hxw hu1.2
            have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
            have hC1w : C1 x ≠ white := by rw [hC1x]; exact hxw
            have hC1y : C1 x ≠ yellow := by rw [hC1x]; exact hxy
            set C2 := AlgC G S nbrOrder m C1 u (nbrOrder u) with hC2def
            have hC2x : C2 x = C1 x := ih m (by omega) C1 u (nbrOrder u) x hC1w hC1y
            have hC2x' : C2 x = C x := by rw [hC2x, hC1x]
            have hC2w : C2 x ≠ white := by rw [hC2x']; exact hxw
            have hC2y : C2 x ≠ yellow := by rw [hC2x']; exact hxy
            have hfinal := ih m (by omega) C2 v rest x hC2w hC2y
            rw [hfinal, hC2x']
          · by_cases hu2 : u ∈ S ∧ C u = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2]
              set C1 := Function.update C u black with hC1def
              have hxu : x ≠ u := by rintro rfl; exact hxy hu2.2
              have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
              have hC1w : C1 x ≠ white := by rw [hC1x]; exact hxw
              have hC1y : C1 x ≠ yellow := by rw [hC1x]; exact hxy
              set C2 := AlgC G S nbrOrder m C1 u (nbrOrder u) with hC2def
              have hC2x : C2 x = C1 x := ih m (by omega) C1 u (nbrOrder u) x hC1w hC1y
              have hC2x' : C2 x = C x := by rw [hC2x, hC1x]
              have hC2w : C2 x ≠ white := by rw [hC2x']; exact hxw
              have hC2y : C2 x ≠ yellow := by rw [hC2x']; exact hxy
              have hfinal := ih m (by omega) C2 v rest x hC2w hC2y
              rw [hfinal, hC2x']
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2]
              exact ih m (by omega) C v rest x hxw hxy
        · by_cases hvr : C v = red
          · by_cases hu1 : u ∈ S ∧ C u = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu1]
              set C1 := Function.update C u blue with hC1def
              have hxu : x ≠ u := by rintro rfl; exact hxw hu1.2
              have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
              have hC1'x : C1' x = C1 x := by
                rw [hC1'def]
                have : C1 x ≠ white := by rw [hC1x]; exact hxw
                exact yellowRest_preserves_nonwhite S (nbrOrder u) C1 x this
              have hC1'x' : C1' x = C x := by rw [hC1'x, hC1x]
              have hC1'w : C1' x ≠ white := by rw [hC1'x']; exact hxw
              have hC1'y : C1' x ≠ yellow := by rw [hC1'x']; exact hxy
              set C2 := AlgC G S nbrOrder m C1' u (nbrOrder u) with hC2def
              have hC2x : C2 x = C1' x := ih m (by omega) C1' u (nbrOrder u) x hC1'w hC1'y
              have hC2x' : C2 x = C x := by rw [hC2x, hC1'x']
              have hC2w : C2 x ≠ white := by rw [hC2x']; exact hxw
              have hC2y : C2 x ≠ yellow := by rw [hC2x']; exact hxy
              have hfinal := ih m (by omega) C2 v rest x hC2w hC2y
              rw [hfinal, hC2x']
            · by_cases hu2 : u ∈ S ∧ C u = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu1 hu2]
                set C1 := Function.update C u black with hC1def
                have hxu : x ≠ u := by rintro rfl; exact hxy hu2.2
                have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
                have hC1w : C1 x ≠ white := by rw [hC1x]; exact hxw
                have hC1y : C1 x ≠ yellow := by rw [hC1x]; exact hxy
                set C2 := AlgC G S nbrOrder m C1 u (nbrOrder u) with hC2def
                have hC2x : C2 x = C1 x := ih m (by omega) C1 u (nbrOrder u) x hC1w hC1y
                have hC2x' : C2 x = C x := by rw [hC2x, hC1x]
                have hC2w : C2 x ≠ white := by rw [hC2x']; exact hxw
                have hC2y : C2 x ≠ yellow := by rw [hC2x']; exact hxy
                have hfinal := ih m (by omega) C2 v rest x hC2w hC2y
                rw [hfinal, hC2x']
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu1 hu2]
                exact ih m (by omega) C v rest x hxw hxy
          · by_cases hvk : C v = black
            · by_cases hu1 : u ∉ S ∧ C u = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu1]
                set C1 := Function.update C u red with hC1def
                have hxu : x ≠ u := by rintro rfl; exact hxw hu1.2
                have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
                have hC1w : C1 x ≠ white := by rw [hC1x]; exact hxw
                have hC1y : C1 x ≠ yellow := by rw [hC1x]; exact hxy
                set C2 := AlgC G S nbrOrder m C1 u (nbrOrder u) with hC2def
                have hC2x : C2 x = C1 x := ih m (by omega) C1 u (nbrOrder u) x hC1w hC1y
                have hC2x' : C2 x = C x := by rw [hC2x, hC1x]
                have hC2w : C2 x ≠ white := by rw [hC2x']; exact hxw
                have hC2y : C2 x ≠ yellow := by rw [hC2x']; exact hxy
                have hfinal := ih m (by omega) C2 v rest x hC2w hC2y
                rw [hfinal, hC2x']
              · by_cases hu2 : u ∈ S ∧ C u = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu1 hu2]
                  set C1 := Function.update C u blue with hC1def
                  have hxu : x ≠ u := by rintro rfl; exact hxw hu2.2
                  have hC1x : C1 x = C x := by rw [hC1def, Function.update_apply, ite_eq_right hxu]
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
                  have hC1'x : C1' x = C1 x := by
                    rw [hC1'def]
                    have : C1 x ≠ white := by rw [hC1x]; exact hxw
                    exact yellowRest_preserves_nonwhite S (nbrOrder u) C1 x this
                  have hC1'x' : C1' x = C x := by rw [hC1'x, hC1x]
                  have hC1'w : C1' x ≠ white := by rw [hC1'x']; exact hxw
                  have hC1'y : C1' x ≠ yellow := by rw [hC1'x']; exact hxy
                  set C2 := AlgC G S nbrOrder m C1' u (nbrOrder u) with hC2def
                  have hC2x : C2 x = C1' x := ih m (by omega) C1' u (nbrOrder u) x hC1'w hC1'y
                  have hC2x' : C2 x = C x := by rw [hC2x, hC1'x']
                  have hC2w : C2 x ≠ white := by rw [hC2x']; exact hxw
                  have hC2y : C2 x ≠ yellow := by rw [hC2x']; exact hxy
                  have hfinal := ih m (by omega) C2 v rest x hC2w hC2y
                  rw [hfinal, hC2x']
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu1 hu2]
                  exact ih m (by omega) C v rest x hxw hxy
            · rw [AlgC_other G S nbrOrder hvb hvr hvk]
              exact ih m (by omega) C v rest x hxw hxy

/-- Corollary, matching the signature style used elsewhere in this
    project: a non-`S` vertex already colored `red` stays `red` forever. -/
public theorem AlgC_red_preserved :
    ∀ n C v us x, x ∉ S → C x = red → AlgC G S nbrOrder n C v us x = red := by
  intro n C v us x _ hx
  have h1 : C x ≠ white := by rw [hx]; decide
  have h2 : C x ≠ yellow := by rw [hx]; decide
  rw [AlgC_preserved_of_ne_white_yellow G S nbrOrder n C v us x h1 h2, hx]

/-- Corollary: a vertex already colored `black` stays `black` forever. -/
public theorem AlgC_black_preserved :
    ∀ n C v us x, C x = black → AlgC G S nbrOrder n C v us x = black := by
  intro n C v us x hx
  have h1 : C x ≠ white := by rw [hx]; decide
  have h2 : C x ≠ yellow := by rw [hx]; decide
  rw [AlgC_preserved_of_ne_white_yellow G S nbrOrder n C v us x h1 h2, hx]

/-- New corollary (a genuine simplification relative to v19's four-color
    model): a vertex already colored `blue` stays `blue` forever — under
    the NEW rules, no branch anywhere checks whether a target is `blue`,
    so blue is just as absorbing as red and black. -/
public theorem AlgC_blue_preserved :
    ∀ n C v us x, C x = blue → AlgC G S nbrOrder n C v us x = blue := by
  intro n C v us x hx
  have h1 : C x ≠ white := by rw [hx]; decide
  have h2 : C x ≠ yellow := by rw [hx]; decide
  rw [AlgC_preserved_of_ne_white_yellow G S nbrOrder n C v us x h1 h2, hx]

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. S-membership invariants.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Red is only ever assigned to a non-`S` vertex.** Both places that
    assign `red` (the blue-branch's `u ∉ S` rule and the black-branch's
    mirrored rule) require the target to be `∉ S` directly; everywhere
    else, red-status is either untouched (absorbing lemma) or passed
    through the `yellowRestOfWhiteSNbrs` side effect unchanged (Helper 3,
    §2). -/
public theorem AlgC_preserves_red_notS :
    ∀ n C v us, (∀ x, C x = red → x ∉ S) →
      ∀ x, AlgC G S nbrOrder n C v us x = red → x ∉ S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hinv x hend
    cases n with
    | zero => rw [AlgC_zero] at hend; exact hinv x hend
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil] at hend; exact hinv x hend
      | cons u rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u ∉ S ∧ C u = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1] at hend
            set C1 := Function.update C u red with hC1def
            have hinv1 : ∀ y, C1 y = red → y ∉ S := by
              intro y hy
              by_cases hyu : y = u
              · rw [hyu]; exact hu1.1
              · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
            have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
            exact ih m (by omega) _ v rest hinv2 x hend
          · by_cases hu2 : u ∈ S ∧ C u = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2] at hend
              set C1 := Function.update C u black with hC1def
              have hinv1 : ∀ y, C1 y = red → y ∉ S := by
                intro y hy
                by_cases hyu : y = u
                · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                  exact absurd hy (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
              have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
              exact ih m (by omega) _ v rest hinv2 x hend
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2] at hend
              exact ih m (by omega) _ v rest hinv x hend
        · by_cases hvr : C v = red
          · by_cases hu1 : u ∈ S ∧ C u = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu1] at hend
              set C1 := Function.update C u blue with hC1def
              have hinv1 : ∀ y, C1 y = red → y ∉ S := by
                intro y hy
                by_cases hyu : y = u
                · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                  exact absurd hy (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
              have hinv1' : ∀ y, C1' y = red → y ∉ S := by
                intro y hy
                rw [hC1'def] at hy
                exact hinv1 y (yellowRest_eq_c_imp S (nbrOrder u) C1 y (by decide) (by decide) hy)
              have hinv2 := ih m (by omega) C1' u (nbrOrder u) hinv1'
              exact ih m (by omega) _ v rest hinv2 x hend
            · by_cases hu2 : u ∈ S ∧ C u = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu1 hu2] at hend
                set C1 := Function.update C u black with hC1def
                have hinv1 : ∀ y, C1 y = red → y ∉ S := by
                  intro y hy
                  by_cases hyu : y = u
                  · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                    exact absurd hy (by decide)
                  · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2 x hend
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu1 hu2] at hend
                exact ih m (by omega) _ v rest hinv x hend
          · by_cases hvk : C v = black
            · by_cases hu1 : u ∉ S ∧ C u = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu1] at hend
                set C1 := Function.update C u red with hC1def
                have hinv1 : ∀ y, C1 y = red → y ∉ S := by
                  intro y hy
                  by_cases hyu : y = u
                  · rw [hyu]; exact hu1.1
                  · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2 x hend
              · by_cases hu2 : u ∈ S ∧ C u = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu1 hu2] at hend
                  set C1 := Function.update C u blue with hC1def
                  have hinv1 : ∀ y, C1 y = red → y ∉ S := by
                    intro y hy
                    by_cases hyu : y = u
                    · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                      exact absurd hy (by decide)
                    · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
                  have hinv1' : ∀ y, C1' y = red → y ∉ S := by
                    intro y hy
                    rw [hC1'def] at hy
                    exact hinv1 y
                      (yellowRest_eq_c_imp S (nbrOrder u) C1 y (by decide) (by decide) hy)
                  have hinv2 := ih m (by omega) C1' u (nbrOrder u) hinv1'
                  exact ih m (by omega) _ v rest hinv2 x hend
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu1 hu2] at hend
                  exact ih m (by omega) _ v rest hinv x hend
            · rw [AlgC_other G S nbrOrder hvb hvr hvk] at hend
              exact ih m (by omega) _ v rest hinv x hend

/-- **Blue is only ever assigned to an `S`-member.** Both places that
    assign `blue` (the red-branch's, and the black-branch's, `u ∈ S`
    rule) require the target to already be `∈ S`. -/
public theorem AlgC_preserves_blue_in_S :
    ∀ n C v us, (∀ x, C x = blue → x ∈ S) →
      ∀ x, AlgC G S nbrOrder n C v us x = blue → x ∈ S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hinv x hend
    cases n with
    | zero => rw [AlgC_zero] at hend; exact hinv x hend
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil] at hend; exact hinv x hend
      | cons u rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u ∉ S ∧ C u = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1] at hend
            set C1 := Function.update C u red with hC1def
            have hinv1 : ∀ y, C1 y = blue → y ∈ S := by
              intro y hy
              by_cases hyu : y = u
              · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                exact absurd hy (by decide)
              · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
            have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
            exact ih m (by omega) _ v rest hinv2 x hend
          · by_cases hu2 : u ∈ S ∧ C u = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2] at hend
              set C1 := Function.update C u black with hC1def
              have hinv1 : ∀ y, C1 y = blue → y ∈ S := by
                intro y hy
                by_cases hyu : y = u
                · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                  exact absurd hy (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
              have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
              exact ih m (by omega) _ v rest hinv2 x hend
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2] at hend
              exact ih m (by omega) _ v rest hinv x hend
        · by_cases hvr : C v = red
          · by_cases hu1 : u ∈ S ∧ C u = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu1] at hend
              set C1 := Function.update C u blue with hC1def
              have hinv1 : ∀ y, C1 y = blue → y ∈ S := by
                intro y hy
                by_cases hyu : y = u
                · rw [hyu]; exact hu1.1
                · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
              have hinv1' : ∀ y, C1' y = blue → y ∈ S := by
                intro y hy
                rw [hC1'def] at hy
                exact hinv1 y (yellowRest_eq_c_imp S (nbrOrder u) C1 y (by decide) (by decide) hy)
              have hinv2 := ih m (by omega) C1' u (nbrOrder u) hinv1'
              exact ih m (by omega) _ v rest hinv2 x hend
            · by_cases hu2 : u ∈ S ∧ C u = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu1 hu2] at hend
                set C1 := Function.update C u black with hC1def
                have hinv1 : ∀ y, C1 y = blue → y ∈ S := by
                  intro y hy
                  by_cases hyu : y = u
                  · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                    exact absurd hy (by decide)
                  · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2 x hend
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu1 hu2] at hend
                exact ih m (by omega) _ v rest hinv x hend
          · by_cases hvk : C v = black
            · by_cases hu1 : u ∉ S ∧ C u = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu1] at hend
                set C1 := Function.update C u red with hC1def
                have hinv1 : ∀ y, C1 y = blue → y ∈ S := by
                  intro y hy
                  by_cases hyu : y = u
                  · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                    exact absurd hy (by decide)
                  · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2 x hend
              · by_cases hu2 : u ∈ S ∧ C u = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu1 hu2] at hend
                  set C1 := Function.update C u blue with hC1def
                  have hinv1 : ∀ y, C1 y = blue → y ∈ S := by
                    intro y hy
                    by_cases hyu : y = u
                    · rw [hyu]; exact hu2.1
                    · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
                  have hinv1' : ∀ y, C1' y = blue → y ∈ S := by
                    intro y hy
                    rw [hC1'def] at hy
                    exact hinv1 y
                      (yellowRest_eq_c_imp S (nbrOrder u) C1 y (by decide) (by decide) hy)
                  have hinv2 := ih m (by omega) C1' u (nbrOrder u) hinv1'
                  exact ih m (by omega) _ v rest hinv2 x hend
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu1 hu2] at hend
                  exact ih m (by omega) _ v rest hinv x hend
            · rw [AlgC_other G S nbrOrder hvb hvr hvk] at hend
              exact ih m (by omega) _ v rest hinv x hend

/-- **Black is only ever assigned to an `S`-member.** Both places that
    assign `black` require the target to already be `∈ S ∧ yellow`,
    hence in particular `∈ S`. -/
public theorem AlgC_preserves_black_in_S :
    ∀ n C v us, (∀ x, C x = black → x ∈ S) →
      ∀ x, AlgC G S nbrOrder n C v us x = black → x ∈ S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hinv x hend
    cases n with
    | zero => rw [AlgC_zero] at hend; exact hinv x hend
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil] at hend; exact hinv x hend
      | cons u rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u ∉ S ∧ C u = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1] at hend
            set C1 := Function.update C u red with hC1def
            have hinv1 : ∀ y, C1 y = black → y ∈ S := by
              intro y hy
              by_cases hyu : y = u
              · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                exact absurd hy (by decide)
              · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
            have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
            exact ih m (by omega) _ v rest hinv2 x hend
          · by_cases hu2 : u ∈ S ∧ C u = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2] at hend
              set C1 := Function.update C u black with hC1def
              have hinv1 : ∀ y, C1 y = black → y ∈ S := by
                intro y hy
                by_cases hyu : y = u
                · rw [hyu]; exact hu2.1
                · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
              have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
              exact ih m (by omega) _ v rest hinv2 x hend
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2] at hend
              exact ih m (by omega) _ v rest hinv x hend
        · by_cases hvr : C v = red
          · by_cases hu1 : u ∈ S ∧ C u = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu1] at hend
              set C1 := Function.update C u blue with hC1def
              have hinv1 : ∀ y, C1 y = black → y ∈ S := by
                intro y hy
                by_cases hyu : y = u
                · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                  exact absurd hy (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
              have hinv1' : ∀ y, C1' y = black → y ∈ S := by
                intro y hy
                rw [hC1'def] at hy
                exact hinv1 y (yellowRest_eq_c_imp S (nbrOrder u) C1 y (by decide) (by decide) hy)
              have hinv2 := ih m (by omega) C1' u (nbrOrder u) hinv1'
              exact ih m (by omega) _ v rest hinv2 x hend
            · by_cases hu2 : u ∈ S ∧ C u = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu1 hu2] at hend
                set C1 := Function.update C u black with hC1def
                have hinv1 : ∀ y, C1 y = black → y ∈ S := by
                  intro y hy
                  by_cases hyu : y = u
                  · rw [hyu]; exact hu2.1
                  · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2 x hend
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu1 hu2] at hend
                exact ih m (by omega) _ v rest hinv x hend
          · by_cases hvk : C v = black
            · by_cases hu1 : u ∉ S ∧ C u = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu1] at hend
                set C1 := Function.update C u red with hC1def
                have hinv1 : ∀ y, C1 y = black → y ∈ S := by
                  intro y hy
                  by_cases hyu : y = u
                  · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                    exact absurd hy (by decide)
                  · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2 x hend
              · by_cases hu2 : u ∈ S ∧ C u = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu1 hu2] at hend
                  set C1 := Function.update C u blue with hC1def
                  have hinv1 : ∀ y, C1 y = black → y ∈ S := by
                    intro y hy
                    by_cases hyu : y = u
                    · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                      exact absurd hy (by decide)
                    · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
                  have hinv1' : ∀ y, C1' y = black → y ∈ S := by
                    intro y hy
                    rw [hC1'def] at hy
                    exact hinv1 y
                      (yellowRest_eq_c_imp S (nbrOrder u) C1 y (by decide) (by decide) hy)
                  have hinv2 := ih m (by omega) C1' u (nbrOrder u) hinv1'
                  exact ih m (by omega) _ v rest hinv2 x hend
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu1 hu2] at hend
                  exact ih m (by omega) _ v rest hinv x hend
            · rw [AlgC_other G S nbrOrder hvb hvr hvk] at hend
              exact ih m (by omega) _ v rest hinv x hend

/-- **Yellow is only ever assigned to an `S`-member.** Yellow is only
    ever produced by `yellowRestOfWhiteSNbrs`, whose own guard already
    requires `∈ S` (Helper 4, §2); elsewhere yellow-status is either
    absorbed-away by the blue/red-branch's blackening rule (fine, since
    the invariant is only about `= yellow`, not preservation of yellow
    itself) or left untouched by the direct-assignment branches. -/
public theorem AlgC_preserves_yellow_in_S :
    ∀ n C v us, (∀ x, C x = yellow → x ∈ S) →
      ∀ x, AlgC G S nbrOrder n C v us x = yellow → x ∈ S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hinv x hend
    cases n with
    | zero => rw [AlgC_zero] at hend; exact hinv x hend
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil] at hend; exact hinv x hend
      | cons u rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u ∉ S ∧ C u = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1] at hend
            set C1 := Function.update C u red with hC1def
            have hinv1 : ∀ y, C1 y = yellow → y ∈ S := by
              intro y hy
              by_cases hyu : y = u
              · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                exact absurd hy (by decide)
              · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
            have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
            exact ih m (by omega) _ v rest hinv2 x hend
          · by_cases hu2 : u ∈ S ∧ C u = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2] at hend
              set C1 := Function.update C u black with hC1def
              have hinv1 : ∀ y, C1 y = yellow → y ∈ S := by
                intro y hy
                by_cases hyu : y = u
                · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                  exact absurd hy (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
              have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
              exact ih m (by omega) _ v rest hinv2 x hend
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2] at hend
              exact ih m (by omega) _ v rest hinv x hend
        · by_cases hvr : C v = red
          · by_cases hu1 : u ∈ S ∧ C u = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu1] at hend
              set C1 := Function.update C u blue with hC1def
              have hinv1 : ∀ y, C1 y = yellow → y ∈ S := by
                intro y hy
                by_cases hyu : y = u
                · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                  exact absurd hy (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
              have hinv1' : ∀ y, C1' y = yellow → y ∈ S := by
                intro y hy
                rw [hC1'def] at hy
                exact yellowRest_yellow_imp_S S (nbrOrder u) C1 y (hinv1 y) hy
              have hinv2 := ih m (by omega) C1' u (nbrOrder u) hinv1'
              exact ih m (by omega) _ v rest hinv2 x hend
            · by_cases hu2 : u ∈ S ∧ C u = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu1 hu2] at hend
                set C1 := Function.update C u black with hC1def
                have hinv1 : ∀ y, C1 y = yellow → y ∈ S := by
                  intro y hy
                  by_cases hyu : y = u
                  · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                    exact absurd hy (by decide)
                  · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2 x hend
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu1 hu2] at hend
                exact ih m (by omega) _ v rest hinv x hend
          · by_cases hvk : C v = black
            · by_cases hu1 : u ∉ S ∧ C u = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu1] at hend
                set C1 := Function.update C u red with hC1def
                have hinv1 : ∀ y, C1 y = yellow → y ∈ S := by
                  intro y hy
                  by_cases hyu : y = u
                  · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                    exact absurd hy (by decide)
                  · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                have hinv2 := ih m (by omega) C1 u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2 x hend
              · by_cases hu2 : u ∈ S ∧ C u = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu1 hu2] at hend
                  set C1 := Function.update C u blue with hC1def
                  have hinv1 : ∀ y, C1 y = yellow → y ∈ S := by
                    intro y hy
                    by_cases hyu : y = u
                    · rw [hC1def, hyu, Function.update_apply, ite_eq_left rfl] at hy
                      exact absurd hy (by decide)
                    · rw [hC1def, Function.update_apply, ite_eq_right hyu] at hy; exact hinv y hy
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC1'def
                  have hinv1' : ∀ y, C1' y = yellow → y ∈ S := by
                    intro y hy
                    rw [hC1'def] at hy
                    exact yellowRest_yellow_imp_S S (nbrOrder u) C1 y (hinv1 y) hy
                  have hinv2 := ih m (by omega) C1' u (nbrOrder u) hinv1'
                  exact ih m (by omega) _ v rest hinv2 x hend
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu1 hu2] at hend
                  exact ih m (by omega) _ v rest hinv x hend
            · rw [AlgC_other G S nbrOrder hvb hvr hvk] at hend
              exact ih m (by omega) _ v rest hinv x hend

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. Top-level corollaries for the actual `runAlgC` call.
-- ═══════════════════════════════════════════════════════════════════════════

/-- The seed itself, and every vertex `initColoring` touches, computed
    directly from `Function.update (fun _ => white) v0 blue` — i.e. the
    coloring BEFORE the seed's own yellowing side effect is applied.
    Used as the common starting point for all four `hinit` derivations
    below via the generalized `yellowRest_*` helper lemmas from §2. -/
private theorem initColoring_pre_eq
    (v0 y : V) :
    (Function.update (fun _ : V => white) v0 blue) y =
      (if y = v0 then blue else white) := by
  by_cases hyv : y = v0
  · rw [ite_eq_left hyv, hyv, Function.update_apply, ite_eq_left rfl]
  · rw [ite_eq_right hyv, Function.update_apply, ite_eq_right hyv]

public theorem ValidColoring_red_not_S
    {v0 : V} {fuel : ℕ} {C : Coloring V}
    (hVC : ValidColoring G S nbrOrder v0 fuel C) {p : V} (hCp : C p = red) :
    p ∉ S := by
  unfold ValidColoring at hVC
  have hCp' : runAlgC G S nbrOrder fuel v0 p = red := by rw [← hVC]; exact hCp
  unfold runAlgC at hCp'
  have hinit : ∀ y, initColoring G S nbrOrder v0 y = red → y ∉ S := by
    intro y hy
    unfold initColoring at hy
    have hC0 : (Function.update (fun _ : V => white) v0 blue) y = red :=
      yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) y
        (by decide) (by decide) hy
    rw [initColoring_pre_eq v0 y] at hC0
    by_cases hyv : y = v0
    · rw [ite_eq_left hyv] at hC0; exact absurd hC0 (by decide)
    · rw [ite_eq_right hyv] at hC0; exact absurd hC0 (by decide)
  exact AlgC_preserves_red_notS G S nbrOrder fuel (initColoring G S nbrOrder v0) v0
    (nbrOrder v0) hinit p hCp'

public theorem ValidColoring_blue_in_S
    {v0 : V} (hv0 : v0 ∈ S) {fuel : ℕ} {C : Coloring V}
    (hVC : ValidColoring G S nbrOrder v0 fuel C) {p : V} (hCp : C p = blue) :
    p ∈ S := by
  unfold ValidColoring at hVC
  have hCp' : runAlgC G S nbrOrder fuel v0 p = blue := by rw [← hVC]; exact hCp
  unfold runAlgC at hCp'
  have hinit : ∀ y, initColoring G S nbrOrder v0 y = blue → y ∈ S := by
    intro y hy
    unfold initColoring at hy
    have hC0 : (Function.update (fun _ : V => white) v0 blue) y = blue :=
      yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) y
        (by decide) (by decide) hy
    rw [initColoring_pre_eq v0 y] at hC0
    by_cases hyv : y = v0
    · rw [hyv]; exact hv0
    · rw [ite_eq_right hyv] at hC0; exact absurd hC0 (by decide)
  exact AlgC_preserves_blue_in_S G S nbrOrder fuel (initColoring G S nbrOrder v0) v0
    (nbrOrder v0) hinit p hCp'

public theorem ValidColoring_yellow_in_S
    {v0 : V} {fuel : ℕ} {C : Coloring V}
    (hVC : ValidColoring G S nbrOrder v0 fuel C) {p : V} (hCp : C p = yellow) :
    p ∈ S := by
  unfold ValidColoring at hVC
  have hCp' : runAlgC G S nbrOrder fuel v0 p = yellow := by rw [← hVC]; exact hCp
  unfold runAlgC at hCp'
  have hinit : ∀ y, initColoring G S nbrOrder v0 y = yellow → y ∈ S := by
    intro y hy
    unfold initColoring at hy
    have hinner : (Function.update (fun _ : V => white) v0 blue) y = yellow → y ∈ S := by
      intro hC0
      rw [initColoring_pre_eq v0 y] at hC0
      by_cases hyv : y = v0
      · rw [ite_eq_left hyv] at hC0; exact absurd hC0 (by decide)
      · rw [ite_eq_right hyv] at hC0; exact absurd hC0 (by decide)
    exact yellowRest_yellow_imp_S S (nbrOrder v0)
      (Function.update (fun _ : V => white) v0 blue) y hinner hy
  exact AlgC_preserves_yellow_in_S G S nbrOrder fuel (initColoring G S nbrOrder v0) v0
    (nbrOrder v0) hinit p hCp'

public theorem ValidColoring_black_in_S
    {v0 : V} {fuel : ℕ} {C : Coloring V}
    (hVC : ValidColoring G S nbrOrder v0 fuel C) {p : V} (hCp : C p = black) :
    p ∈ S := by
  unfold ValidColoring at hVC
  have hCp' : runAlgC G S nbrOrder fuel v0 p = black := by rw [← hVC]; exact hCp
  unfold runAlgC at hCp'
  have hinit : ∀ y, initColoring G S nbrOrder v0 y = black → y ∈ S := by
    intro y hy
    unfold initColoring at hy
    have hC0 : (Function.update (fun _ : V => white) v0 blue) y = black :=
      yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) y
        (by decide) (by decide) hy
    rw [initColoring_pre_eq v0 y] at hC0
    by_cases hyv : y = v0
    · rw [ite_eq_left hyv] at hC0; exact absurd hC0 (by decide)
    · rw [ite_eq_right hyv] at hC0; exact absurd hC0 (by decide)
  exact AlgC_preserves_black_in_S G S nbrOrder fuel (initColoring G S nbrOrder v0) v0
    (nbrOrder v0) hinit p hCp'

-- ═══════════════════════════════════════════════════════════════════════════
-- §10. Miscellaneous fuel scaffolding kept for signature stability.
-- ═══════════════════════════════════════════════════════════════════════════

/-- A fuel bound built on `resolvedMeasure` (NOT `whiteCount` — see that
    definition's own docstring for why `whiteCount` alone is unsound
    here: `yellow → black` transitions consume a recursive call without
    decreasing `whiteCount`). -/
public abbrev fuelBound (C : Coloring V) (us : List V) : ℕ :=
  resolvedMeasure C * (Fintype.card V + 2) + us.length + 1

public abbrev seedFuel (v : V) : ℕ := fuelBound (initColoring G S nbrOrder v) (nbrOrder v)

public theorem seedFuel_sufficient (v : V) :
    fuelBound (initColoring G S nbrOrder v) (nbrOrder v) ≤ seedFuel G S nbrOrder v := le_refl _

public theorem fuelBound_of_resolvedMeasure_lt {C1 C : Coloring V}
    (hwc : resolvedMeasure C1 < resolvedMeasure C)
    (newlist : List V) (hnewlen : newlist.length ≤ Fintype.card V) {m : ℕ}
    (hfuel_bound : resolvedMeasure C * (Fintype.card V + 2) + 1 ≤ m) :
    fuelBound C1 newlist ≤ m := by
  have hmul : (resolvedMeasure C1 + 1) * (Fintype.card V + 2)
      ≤ resolvedMeasure C * (Fintype.card V + 2) := by
    first
    | exact Nat.mul_le_mul (by omega) (le_refl _)
    | { gcongr; omega }
    | gcongr
  have hexpand : (resolvedMeasure C1 + 1) * (Fintype.card V + 2)
      = resolvedMeasure C1 * (Fintype.card V + 2) + (Fintype.card V + 2) := by ring
  rw [hexpand] at hmul
  unfold fuelBound
  omega

public theorem fuelBound_of_resolvedMeasure_le {C1 C : Coloring V}
    (hwc : resolvedMeasure C1 ≤ resolvedMeasure C)
    (rest : List V) {m : ℕ}
    (hfuel_bound : resolvedMeasure C * (Fintype.card V + 2) + rest.length + 1 ≤ m) :
    fuelBound C1 rest ≤ m := by
  have hmul : resolvedMeasure C1 * (Fintype.card V + 2) ≤
   resolvedMeasure C * (Fintype.card V + 2) := by
    first
    | exact Nat.mul_le_mul hwc (le_refl _)
    | gcongr
  unfold fuelBound
  omega

/-- `resolvedMeasure` is non-increasing across any `AlgC` call — every
    genuine assignment site strictly decreases it (Helper above), the
    `yellowRestOfWhiteSNbrs` side effect leaves it unchanged
    (`yellowRest_resolvedMeasure_le`), and both facts chain cleanly
    across the two nested recursive calls (dive, then continue) via
    `omega` treating each `resolvedMeasure (AlgC ...)` term as an atom. -/
public theorem AlgC_resolvedMeasure_le :
    ∀ n C v us, resolvedMeasure (AlgC G S nbrOrder n C v us) ≤ resolvedMeasure C := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us
    cases n with
    | zero => rw [AlgC_zero]
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil]
      | cons u rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u ∉ S ∧ C u = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1]
            have h1 : resolvedMeasure (Function.update C u red) ≤ resolvedMeasure C :=
              le_of_lt (resolvedMeasure_update_lt (Or.inl hu1.2) (by decide))
            have h2 := ih m (by omega) (Function.update C u red) u (nbrOrder u)
            have h3 := ih m (by omega)
              (AlgC G S nbrOrder m (Function.update C u red) u (nbrOrder u)) v rest
            omega
          · by_cases hu2 : u ∈ S ∧ C u = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2]
              have h1 : resolvedMeasure (Function.update C u black) ≤ resolvedMeasure C :=
                le_of_lt (resolvedMeasure_update_lt (Or.inr hu2.2) (by decide))
              have h2 := ih m (by omega) (Function.update C u black) u (nbrOrder u)
              have h3 := ih m (by omega)
                (AlgC G S nbrOrder m (Function.update C u black) u (nbrOrder u)) v rest
              omega
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2]
              exact ih m (by omega) C v rest
        · by_cases hvr : C v = red
          · by_cases hu1 : u ∈ S ∧ C u = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu1]
              have h1 : resolvedMeasure (Function.update C u blue) ≤ resolvedMeasure C :=
                le_of_lt (resolvedMeasure_update_lt (Or.inl hu1.2) (by decide))
              have h1' : resolvedMeasure
                  (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u))
                  ≤ resolvedMeasure (Function.update C u blue) :=
                yellowRest_resolvedMeasure_le S (nbrOrder u) (Function.update C u blue)
              have h2 := ih m (by omega)
                (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u)) u (nbrOrder u)
              have h3 := ih m (by omega)
                (AlgC G S nbrOrder m
                  (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u)) u (nbrOrder u))
                v rest
              omega
            · by_cases hu2 : u ∈ S ∧ C u = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu1 hu2]
                have h1 : resolvedMeasure (Function.update C u black) ≤ resolvedMeasure C :=
                  le_of_lt (resolvedMeasure_update_lt (Or.inr hu2.2) (by decide))
                have h2 := ih m (by omega) (Function.update C u black) u (nbrOrder u)
                have h3 := ih m (by omega)
                  (AlgC G S nbrOrder m (Function.update C u black) u (nbrOrder u)) v rest
                omega
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu1 hu2]
                exact ih m (by omega) C v rest
          · by_cases hvk : C v = black
            · by_cases hu1 : u ∉ S ∧ C u = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu1]
                have h1 : resolvedMeasure (Function.update C u red) ≤ resolvedMeasure C :=
                  le_of_lt (resolvedMeasure_update_lt (Or.inl hu1.2) (by decide))
                have h2 := ih m (by omega) (Function.update C u red) u (nbrOrder u)
                have h3 := ih m (by omega)
                  (AlgC G S nbrOrder m (Function.update C u red) u (nbrOrder u)) v rest
                omega
              · by_cases hu2 : u ∈ S ∧ C u = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu1 hu2]
                  have h1 : resolvedMeasure (Function.update C u blue) ≤ resolvedMeasure C :=
                    le_of_lt (resolvedMeasure_update_lt (Or.inl hu2.2) (by decide))
                  have h1' : resolvedMeasure
                      (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u))
                      ≤ resolvedMeasure (Function.update C u blue) :=
                    yellowRest_resolvedMeasure_le S (nbrOrder u) (Function.update C u blue)
                  have h2 := ih m (by omega)
                    (yellowRestOfWhiteSNbrs S (Function.update C u blue)
                     (nbrOrder u)) u (nbrOrder u)
                  have h3 := ih m (by omega)
                    (AlgC G S nbrOrder m
                      (yellowRestOfWhiteSNbrs S (Function.update C u blue)
                       (nbrOrder u)) u (nbrOrder u))
                    v rest
                  omega
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu1 hu2]
                  exact ih m (by omega) C v rest
            · rw [AlgC_other G S nbrOrder hvb hvr hvk]
              exact ih m (by omega) C v rest

-- ═══════════════════════════════════════════════════════════════════════════
-- §10.5. The `BlueNbrsResolved` invariant: every blue vertex's white-at-
--     creation-time `S`-neighbors are already non-white. True by
--     construction at every blue-creation site (the seed's own
--     `initColoring`, and the red/black-branch's `u ∈ S ∧ white → blue`
--     rule), and preserved forward — this is the fact you identified:
--     an `S`-neighbor of a blue vertex is ALREADY yellow (or otherwise
--     resolved) by the time it is traversed, with no dependence on
--     other parts of the graph.
-- ═══════════════════════════════════════════════════════════════════════════

/-- `BlueNbrsResolved C`: every blue vertex's `S`-neighbors (per
    `nbrOrder`) are not white — i.e. already `yellow`, `black`, or
    `blue`. -/
public abbrev BlueNbrsResolved (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)
    (C : Coloring V) : Prop :=
  ∀ x, C x = blue → ∀ w ∈ nbrOrder x, w ∈ S → C w ≠ white

/-- The fold never touches a vertex outside `S` at all — its guard
    always requires `w ∈ S`. -/
public theorem yellowRest_preserves_notS (S : Finset V) :
    ∀ (nbrs : List V) (C0 : Coloring V) (x : V), x ∉ S →
      yellowRestOfWhiteSNbrs S C0 nbrs x = C0 x := by
  intro nbrs
  induction nbrs with
  | nil => intro C0 x _; rw [yellowRestOfWhiteSNbrs_nil]
  | cons w ws ih =>
      intro C0 x hxS
      rw [yellowRestOfWhiteSNbrs_cons]
      set C1 := if w ∈ S ∧ C0 w = white then Function.update C0 w yellow else C0 with hC1def
      have hC1x : C1 x = C0 x := by
        by_cases hw : w ∈ S ∧ C0 w = white
        · rw [hC1def, ite_eq_left hw]
          have hxw : x ≠ w := fun h => hxS (h ▸ hw.1)
          rw [Function.update_apply, ite_eq_right hxw]
        · rw [hC1def, ite_eq_right hw]
      rw [ih C1 x hxS, hC1x]

/-- **The key structural fact you identified**: for `w` within the SAME
    list `nbrs` the fold is processing, if `w ∈ S`, the fold guarantees
    `w` ends up non-white — either it was already non-white and stayed
    that way, or the fold reaches `w`'s own occurrence in the list and
    yellows it right then (since its guard, at that moment, is exactly
    `w ∈ S ∧ (current value) = white`). -/
public theorem yellowRest_resolves_own_list (S : Finset V) :
    ∀ (nbrs : List V) (C0 : Coloring V) (w : V), w ∈ nbrs → w ∈ S →
      yellowRestOfWhiteSNbrs S C0 nbrs w ≠ white := by
  intro nbrs
  induction nbrs with
  | nil => intro C0 w hw _; exact absurd hw (List.not_mem_nil)
  | cons w0 ws ih =>
      intro C0 w hw hwS
      rw [yellowRestOfWhiteSNbrs_cons]
      set C1 := if w0 ∈ S ∧ C0 w0 = white then Function.update C0 w0 yellow else C0 with hC1def
      by_cases hww0 : w = w0
      · have hw0S : w0 ∈ S := by rw [← hww0]; exact hwS
        by_cases hcase : C0 w0 = white
        · have hC1w : C1 w = yellow := by
            rw [hC1def, ite_eq_left ⟨hw0S, hcase⟩, Function.update_apply, ite_eq_left hww0]
          have hne : C1 w ≠ white := by rw [hC1w]; decide
          rw [yellowRest_preserves_nonwhite S ws C1 w hne]
          exact hne
        · have hC1w : C1 w = C0 w := by
            rw [hC1def, ite_eq_right (fun hg : w0 ∈ S ∧ C0 w0 = white => hcase hg.2)]
          have hne : C1 w ≠ white := by rw [hC1w, hww0]; exact hcase
          rw [yellowRest_preserves_nonwhite S ws C1 w hne]
          exact hne
      · have hw' : w ∈ ws := by
          rcases List.mem_cons.mp hw with h1 | h2
          · exact absurd h1 hww0
          · exact h2
        exact ih C1 w hw' hwS

/-- Single-step preservation of `BlueNbrsResolved` under any update that
    does not touch a currently-blue vertex's own color and is not itself
    a blue-assignment (i.e. every direct update EXCEPT the "new blue"
    sites): `c` is the new color, and it must be neither `blue` (else the
    updated vertex's own color changes, invalidating the "x blue"
    premise trivially — handled) nor `white` (else the conclusion
    "≠ white" could fail at exactly the updated vertex). -/
public theorem BlueNbrsResolved_update_absorbing
    {C : Coloring V} {u : V} {c : Color} (hcb : c ≠ blue) (hcw : c ≠ white)
    (hinv : BlueNbrsResolved G S nbrOrder C) :
    BlueNbrsResolved G S nbrOrder (Function.update C u c) := by
  intro x hx w hw hwS
  have hxu : x ≠ u := by
    rintro rfl
    rw [Function.update_apply, ite_eq_left rfl] at hx
    exact hcb hx
  have hCx : C x = blue := by
    have h := hx
    rw [Function.update_apply, ite_eq_right hxu] at h
    exact h
  have hCw := hinv x hCx w hw hwS
  by_cases hwu : w = u
  · rw [hwu, Function.update_apply, ite_eq_left rfl]
    exact hcw
  · rw [Function.update_apply, ite_eq_right hwu]
    exact hCw

/-- Single-step preservation of `BlueNbrsResolved` at the "new blue"
    creation site: the freshly-blued vertex `u`'s OWN invariant is
    established directly by `yellowRest_resolves_own_list` (its guard
    fires on `u`'s own neighbor list at creation time); every other
    already-blue vertex's invariant is untouched, since the fold can
    only ever have produced `blue` at `x` (given `x ≠ u`) if `x` was
    already blue before this step (blue is never freshly assigned by
    the fold — only `yellow` is). -/
public theorem BlueNbrsResolved_new_blue
    {C : Coloring V} {u : V}
    (hinv : BlueNbrsResolved G S nbrOrder C) :
    BlueNbrsResolved G S nbrOrder
      (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u)) := by
  set C1 := Function.update C u blue with hC1def
  set C2 := yellowRestOfWhiteSNbrs S C1 (nbrOrder u) with hC2def
  intro x hx w hw hwS
  by_cases hxu : x = u
  · rw [hxu] at hw
    rw [hC2def]
    exact yellowRest_resolves_own_list S (nbrOrder u) C1 w hw hwS
  · have hC1x_eq : C1 x = blue := by
      rw [hC2def] at hx
      exact yellowRest_eq_c_imp S (nbrOrder u) C1 x (by decide) (by decide) hx
    have hCx : C x = blue := by
      rw [hC1def, Function.update_apply, ite_eq_right hxu] at hC1x_eq
      exact hC1x_eq
    have hCw : C w ≠ white := hinv x hCx w hw hwS
    have hC1w : C1 w ≠ white := by
      by_cases hwu : w = u
      · rw [hC1def, hwu, Function.update_apply, ite_eq_left rfl]; decide
      · rw [hC1def, Function.update_apply, ite_eq_right hwu]; exact hCw
    rw [hC2def, yellowRest_preserves_nonwhite S (nbrOrder u) C1 w hC1w]
    exact hC1w

/-- **`BlueNbrsResolved` is a global invariant of the recursion**: it
    holds throughout ANY `AlgC` run, given it held at the start. -/
public theorem AlgC_preserves_BlueNbrsResolved :
    ∀ n C v us, BlueNbrsResolved G S nbrOrder C →
      BlueNbrsResolved G S nbrOrder (AlgC G S nbrOrder n C v us) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hinv
    cases n with
    | zero => rw [AlgC_zero]; exact hinv
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil]; exact hinv
      | cons u rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u ∉ S ∧ C u = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1]
            have hinv1 := BlueNbrsResolved_update_absorbing G S nbrOrder
              (u := u) (c := red) (by decide) (by decide) hinv
            have hinv2 := ih m (by omega) (Function.update C u red) u (nbrOrder u) hinv1
            exact ih m (by omega) _ v rest hinv2
          · by_cases hu2 : u ∈ S ∧ C u = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2]
              have hinv1 := BlueNbrsResolved_update_absorbing G S nbrOrder
                (u := u) (c := black) (by decide) (by decide) hinv
              have hinv2 := ih m (by omega) (Function.update C u black) u (nbrOrder u) hinv1
              exact ih m (by omega) _ v rest hinv2
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2]
              exact ih m (by omega) C v rest hinv
        · by_cases hvr : C v = red
          · by_cases hu1 : u ∈ S ∧ C u = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu1]
              have hinv1 := BlueNbrsResolved_new_blue G S nbrOrder (u := u) hinv
              have hinv2 := ih m (by omega)
                (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u))
                u (nbrOrder u) hinv1
              exact ih m (by omega) _ v rest hinv2
            · by_cases hu2 : u ∈ S ∧ C u = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu1 hu2]
                have hinv1 := BlueNbrsResolved_update_absorbing G S nbrOrder
                  (u := u) (c := black) (by decide) (by decide) hinv
                have hinv2 := ih m (by omega) (Function.update C u black) u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu1 hu2]
                exact ih m (by omega) C v rest hinv
          · by_cases hvk : C v = black
            · by_cases hu1 : u ∉ S ∧ C u = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu1]
                have hinv1 := BlueNbrsResolved_update_absorbing G S nbrOrder
                  (u := u) (c := red) (by decide) (by decide) hinv
                have hinv2 := ih m (by omega) (Function.update C u red) u (nbrOrder u) hinv1
                exact ih m (by omega) _ v rest hinv2
              · by_cases hu2 : u ∈ S ∧ C u = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu1 hu2]
                  have hinv1 := BlueNbrsResolved_new_blue G S nbrOrder (u := u) hinv
                  have hinv2 := ih m (by omega)
                    (yellowRestOfWhiteSNbrs S (Function.update C u blue) (nbrOrder u))
                    u (nbrOrder u) hinv1
                  exact ih m (by omega) _ v rest hinv2
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu1 hu2]
                  exact ih m (by omega) C v rest hinv
            · rw [AlgC_other G S nbrOrder hvb hvr hvk]
              exact ih m (by omega) C v rest hinv

/-- **Base case**: `initColoring` itself satisfies `BlueNbrsResolved` —
    the seed's own blue-assignment is accompanied by exactly the same
    yellowing side effect (this file's earlier fix), so
    `yellowRest_resolves_own_list` applies directly at `x = v0`; for any
    OTHER `x`, `x` cannot be blue at all (only `v0` is, or ever was, blue
    at this stage), so the premise is vacuous. -/
public theorem initColoring_BlueNbrsResolved (v0 : V) :
    BlueNbrsResolved G S nbrOrder (initColoring G S nbrOrder v0) := by
  unfold initColoring
  intro x hx w hw hwS
  set C0 := Function.update (fun _ : V => white) v0 blue with hC0def
  by_cases hxv0 : x = v0
  · rw [hxv0] at hw
    exact yellowRest_resolves_own_list S (nbrOrder v0) C0 w hw hwS
  · exfalso
    have hC0x_eq : C0 x = blue :=
      yellowRest_eq_c_imp S (nbrOrder v0) C0 x (by decide) (by decide) hx
    rw [hC0def, Function.update_apply, ite_eq_right hxv0] at hC0x_eq
    exact absurd hC0x_eq (by decide)

/-- **Global fact**: `∀x∉S, Cx=white∨red` is preserved through ANY
    `AlgC` run, given it held at the start — an immediate consequence of
    the three `_in_S` invariants already proved: a non-`S` vertex can
    never be blue, yellow, or black, so by elimination (`Color` has
    exactly five constructors) it stays white or red. -/
public theorem AlgC_preserves_notS_white_or_red :
    ∀ n C v us, (∀ x ∉ S, C x = white ∨ C x = red) →
      ∀ x ∉ S, AlgC G S nbrOrder n C v us x = white ∨ AlgC G S nbrOrder n C v us x = red := by
  intro n C v us hinv x hxS
  have hblue_inv : ∀ y, C y = blue → y ∈ S := by
    intro y hy
    by_contra hyS
    rcases hinv y hyS with hw | hr
    · rw [hy] at hw; exact absurd hw (by decide)
    · rw [hy] at hr; exact absurd hr (by decide)
  have hyellow_inv : ∀ y, C y = yellow → y ∈ S := by
    intro y hy
    by_contra hyS
    rcases hinv y hyS with hw | hr
    · rw [hy] at hw; exact absurd hw (by decide)
    · rw [hy] at hr; exact absurd hr (by decide)
  have hblack_inv : ∀ y, C y = black → y ∈ S := by
    intro y hy
    by_contra hyS
    rcases hinv y hyS with hw | hr
    · rw [hy] at hw; exact absurd hw (by decide)
    · rw [hy] at hr; exact absurd hr (by decide)
  have hnotblue : AlgC G S nbrOrder n C v us x ≠ blue := fun h =>
    hxS (AlgC_preserves_blue_in_S G S nbrOrder n C v us hblue_inv x h)
  have hnotyellow : AlgC G S nbrOrder n C v us x ≠ yellow := fun h =>
    hxS (AlgC_preserves_yellow_in_S G S nbrOrder n C v us hyellow_inv x h)
  have hnotblack : AlgC G S nbrOrder n C v us x ≠ black := fun h =>
    hxS (AlgC_preserves_black_in_S G S nbrOrder n C v us hblack_inv x h)
  cases hc : AlgC G S nbrOrder n C v us x with
  | white => left; rfl
  | blue => exact absurd hc hnotblue
  | red => right; rfl
  | black => exact absurd hc hnotblack
  | yellow => exact absurd hc hnotyellow

-- ═══════════════════════════════════════════════════════════════════════════
-- §10.6. THE MAIN THEOREM: a blue vertex's own neighbor-list traversal
--     resolves every `S`-neighbor to `black` or `blue`, and every
--     non-`S`-neighbor to `red` — given sufficient fuel to actually
--     reach the end of the list.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Blue-neighbor resolution**. Given `C v = blue`, `BlueNbrsResolved
    C`, the standing invariants `red ⟹ ∉S` / `∉S ⟹ white∨red`, and
    sufficient fuel to process all of `us` (a sub-list of `v`'s own
    neighbor order, and one that does not contain `v` itself): every
    `u ∈ us` ends up `black` or `blue` if `u ∈ S`, and `red` if `u ∉ S`.

    Proof: for the head `u'` of the list, `BlueNbrsResolved C` (if
    `u' ∈ S`) or the standing `∉S` invariant (if `u' ∉ S`) pins down `C
    u'` to one of exactly two live possibilities in each case — and in
    EVERY case, the single processing step immediately resolves `u'`
    (either it was already resolved and the step is a no-op, or the
    step performs the resolving assignment directly), after which
    `u'`'s color is ABSORBING (`AlgC_blue_preserved` /
    `AlgC_black_preserved` / `AlgC_red_preserved`) through everything
    that happens afterward — the dive into `u'`'s own list, and the
    continuation over the rest of `us`. The remaining content of the
    proof is exactly the fuel bookkeeping (via `resolvedMeasure`) needed
    to justify recursing into the tail of the list with the induction
    hypothesis. -/
public theorem AlgC_blue_resolves_own_list
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) :
    ∀ n C v us, (∀ y ∈ us, y ≠ v) → C v = blue →
      (∀ x, C x = red → x ∉ S) →
      (∀ x ∉ S, C x = white ∨ C x = red) →
      BlueNbrsResolved G S nbrOrder C →
      (∀ y ∈ us, y ∈ nbrOrder v) →
      fuelBound C us ≤ n →
      ∀ u ∈ us,
        (u ∈ S →
          AlgC G S nbrOrder n C v us u = black ∨ AlgC G S nbrOrder n C v us u = blue) ∧
        (u ∉ S → AlgC G S nbrOrder n C v us u = red) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hwf hvb hred hnotS hinv hsub hfuel u hu
    cases n with
    | zero =>
      exfalso
      cases us with
      | nil => exact List.not_mem_nil hu
      | cons u' rest =>
        simp only [fuelBound, List.length_cons] at hfuel
        omega
    | succ m =>
      cases us with
      | nil => exact absurd hu (List.not_mem_nil)
      | cons u' rest =>
        simp only [fuelBound, List.length_cons] at hfuel
        have hu'nbr : u' ∈ nbrOrder v := hsub u' (List.mem_cons.mpr (Or.inl rfl))
        have hu'v : u' ≠ v := hwf u' (List.mem_cons.mpr (Or.inl rfl))
        have hrestwf : ∀ y ∈ rest, y ≠ v := fun y hy => hwf y (List.mem_cons.mpr (Or.inr hy))
        have hrestsub : ∀ y ∈ rest, y ∈ nbrOrder v := fun y hy => hsub y (List.mem_cons.mpr (Or.inr hy))
        by_cases hu'S : u' ∈ S
        · have hCu'_ne_white : C u' ≠ white := hinv v hvb u' hu'nbr hu'S
          have hCu'_ne_red : C u' ≠ red := fun hr => (hred u' hr) hu'S
          by_cases hCublue : C u' = blue
          · have hu1 : ¬ (u' ∉ S ∧ C u' = white) := fun h => h.1 hu'S
            have hu2 : ¬ (u' ∈ S ∧ C u' = yellow) := by
              intro h; rw [hCublue] at h; exact absurd h.2 (by decide)
            rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2]
            rcases List.mem_cons.mp hu with heq | hu_rest
            · rw [heq]
              exact ⟨fun _ => Or.inr (AlgC_blue_preserved G S nbrOrder m C v rest u' hCublue),
                fun hnS => absurd hu'S hnS⟩
            · have hfuel' : fuelBound C rest ≤ m := by unfold fuelBound; omega
              exact ih m (by omega) C v rest hrestwf hvb hred hnotS hinv hrestsub hfuel' u hu_rest
          · by_cases hCublack : C u' = black
            · have hu1 : ¬ (u' ∉ S ∧ C u' = white) := fun h => h.1 hu'S
              have hu2 : ¬ (u' ∈ S ∧ C u' = yellow) := by
                intro h; rw [hCublack] at h; exact absurd h.2 (by decide)
              rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2]
              rcases List.mem_cons.mp hu with heq | hu_rest
              · rw [heq]
                exact ⟨fun _ => Or.inl (AlgC_black_preserved G S nbrOrder m C v rest u' hCublack),
                  fun hnS => absurd hu'S hnS⟩
              · have hfuel' : fuelBound C rest ≤ m := by unfold fuelBound; omega
                exact ih m (by omega) C v rest hrestwf hvb hred hnotS hinv hrestsub hfuel' u hu_rest
            · have hCuyellow : C u' = yellow := by
                cases hc : C u' with
                | white => exact absurd hc hCu'_ne_white
                | blue => exact absurd hc hCublue
                | red => exact absurd hc hCu'_ne_red
                | black => exact absurd hc hCublack
                | yellow => rfl
              have hu1 : ¬ (u' ∉ S ∧ C u' = white) := fun h => h.1 hu'S
              have hu2 : u' ∈ S ∧ C u' = yellow := ⟨hu'S, hCuyellow⟩
              rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2]
              set C1 := Function.update C u' black with hC1def
              have hvb1 : C1 v = blue := by
                rw [hC1def, Function.update_apply, ite_eq_right (Ne.symm hu'v)]; exact hvb
              have hred1 : ∀ x, C1 x = red → x ∉ S := by
                intro x hx
                by_cases hxu' : x = u'
                · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                  exact absurd hx (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx
                  exact hred x hx
              have hnotS1 : ∀ x ∉ S, C1 x = white ∨ C1 x = red := by
                intro x hxS
                have hxu' : x ≠ u' := fun h => hxS (h ▸ hu'S)
                rw [hC1def, Function.update_apply, ite_eq_right hxu']
                exact hnotS x hxS
              have hinv1 : BlueNbrsResolved G S nbrOrder C1 :=
                BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hinv
              have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                resolvedMeasure_update_lt (Or.inr hCuyellow) (by decide)
              have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
                fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
              set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
              have hred2 : ∀ x, C2 x = red → x ∉ S :=
                AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hred1
              have hnotS2 : ∀ x ∉ S, C2 x = white ∨ C2 x = red :=
                AlgC_preserves_notS_white_or_red G S nbrOrder m C1 u' (nbrOrder u') hnotS1
              have hinv2 : BlueNbrsResolved G S nbrOrder C2 :=
                AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hinv1
              have hvb2 : C2 v = blue := AlgC_blue_preserved G S nbrOrder m C1 u' (nbrOrder u') v hvb1
              have hC2u' : C2 u' = black := by
                have hC1u' : C1 u' = black := by
                  rw [hC1def, Function.update_apply, ite_eq_left rfl]
                exact AlgC_black_preserved G S nbrOrder m C1 u' (nbrOrder u') u' hC1u'
              have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u')) (le_of_lt hwc1)
              have hfuel' : fuelBound C2 rest ≤ m :=
                fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
              rcases List.mem_cons.mp hu with heq | hu_rest
              · rw [heq]
                exact ⟨fun _ => Or.inl (AlgC_black_preserved G S nbrOrder m C2 v rest u' hC2u'),
                  fun hnS => absurd hu'S hnS⟩
              · exact ih m (by omega) C2 v rest hrestwf hvb2 hred2 hnotS2 hinv2 hrestsub hfuel' u hu_rest
        · have hCu'wr : C u' = white ∨ C u' = red := hnotS u' hu'S
          rcases hCu'wr with hCuwhite | hCured
          · have hu1 : u' ∉ S ∧ C u' = white := ⟨hu'S, hCuwhite⟩
            rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1]
            set C1 := Function.update C u' red with hC1def
            have hvb1 : C1 v = blue := by
              rw [hC1def, Function.update_apply, ite_eq_right (Ne.symm hu'v)]; exact hvb
            have hred1 : ∀ x, C1 x = red → x ∉ S := by
              intro x hx
              by_cases hxu' : x = u'
              · rw [hxu']; exact hu'S
              · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx
                exact hred x hx
            have hnotS1 : ∀ x ∉ S, C1 x = white ∨ C1 x = red := by
              intro x hxS
              by_cases hxu' : x = u'
              · right; rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl]
              · rw [hC1def, Function.update_apply, ite_eq_right hxu']
                exact hnotS x hxS
            have hinv1 : BlueNbrsResolved G S nbrOrder C1 :=
              BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hinv
            have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
              resolvedMeasure_update_lt (Or.inl hCuwhite) (by decide)
            have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
              fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
            set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
            have hred2 : ∀ x, C2 x = red → x ∉ S :=
              AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hred1
            have hnotS2 : ∀ x ∉ S, C2 x = white ∨ C2 x = red :=
              AlgC_preserves_notS_white_or_red G S nbrOrder m C1 u' (nbrOrder u') hnotS1
            have hinv2 : BlueNbrsResolved G S nbrOrder C2 :=
              AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hinv1
            have hvb2 : C2 v = blue := AlgC_blue_preserved G S nbrOrder m C1 u' (nbrOrder u') v hvb1
            have hC2u' : C2 u' = red := by
              have hC1u' : C1 u' = red := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
              exact AlgC_red_preserved G S nbrOrder m C1 u' (nbrOrder u') u' hu'S hC1u'
            have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
              le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u')) (le_of_lt hwc1)
            have hfuel' : fuelBound C2 rest ≤ m :=
              fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
            rcases List.mem_cons.mp hu with heq | hu_rest
            · rw [heq]
              exact ⟨fun hS => absurd hS hu'S,
                fun _ => AlgC_red_preserved G S nbrOrder m C2 v rest u' hu'S hC2u'⟩
            · exact ih m (by omega) C2 v rest hrestwf hvb2 hred2 hnotS2 hinv2 hrestsub hfuel' u hu_rest
          · have hu1 : ¬ (u' ∉ S ∧ C u' = white) := fun h => absurd hCured (by rw [h.2]; decide)
            have hu2 : ¬ (u' ∈ S ∧ C u' = yellow) := fun h => absurd h.1 hu'S
            rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2]
            rcases List.mem_cons.mp hu with heq | hu_rest
            · rw [heq]
              exact ⟨fun hS => absurd hS hu'S,
                fun _ => AlgC_red_preserved G S nbrOrder m C v rest u' hu'S hCured⟩
            · have hfuel' : fuelBound C rest ≤ m := by unfold fuelBound; omega
              exact ih m (by omega) C v rest hrestwf hvb hred hnotS hinv hrestsub hfuel' u hu_rest

/-- **Top-level corollary, seeded case**: every direct `S`-neighbor of
    the seed `v0` ends up `black` or `blue`, and every non-`S`-neighbor
    ends up `red`, in the final `runAlgC` output — this is precisely the
    original question, answered: an `S`-neighbor of the (now correctly
    yellow-accompanied) blue seed is ALREADY yellow by the time the
    seed's own traversal reaches it, so it is unconditionally resolved,
    with no dependence on the rest of the graph. -/
public theorem runAlgC_seed_neighbors_resolved
    (hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {v0 : V} (hv0 : v0 ∈ S) {fuel : ℕ}
    (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel) :
    ∀ w ∈ nbrOrder v0,
      (w ∈ S →
        runAlgC G S nbrOrder fuel v0 w = black ∨ runAlgC G S nbrOrder fuel v0 w = blue) ∧
      (w ∉ S → runAlgC G S nbrOrder fuel v0 w = red) := by
  have hvb : initColoring G S nbrOrder v0 v0 = blue := by
    unfold initColoring
    have hC0 : (Function.update (fun _ : V => white) v0 blue) v0 = blue := by
      rw [Function.update_apply, ite_eq_left rfl]
    have hne : (Function.update (fun _ : V => white) v0 blue) v0 ≠ white := by rw [hC0]; decide
    rw [yellowRest_preserves_nonwhite S (nbrOrder v0)
      (Function.update (fun _ : V => white) v0 blue) v0 hne, hC0]
  have hred0 : ∀ x, initColoring G S nbrOrder v0 x = red → x ∉ S := by
    intro x hx
    exfalso
    unfold initColoring at hx
    have hC0 : (Function.update (fun _ : V => white) v0 blue) x = red :=
      yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) x
        (by decide) (by decide) hx
    by_cases hxv : x = v0
    · rw [hxv, Function.update_apply, ite_eq_left rfl] at hC0; exact absurd hC0 (by decide)
    · rw [Function.update_apply, ite_eq_right hxv] at hC0; exact absurd hC0 (by decide)
  have hwhite0 : ∀ x ∉ S, initColoring G S nbrOrder v0 x = white := by
    intro x hxS
    have hxv0 : x ≠ v0 := by intro h; apply hxS; rw [h]; exact hv0
    unfold initColoring
    rw [yellowRest_preserves_notS S (nbrOrder v0)
      (Function.update (fun _ : V => white) v0 blue) x hxS]
    rw [Function.update_apply, ite_eq_right hxv0]
  have hnotS0 : ∀ x ∉ S,
      initColoring G S nbrOrder v0 x = white ∨ initColoring G S nbrOrder v0 x = red :=
    fun x hxS => Or.inl (hwhite0 x hxS)
  have hinv0 : BlueNbrsResolved G S nbrOrder (initColoring G S nbrOrder v0) :=
    initColoring_BlueNbrsResolved G S nbrOrder v0
  intro w hw
  unfold runAlgC
  exact AlgC_blue_resolves_own_list G S nbrOrder hlen fuel (initColoring G S nbrOrder v0) v0
    (nbrOrder v0) (hirrefl v0) hvb hred0 hnotS0 hinv0 (fun y hy => hy) hfuel w hw

-- ═══════════════════════════════════════════════════════════════════════════
-- §11. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry` or hypothesis hacking, 1 `axiom`.

  Proof map:
    whiteCount_update_lt                — pure Finset argument (unchanged
                                           from v20)
    yellowRestOfWhiteSNbrs_nil/_cons    — definitional unfolding equations
                                           for the new side effect
    yellowRest_preserves_nonwhite       — the fold never touches an
                                           already-non-white vertex
    yellowRest_white_stays_white_or_yellow
                                         — a white vertex either stays
                                           white or becomes yellow
    yellowRest_ne_c_of_ne_c /
    yellowRest_eq_c_imp                 — for c ∉ {white, yellow}, the
                                           fold can only PRESERVE c, never
                                           manufacture it fresh
    yellowRest_yellow_imp_S             — any freshly-yellowed vertex was
                                           the guard's own w ∈ S
    Lemma12_Part1 / _apply              — unchanged: immediate from
                                           ValidColoring's definitional
                                           equality to runAlgC's output
    AlgC_blue_red_recurse, ..., AlgC_other, AlgC_nil, AlgC_zero
                                         — twelve mechanical unfolding
                                           lemmas, one per leaf-branch
    AlgC_preserved_of_ne_white_yellow   — THE key new lemma: any vertex
                                           not currently white/yellow is
                                           absorbing, proved by strong
                                           induction on fuel mirroring the
                                           nine-branch case split
    AlgC_red_preserved / _black_preserved / _blue_preserved
                                         — one-line corollaries
    AlgC_preserves_red_notS / _blue_in_S / _black_in_S / _yellow_in_S
                                         — the four S-membership
                                           invariants, each by strong
                                           induction on fuel, using the
                                           §2 helper lemmas at every site
                                           where `yellowRestOfWhiteSNbrs`
                                           is invoked
    ValidColoring_red_not_S / _blue_in_S / _yellow_in_S / _black_in_S
                                         — top-level corollaries for the
                                           actual `runAlgC` call, base
                                           case from `initColoring`
    fuelBound, seedFuel, seedFuel_sufficient
                                         — trivial scaffolding, kept for
                                           signature stability with any
                                           downstream files
-/
