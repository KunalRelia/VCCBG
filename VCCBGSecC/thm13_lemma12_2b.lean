/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 12, Part 2(b)

  "When a black vertex is in an odd cycle"

  Source: paper §C.2.2, lines 2546–2591.

  Ported to the FIVE-COLOR `Lemma12_1` Algorithm-C model (white/blue/red/
  black/yellow), matching `thm13_lemma12_2a.lean`.

  KEY INSIGHT: the blue-branch's forcing rule IS
  unconditional in the sense that matters — every `yellow` vertex is
  eventually blackened (the blue/black-branch's `u ∈ S ∧ yellow → black`
  rule has no further gate). Combined with `Lemma12_1`'s own
  `BlueNbrsResolved` invariant (every blue vertex's white-at-creation-
  time `S`-neighbors are immediately yellowed, never left white), this
  gives a genuine `NoBlueBlue` invariant (§4).
-/

public import VCCBGSecC.thm13_lemma12_2a

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

open Color

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. A robust helper: two forced colors on the same vertex clash.
-- ═══════════════════════════════════════════════════════════════════════════

private theorem color_clash
    {C : Coloring V} {x : V} {c1 c2 : Color}
    (h1 : C x = c1) (h2 : C x = c2) (hne : c1 ≠ c2) : False :=
  hne (h1 ▸ h2)

variable (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)

private theorem red_absorb
    (n : ℕ) (C : Coloring V) (v : V) (us : List V) (x : V) (hx : C x = red) :
    AlgC G S nbrOrder n C v us x = red := by
  have h1 : C x ≠ white := by rw [hx]; decide
  have h2 : C x ≠ yellow := by rw [hx]; decide
  rw [AlgC_preserved_of_ne_white_yellow G S nbrOrder n C v us x h1 h2, hx]

private theorem blue_absorb
    (n : ℕ) (C : Coloring V) (v : V) (us : List V) (x : V) (hx : C x = blue) :
    AlgC G S nbrOrder n C v us x = blue :=
  AlgC_blue_preserved G S nbrOrder n C v us x hx

private theorem black_absorb
    (n : ℕ) (C : Coloring V) (v : V) (us : List V) (x : V) (hx : C x = black) :
    AlgC G S nbrOrder n C v us x = black :=
  AlgC_black_preserved G S nbrOrder n C v us x hx

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. A red vertex resolves its own neighbor list.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem AlgC_red_resolves_own_list
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) :
    ∀ n C v us, (∀ y ∈ us, y ≠ v) → C v = red →
      (∀ x, C x = red → x ∉ S) →
      fuelBound C us ≤ n →
      ∀ u ∈ us, u ∈ S →
        (AlgC G S nbrOrder n C v us u = blue ∨
         AlgC G S nbrOrder n C v us u = black) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hwf hvr hCSred hfuel u hu huS
    cases n with
    | zero =>
      exfalso
      cases us with
      | nil => exact List.not_mem_nil hu
      | cons u' rest => simp only [fuelBound, List.length_cons] at hfuel; omega
    | succ m =>
      cases us with
      | nil => exact absurd hu (List.not_mem_nil)
      | cons u' rest =>
        simp only [fuelBound, List.length_cons] at hfuel
        have hu'v : u' ≠ v := hwf u' (List.mem_cons.mpr (Or.inl rfl))
        have hrestwf : ∀ y ∈ rest, y ≠ v := fun y hy => hwf y (List.mem_cons.mpr (Or.inr hy))
        have hvb_false : ¬ C v = blue := by rw [hvr]; decide
        by_cases hu'1 : u' ∈ S ∧ C u' = white
        · rw [AlgC_red_blue_recurse G S nbrOrder hvb_false hvr hu'1]
          set C1 := Function.update C u' blue with hC1def
          have hC1u' : C1 u' = blue := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
          have hC1v : C1 v = red := by
            rw [hC1def, Function.update_apply, ite_eq_right (Ne.symm hu'v)]; exact hvr
          have hC1red : ∀ x, C1 x = red → x ∉ S := by
            intro x hx
            by_cases hxu' : x = u'
            · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
              exact absurd hx (by decide)
            · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
          set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u') with hC1'def
          have hC1'v : C1' v = red := by
            rw [hC1'def, yellowRest_preserves_nonwhite S (nbrOrder u') C1 v
              (by rw [hC1v]; decide)]
            exact hC1v
          have hC1'u' : C1' u' = blue := by
            rw [hC1'def, yellowRest_preserves_nonwhite S (nbrOrder u') C1 u'
              (by rw [hC1u']; decide)]
            exact hC1u'
          have hC1'red : ∀ x, C1' x = red → x ∉ S := by
            intro x hx
            exact hC1red x
              (yellowRest_eq_c_imp S (nbrOrder u') C1 x (by decide) (by decide) hx)
          have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
            resolvedMeasure_update_lt (Or.inl hu'1.2) (by decide)
          have hwc1' : resolvedMeasure C1' ≤ resolvedMeasure C1 :=
            yellowRest_resolvedMeasure_le S (nbrOrder u') C1
          have hwc1'' : resolvedMeasure C1' < resolvedMeasure C := lt_of_le_of_lt hwc1' hwc1
          have hbound1 : fuelBound C1' (nbrOrder u') ≤ m :=
            fuelBound_of_resolvedMeasure_lt hwc1'' (nbrOrder u') (hlen u') (by omega)
          set C2 := AlgC G S nbrOrder m C1' u' (nbrOrder u') with hC2def
          have hC2v : C2 v = red := red_absorb G S nbrOrder m C1' u' (nbrOrder u') v hC1'v
          have hC2u' : C2 u' = blue :=
            blue_absorb G S nbrOrder m C1' u' (nbrOrder u') u' hC1'u'
          have hC2red : ∀ x, C2 x = red → x ∉ S :=
            AlgC_preserves_red_notS G S nbrOrder m C1' u' (nbrOrder u') hC1'red
          have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
            le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1' u' (nbrOrder u'))
              (le_of_lt hwc1'')
          have hfuel' : fuelBound C2 rest ≤ m :=
            fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
          rcases List.mem_cons.mp hu with heq | hu_rest
          · rw [heq]; left; exact blue_absorb G S nbrOrder m C2 v rest u' hC2u'
          · exact ih m (by omega) C2 v rest hrestwf hC2v hC2red hfuel' u hu_rest huS
        · by_cases hu'2 : u' ∈ S ∧ C u' = yellow
          · rw [AlgC_red_black_recurse G S nbrOrder hvb_false hvr hu'1 hu'2]
            set C1 := Function.update C u' black with hC1def
            have hC1u' : C1 u' = black := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
            have hC1v : C1 v = red := by
              rw [hC1def, Function.update_apply, ite_eq_right (Ne.symm hu'v)]; exact hvr
            have hC1red : ∀ x, C1 x = red → x ∉ S := by
              intro x hx
              by_cases hxu' : x = u'
              · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                exact absurd hx (by decide)
              · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
            have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
              resolvedMeasure_update_lt (Or.inr hu'2.2) (by decide)
            have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
              fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
            set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
            have hC2v : C2 v = red := red_absorb G S nbrOrder m C1 u' (nbrOrder u') v hC1v
            have hC2u' : C2 u' = black :=
              black_absorb G S nbrOrder m C1 u' (nbrOrder u') u' hC1u'
            have hC2red : ∀ x, C2 x = red → x ∉ S :=
              AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
            have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
              le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                (le_of_lt hwc1)
            have hfuel' : fuelBound C2 rest ≤ m :=
              fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
            rcases List.mem_cons.mp hu with heq | hu_rest
            · rw [heq]; right; exact black_absorb G S nbrOrder m C2 v rest u' hC2u'
            · exact ih m (by omega) C2 v rest hrestwf hC2v hC2red hfuel' u hu_rest huS
          · rw [AlgC_red_noop G S nbrOrder hvb_false hvr hu'1 hu'2]
            have hfuel' : fuelBound C rest ≤ m :=
              fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
            rcases List.mem_cons.mp hu with heq | hu_rest
            · rw [heq] at huS ⊢
              have hne_white : C u' ≠ white := fun h => hu'1 ⟨huS, h⟩
              have hne_yellow : C u' ≠ yellow := fun h => hu'2 ⟨huS, h⟩
              have hne_red : C u' ≠ red := fun h => hCSred u' h huS
              cases hck : C u' with
              | white => exact absurd hck hne_white
              | yellow => exact absurd hck hne_yellow
              | red => exact absurd hck hne_red
              | blue => left; exact blue_absorb G S nbrOrder m C v rest u' hck
              | black => right; exact black_absorb G S nbrOrder m C v rest u' hck
            · exact ih m (by omega) C v rest hrestwf hvr hCSred hfuel' u hu_rest huS

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. `AlgC_correct_red` — the fully general "some vertex transitions
--     to red anywhere in this call" analogue.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem AlgC_correct_red
    (hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) :
    ∀ n C v us, (∀ y ∈ us, y ≠ v) →
      (∀ x, C x = red → x ∉ S) →
      fuelBound C us ≤ n →
      ∀ p, C p ≠ red → AlgC G S nbrOrder n C v us p = red →
        ∀ w ∈ nbrOrder p, w ∈ S →
          (AlgC G S nbrOrder n C v us w = blue ∨
           AlgC G S nbrOrder n C v us w = black) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hwf hCSred hfuel p hCp hresp
    cases n with
    | zero => rw [AlgC_zero] at hresp; exact absurd hresp hCp
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil] at hresp; exact absurd hresp hCp
      | cons u' rest =>
        simp only [fuelBound, List.length_cons] at hfuel
        have hu'v : u' ≠ v := hwf u' (List.mem_cons.mpr (Or.inl rfl))
        have hrestwf : ∀ y ∈ rest, y ≠ v := fun y hy => hwf y (List.mem_cons.mpr (Or.inr hy))
        by_cases hvb : C v = blue
        · by_cases hu1 : u' ∉ S ∧ C u' = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1] at hresp ⊢
            set C1 := Function.update C u' red with hC1def
            have hC1u' : C1 u' = red := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
            have hC1red : ∀ x, C1 x = red → x ∉ S := by
              intro x hx
              by_cases hxu' : x = u'
              · rw [hxu']; exact hu1.1
              · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
            have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
              resolvedMeasure_update_lt (Or.inl hu1.2) (by decide)
            have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
              fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
            set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
            have hC2red : ∀ x, C2 x = red → x ∉ S :=
              AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
            have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
              le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                (le_of_lt hwc1)
            have hfuel' : fuelBound C2 rest ≤ m :=
              fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
            by_cases hpu' : p = u'
            · rw [hpu']
              intro w hw hwS
              have hResolve :=
                AlgC_red_resolves_own_list G S nbrOrder hlen m C1 u' (nbrOrder u')
                  (fun y hy => hirrefl u' y hy) hC1u' hC1red hbound1 w hw hwS
              rcases hResolve with h | h
              · left; exact blue_absorb G S nbrOrder m C2 v rest w h
              · right; exact black_absorb G S nbrOrder m C2 v rest w h
            · have hCp1 : C1 p ≠ red := by
                rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
              by_cases hCp2 : C2 p = red
              · have hstep := ih m (by omega) C1 u' (nbrOrder u') (hirrefl u') hC1red hbound1
                  p hCp1 hCp2
                intro w hw hwS
                rcases hstep w hw hwS with h | h
                · left; exact blue_absorb G S nbrOrder m C2 v rest w h
                · right; exact black_absorb G S nbrOrder m C2 v rest w h
              · exact ih m (by omega) C2 v rest hrestwf hC2red hfuel' p hCp2 hresp
          · by_cases hu2 : u' ∈ S ∧ C u' = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2] at hresp ⊢
              set C1 := Function.update C u' black with hC1def
              have hC1black : C1 u' = black := by
                rw [hC1def, Function.update_apply, ite_eq_left rfl]
              have hC1red : ∀ x, C1 x = red → x ∉ S := by
                intro x hx
                by_cases hxu' : x = u'
                · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                  exact absurd hx (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
              have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                resolvedMeasure_update_lt (Or.inr hu2.2) (by decide)
              have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
                fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
              set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
              have hC2red : ∀ x, C2 x = red → x ∉ S :=
                AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
              have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                  (le_of_lt hwc1)
              have hfuel' : fuelBound C2 rest ≤ m :=
                fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
              by_cases hpu' : p = u'
              · exfalso
                rw [hpu'] at hresp
                have hC2p : C2 u' = black :=
                  black_absorb G S nbrOrder m C1 u' (nbrOrder u') u' hC1black
                have hfinal : AlgC G S nbrOrder m C2 v rest u' = black :=
                  black_absorb G S nbrOrder m C2 v rest u' hC2p
                rw [hfinal] at hresp; exact absurd hresp (by decide)
              · have hCp1 : C1 p ≠ red := by
                  rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                by_cases hCp2 : C2 p = red
                · have hstep := ih m (by omega) C1 u' (nbrOrder u') (hirrefl u') hC1red hbound1
                    p hCp1 hCp2
                  intro w hw hwS
                  rcases hstep w hw hwS with h | h
                  · left; exact blue_absorb G S nbrOrder m C2 v rest w h
                  · right; exact black_absorb G S nbrOrder m C2 v rest w h
                · exact ih m (by omega) C2 v rest hrestwf hC2red hfuel' p hCp2 hresp
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2] at hresp ⊢
              have hfuel' : fuelBound C rest ≤ m :=
                fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
              exact ih m (by omega) C v rest hrestwf hCSred hfuel' p hCp hresp
        · by_cases hvr : C v = red
          · by_cases hu3 : u' ∈ S ∧ C u' = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu3] at hresp ⊢
              set C1 := Function.update C u' blue with hC1def
              have hC1blue : C1 u' = blue := by
                rw [hC1def, Function.update_apply, ite_eq_left rfl]
              have hC1red : ∀ x, C1 x = red → x ∉ S := by
                intro x hx
                by_cases hxu' : x = u'
                · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                  exact absurd hx (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u') with hC1'def
              have hC1'blue : C1' u' = blue := by
                rw [hC1'def, yellowRest_preserves_nonwhite S (nbrOrder u') C1 u'
                  (by rw [hC1blue]; decide)]
                exact hC1blue
              have hC1'red : ∀ x, C1' x = red → x ∉ S := by
                intro x hx
                exact hC1red x
                  (yellowRest_eq_c_imp S (nbrOrder u') C1 x (by decide) (by decide) hx)
              have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                resolvedMeasure_update_lt (Or.inl hu3.2) (by decide)
              have hwc1' : resolvedMeasure C1' ≤ resolvedMeasure C1 :=
                yellowRest_resolvedMeasure_le S (nbrOrder u') C1
              have hwc1'' : resolvedMeasure C1' < resolvedMeasure C := lt_of_le_of_lt hwc1' hwc1
              have hbound1 : fuelBound C1' (nbrOrder u') ≤ m :=
                fuelBound_of_resolvedMeasure_lt hwc1'' (nbrOrder u') (hlen u') (by omega)
              set C2 := AlgC G S nbrOrder m C1' u' (nbrOrder u') with hC2def
              have hC2red : ∀ x, C2 x = red → x ∉ S :=
                AlgC_preserves_red_notS G S nbrOrder m C1' u' (nbrOrder u') hC1'red
              have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1' u' (nbrOrder u'))
                  (le_of_lt hwc1'')
              have hfuel' : fuelBound C2 rest ≤ m :=
                fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
              by_cases hpu' : p = u'
              · exfalso
                rw [hpu'] at hresp
                have hC2p : C2 u' = blue :=
                  blue_absorb G S nbrOrder m C1' u' (nbrOrder u') u' hC1'blue
                have hfinal : AlgC G S nbrOrder m C2 v rest u' = blue :=
                  blue_absorb G S nbrOrder m C2 v rest u' hC2p
                rw [hfinal] at hresp; exact absurd hresp (by decide)
              · have hCp1 : C1 p ≠ red := by
                  rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                have hCp1' : C1' p ≠ red := by
                  intro hcontra
                  exact hCp1
                    (yellowRest_eq_c_imp S (nbrOrder u') C1 p (by decide) (by decide) hcontra)
                by_cases hCp2 : C2 p = red
                · have hstep := ih m (by omega) C1' u' (nbrOrder u') (hirrefl u') hC1'red hbound1
                    p hCp1' hCp2
                  intro w hw hwS
                  rcases hstep w hw hwS with h | h
                  · left; exact blue_absorb G S nbrOrder m C2 v rest w h
                  · right; exact black_absorb G S nbrOrder m C2 v rest w h
                · exact ih m (by omega) C2 v rest hrestwf hC2red hfuel' p hCp2 hresp
            · by_cases hu4 : u' ∈ S ∧ C u' = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu3 hu4] at hresp ⊢
                set C1 := Function.update C u' black with hC1def
                have hC1black : C1 u' = black := by
                  rw [hC1def, Function.update_apply, ite_eq_left rfl]
                have hC1red : ∀ x, C1 x = red → x ∉ S := by
                  intro x hx
                  by_cases hxu' : x = u'
                  · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                    exact absurd hx (by decide)
                  · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
                have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                  resolvedMeasure_update_lt (Or.inr hu4.2) (by decide)
                have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
                  fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
                set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
                have hC2red : ∀ x, C2 x = red → x ∉ S :=
                  AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
                have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                  le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                    (le_of_lt hwc1)
                have hfuel' : fuelBound C2 rest ≤ m :=
                  fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
                by_cases hpu' : p = u'
                · exfalso
                  rw [hpu'] at hresp
                  have hC2p : C2 u' = black :=
                    black_absorb G S nbrOrder m C1 u' (nbrOrder u') u' hC1black
                  have hfinal : AlgC G S nbrOrder m C2 v rest u' = black :=
                    black_absorb G S nbrOrder m C2 v rest u' hC2p
                  rw [hfinal] at hresp; exact absurd hresp (by decide)
                · have hCp1 : C1 p ≠ red := by
                    rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                  by_cases hCp2 : C2 p = red
                  · have hstep :=
                      ih m (by omega) C1 u' (nbrOrder u') (hirrefl u') hC1red hbound1
                        p hCp1 hCp2
                    intro w hw hwS
                    rcases hstep w hw hwS with h | h
                    · left; exact blue_absorb G S nbrOrder m C2 v rest w h
                    · right; exact black_absorb G S nbrOrder m C2 v rest w h
                  · exact ih m (by omega) C2 v rest hrestwf hC2red hfuel' p hCp2 hresp
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu3 hu4] at hresp ⊢
                have hfuel' : fuelBound C rest ≤ m :=
                  fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
                exact ih m (by omega) C v rest hrestwf hCSred hfuel' p hCp hresp
          · by_cases hvk : C v = black
            · by_cases hu5 : u' ∉ S ∧ C u' = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu5] at hresp ⊢
                set C1 := Function.update C u' red with hC1def
                have hC1u' : C1 u' = red := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
                have hC1red : ∀ x, C1 x = red → x ∉ S := by
                  intro x hx
                  by_cases hxu' : x = u'
                  · rw [hxu']; exact hu5.1
                  · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
                have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                  resolvedMeasure_update_lt (Or.inl hu5.2) (by decide)
                have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
                  fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
                set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
                have hC2red : ∀ x, C2 x = red → x ∉ S :=
                  AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
                have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                  le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                    (le_of_lt hwc1)
                have hfuel' : fuelBound C2 rest ≤ m :=
                  fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
                by_cases hpu' : p = u'
                · rw [hpu']
                  intro w hw hwS
                  have hResolve :=
                    AlgC_red_resolves_own_list G S nbrOrder hlen m C1 u' (nbrOrder u')
                      (fun y hy => hirrefl u' y hy) hC1u' hC1red hbound1 w hw hwS
                  rcases hResolve with h | h
                  · left; exact blue_absorb G S nbrOrder m C2 v rest w h
                  · right; exact black_absorb G S nbrOrder m C2 v rest w h
                · have hCp1 : C1 p ≠ red := by
                    rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                  by_cases hCp2 : C2 p = red
                  · have hstep :=
                      ih m (by omega) C1 u' (nbrOrder u') (hirrefl u') hC1red hbound1
                        p hCp1 hCp2
                    intro w hw hwS
                    rcases hstep w hw hwS with h | h
                    · left; exact blue_absorb G S nbrOrder m C2 v rest w h
                    · right; exact black_absorb G S nbrOrder m C2 v rest w h
                  · exact ih m (by omega) C2 v rest hrestwf hC2red hfuel' p hCp2 hresp
              · by_cases hu6 : u' ∈ S ∧ C u' = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu5 hu6] at hresp ⊢
                  set C1 := Function.update C u' blue with hC1def
                  have hC1u' : C1 u' = blue := by
                    rw [hC1def, Function.update_apply, ite_eq_left rfl]
                  have hC1red : ∀ x, C1 x = red → x ∉ S := by
                    intro x hx
                    by_cases hxu' : x = u'
                    · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                      exact absurd hx (by decide)
                    · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u') with hC1'def
                  have hC1'u' : C1' u' = blue := by
                    rw [hC1'def, yellowRest_preserves_nonwhite S (nbrOrder u') C1 u'
                      (by rw [hC1u']; decide)]
                    exact hC1u'
                  have hC1'red : ∀ x, C1' x = red → x ∉ S := by
                    intro x hx
                    exact hC1red x
                      (yellowRest_eq_c_imp S (nbrOrder u') C1 x (by decide) (by decide) hx)
                  have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                    resolvedMeasure_update_lt (Or.inl hu6.2) (by decide)
                  have hwc1' : resolvedMeasure C1' ≤ resolvedMeasure C1 :=
                    yellowRest_resolvedMeasure_le S (nbrOrder u') C1
                  have hwc1'' : resolvedMeasure C1' < resolvedMeasure C :=
                    lt_of_le_of_lt hwc1' hwc1
                  have hbound1 : fuelBound C1' (nbrOrder u') ≤ m :=
                    fuelBound_of_resolvedMeasure_lt hwc1'' (nbrOrder u') (hlen u') (by omega)
                  set C2 := AlgC G S nbrOrder m C1' u' (nbrOrder u') with hC2def
                  have hC2red : ∀ x, C2 x = red → x ∉ S :=
                    AlgC_preserves_red_notS G S nbrOrder m C1' u' (nbrOrder u') hC1'red
                  have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                    le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1' u' (nbrOrder u'))
                      (le_of_lt hwc1'')
                  have hfuel' : fuelBound C2 rest ≤ m :=
                    fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
                  by_cases hpu' : p = u'
                  · exfalso
                    rw [hpu'] at hresp
                    have hC2p : C2 u' = blue :=
                      blue_absorb G S nbrOrder m C1' u' (nbrOrder u') u' hC1'u'
                    have hfinal : AlgC G S nbrOrder m C2 v rest u' = blue :=
                      blue_absorb G S nbrOrder m C2 v rest u' hC2p
                    rw [hfinal] at hresp; exact absurd hresp (by decide)
                  · have hCp1 : C1 p ≠ red := by
                      rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                    have hCp1' : C1' p ≠ red := by
                      intro hcontra
                      exact hCp1
                        (yellowRest_eq_c_imp S (nbrOrder u') C1 p (by decide) (by decide) hcontra)
                    by_cases hCp2 : C2 p = red
                    · have hstep :=
                        ih m (by omega) C1' u' (nbrOrder u') (hirrefl u') hC1'red hbound1
                          p hCp1' hCp2
                      intro w hw hwS
                      rcases hstep w hw hwS with h | h
                      · left; exact blue_absorb G S nbrOrder m C2 v rest w h
                      · right; exact black_absorb G S nbrOrder m C2 v rest w h
                    · exact ih m (by omega) C2 v rest hrestwf hC2red hfuel' p hCp2 hresp
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu5 hu6] at hresp ⊢
                  have hfuel' : fuelBound C rest ≤ m :=
                    fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
                  exact ih m (by omega) C v rest hrestwf hCSred hfuel' p hCp hresp
            · rw [AlgC_other G S nbrOrder hvb hvr hvk] at hresp ⊢
              have hfuel' : fuelBound C rest ≤ m :=
                fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
              exact ih m (by omega) C v rest hrestwf hCSred hfuel' p hCp hresp

-- ═══════════════════════════════════════════════════════════════════════════
-- §3.5. `AlgC_correct_blue` — the structural mirror of `AlgC_correct_red`
--     for blue.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem AlgC_correct_blue
    (hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) :
    ∀ n C v us, (∀ y ∈ us, y ≠ v) →
      (∀ x, C x = red → x ∉ S) →
      (∀ x ∉ S, C x = white ∨ C x = red) →
      BlueNbrsResolved G S nbrOrder C →
      fuelBound C us ≤ n →
      ∀ p, C p ≠ blue → AlgC G S nbrOrder n C v us p = blue →
        ∀ w ∈ nbrOrder p, w ∈ S →
          (AlgC G S nbrOrder n C v us w = black ∨
           AlgC G S nbrOrder n C v us w = blue) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hwf hCSred hnotS hBinv hfuel p hCp hresp
    cases n with
    | zero => rw [AlgC_zero] at hresp; exact absurd hresp hCp
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil] at hresp; exact absurd hresp hCp
      | cons u' rest =>
        simp only [fuelBound, List.length_cons] at hfuel
        have hu'v : u' ≠ v := hwf u' (List.mem_cons.mpr (Or.inl rfl))
        have hrestwf : ∀ y ∈ rest, y ≠ v := fun y hy => hwf y (List.mem_cons.mpr (Or.inr hy))
        by_cases hvb : C v = blue
        · by_cases hu1 : u' ∉ S ∧ C u' = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1] at hresp ⊢
            set C1 := Function.update C u' red with hC1def
            have hC1red : ∀ x, C1 x = red → x ∉ S := by
              intro x hx
              by_cases hxu' : x = u'
              · rw [hxu']; exact hu1.1
              · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
            have hnotS1 : ∀ x ∉ S, C1 x = white ∨ C1 x = red := by
              intro x hxS
              by_cases hxu' : x = u'
              · right; rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl]
              · rw [hC1def, Function.update_apply, ite_eq_right hxu']; exact hnotS x hxS
            have hBinv1 : BlueNbrsResolved G S nbrOrder C1 :=
              BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hBinv
            have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
              resolvedMeasure_update_lt (Or.inl hu1.2) (by decide)
            have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
              fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
            set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
            have hC2red : ∀ x, C2 x = red → x ∉ S :=
              AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
            have hnotS2 : ∀ x ∉ S, C2 x = white ∨ C2 x = red :=
              AlgC_preserves_notS_white_or_red G S nbrOrder m C1 u' (nbrOrder u') hnotS1
            have hBinv2 : BlueNbrsResolved G S nbrOrder C2 :=
              AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hBinv1
            have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
              le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                (le_of_lt hwc1)
            have hfuel' : fuelBound C2 rest ≤ m :=
              fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
            have hCp1 : C1 p ≠ blue := by
              by_cases hpu' : p = u'
              · rw [hC1def, hpu', Function.update_apply, ite_eq_left rfl]; decide
              · rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
            by_cases hCp2 : C2 p = blue
            · have hstep := ih m (by omega) C1 u' (nbrOrder u') (hirrefl u')
                hC1red hnotS1 hBinv1 hbound1 p hCp1 hCp2
              intro w hw hwS
              rcases hstep w hw hwS with h | h
              · left; exact black_absorb G S nbrOrder m C2 v rest w h
              · right; exact blue_absorb G S nbrOrder m C2 v rest w h
            · exact ih m (by omega) C2 v rest hrestwf hC2red hnotS2 hBinv2 hfuel'
                p hCp2 hresp
          · by_cases hu2 : u' ∈ S ∧ C u' = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2] at hresp ⊢
              set C1 := Function.update C u' black with hC1def
              have hC1red : ∀ x, C1 x = red → x ∉ S := by
                intro x hx
                by_cases hxu' : x = u'
                · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                  exact absurd hx (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
              have hnotS1 : ∀ x ∉ S, C1 x = white ∨ C1 x = red := by
                intro x hxS
                have hxu' : x ≠ u' := fun h => hxS (h ▸ hu2.1)
                rw [hC1def, Function.update_apply, ite_eq_right hxu']; exact hnotS x hxS
              have hBinv1 : BlueNbrsResolved G S nbrOrder C1 :=
                BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hBinv
              have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                resolvedMeasure_update_lt (Or.inr hu2.2) (by decide)
              have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
                fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
              set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
              have hC2red : ∀ x, C2 x = red → x ∉ S :=
                AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
              have hnotS2 : ∀ x ∉ S, C2 x = white ∨ C2 x = red :=
                AlgC_preserves_notS_white_or_red G S nbrOrder m C1 u' (nbrOrder u') hnotS1
              have hBinv2 : BlueNbrsResolved G S nbrOrder C2 :=
                AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hBinv1
              have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                  (le_of_lt hwc1)
              have hfuel' : fuelBound C2 rest ≤ m :=
                fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
              have hCp1 : C1 p ≠ blue := by
                by_cases hpu' : p = u'
                · rw [hC1def, hpu', Function.update_apply, ite_eq_left rfl]; decide
                · rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
              by_cases hCp2 : C2 p = blue
              · have hstep := ih m (by omega) C1 u' (nbrOrder u') (hirrefl u')
                  hC1red hnotS1 hBinv1 hbound1 p hCp1 hCp2
                intro w hw hwS
                rcases hstep w hw hwS with h | h
                · left; exact black_absorb G S nbrOrder m C2 v rest w h
                · right; exact blue_absorb G S nbrOrder m C2 v rest w h
              · exact ih m (by omega) C2 v rest hrestwf hC2red hnotS2 hBinv2 hfuel'
                  p hCp2 hresp
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2] at hresp ⊢
              have hfuel' : fuelBound C rest ≤ m :=
                fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
              exact ih m (by omega) C v rest hrestwf hCSred hnotS hBinv hfuel' p hCp hresp
        · by_cases hvr : C v = red
          · by_cases hu3 : u' ∈ S ∧ C u' = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu3] at hresp ⊢
              set C1 := Function.update C u' blue with hC1def
              have hC1u' : C1 u' = blue := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
              have hC1red : ∀ x, C1 x = red → x ∉ S := by
                intro x hx
                by_cases hxu' : x = u'
                · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                  exact absurd hx (by decide)
                · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
              have hnotS1 : ∀ x ∉ S, C1 x = white ∨ C1 x = red := by
                intro x hxS
                have hxu' : x ≠ u' := fun h => hxS (h ▸ hu3.1)
                rw [hC1def, Function.update_apply, ite_eq_right hxu']; exact hnotS x hxS
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u') with hC1'def
              have hBinv1' : BlueNbrsResolved G S nbrOrder C1' :=
                hC1'def ▸ BlueNbrsResolved_new_blue G S nbrOrder (u := u') hBinv
              have hC1'u' : C1' u' = blue := by
                rw [hC1'def, yellowRest_preserves_nonwhite S (nbrOrder u') C1 u'
                  (by rw [hC1u']; decide)]
                exact hC1u'
              have hC1'red : ∀ x, C1' x = red → x ∉ S := by
                intro x hx
                exact hC1red x
                  (yellowRest_eq_c_imp S (nbrOrder u') C1 x (by decide) (by decide) hx)
              have hnotS1' : ∀ x ∉ S, C1' x = white ∨ C1' x = red := by
                intro x hxS
                rw [hC1'def, yellowRest_preserves_notS S (nbrOrder u') C1 x hxS]
                exact hnotS1 x hxS
              have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                resolvedMeasure_update_lt (Or.inl hu3.2) (by decide)
              have hwc1' : resolvedMeasure C1' ≤ resolvedMeasure C1 :=
                yellowRest_resolvedMeasure_le S (nbrOrder u') C1
              have hwc1'' : resolvedMeasure C1' < resolvedMeasure C := lt_of_le_of_lt hwc1' hwc1
              have hbound1 : fuelBound C1' (nbrOrder u') ≤ m :=
                fuelBound_of_resolvedMeasure_lt hwc1'' (nbrOrder u') (hlen u') (by omega)
              set C2 := AlgC G S nbrOrder m C1' u' (nbrOrder u') with hC2def
              have hC2red : ∀ x, C2 x = red → x ∉ S :=
                AlgC_preserves_red_notS G S nbrOrder m C1' u' (nbrOrder u') hC1'red
              have hnotS2 : ∀ x ∉ S, C2 x = white ∨ C2 x = red :=
                AlgC_preserves_notS_white_or_red G S nbrOrder m C1' u' (nbrOrder u') hnotS1'
              have hBinv2 : BlueNbrsResolved G S nbrOrder C2 :=
                AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1' u' (nbrOrder u') hBinv1'
              have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1' u' (nbrOrder u'))
                  (le_of_lt hwc1'')
              have hfuel' : fuelBound C2 rest ≤ m :=
                fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
              by_cases hpu' : p = u'
              · rw [hpu']
                intro w hw hwS
                have hResolve := AlgC_blue_resolves_own_list G S nbrOrder hlen m C1' u'
                  (nbrOrder u') (fun y hy => hirrefl u' y hy) hC1'u' hC1'red hnotS1'
                  hBinv1' (fun y hy => hy) hbound1 w hw
                rcases hResolve.1 hwS with h | h
                · left; exact black_absorb G S nbrOrder m C2 v rest w h
                · right; exact blue_absorb G S nbrOrder m C2 v rest w h
              · have hCp1 : C1 p ≠ blue := by
                  rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                have hCp1' : C1' p ≠ blue := by
                  intro hcontra
                  exact hCp1
                    (yellowRest_eq_c_imp S (nbrOrder u') C1 p (by decide) (by decide) hcontra)
                by_cases hCp2 : C2 p = blue
                · have hstep := ih m (by omega) C1' u' (nbrOrder u') (hirrefl u')
                    hC1'red hnotS1' hBinv1' hbound1 p hCp1' hCp2
                  intro w hw hwS
                  rcases hstep w hw hwS with h | h
                  · left; exact black_absorb G S nbrOrder m C2 v rest w h
                  · right; exact blue_absorb G S nbrOrder m C2 v rest w h
                · exact ih m (by omega) C2 v rest hrestwf hC2red hnotS2 hBinv2 hfuel'
                    p hCp2 hresp
            · by_cases hu4 : u' ∈ S ∧ C u' = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu3 hu4] at hresp ⊢
                set C1 := Function.update C u' black with hC1def
                have hC1black : C1 u' = black := by
                  rw [hC1def, Function.update_apply, ite_eq_left rfl]
                have hC1red : ∀ x, C1 x = red → x ∉ S := by
                  intro x hx
                  by_cases hxu' : x = u'
                  · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                    exact absurd hx (by decide)
                  · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
                have hnotS1 : ∀ x ∉ S, C1 x = white ∨ C1 x = red := by
                  intro x hxS
                  have hxu' : x ≠ u' := fun h => hxS (h ▸ hu4.1)
                  rw [hC1def, Function.update_apply, ite_eq_right hxu']; exact hnotS x hxS
                have hBinv1 : BlueNbrsResolved G S nbrOrder C1 :=
                  BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hBinv
                have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                  resolvedMeasure_update_lt (Or.inr hu4.2) (by decide)
                have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
                  fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
                set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
                have hC2red : ∀ x, C2 x = red → x ∉ S :=
                  AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
                have hnotS2 : ∀ x ∉ S, C2 x = white ∨ C2 x = red :=
                  AlgC_preserves_notS_white_or_red G S nbrOrder m C1 u' (nbrOrder u') hnotS1
                have hBinv2 : BlueNbrsResolved G S nbrOrder C2 :=
                  AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hBinv1
                have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                  le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                    (le_of_lt hwc1)
                have hfuel' : fuelBound C2 rest ≤ m :=
                  fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
                have hCp1 : C1 p ≠ blue := by
                  by_cases hpu' : p = u'
                  · rw [hC1def, hpu', Function.update_apply, ite_eq_left rfl]; decide
                  · rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                by_cases hCp2 : C2 p = blue
                · have hstep := ih m (by omega) C1 u' (nbrOrder u') (hirrefl u')
                    hC1red hnotS1 hBinv1 hbound1 p hCp1 hCp2
                  intro w hw hwS
                  rcases hstep w hw hwS with h | h
                  · left; exact black_absorb G S nbrOrder m C2 v rest w h
                  · right; exact blue_absorb G S nbrOrder m C2 v rest w h
                · exact ih m (by omega) C2 v rest hrestwf hC2red hnotS2 hBinv2 hfuel'
                    p hCp2 hresp
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu3 hu4] at hresp ⊢
                have hfuel' : fuelBound C rest ≤ m :=
                  fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
                exact ih m (by omega) C v rest hrestwf hCSred hnotS hBinv hfuel' p hCp hresp
          · by_cases hvk : C v = black
            · by_cases hu5 : u' ∉ S ∧ C u' = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu5] at hresp ⊢
                set C1 := Function.update C u' red with hC1def
                have hC1red : ∀ x, C1 x = red → x ∉ S := by
                  intro x hx
                  by_cases hxu' : x = u'
                  · rw [hxu']; exact hu5.1
                  · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
                have hnotS1 : ∀ x ∉ S, C1 x = white ∨ C1 x = red := by
                  intro x hxS
                  by_cases hxu' : x = u'
                  · right; rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl]
                  · rw [hC1def, Function.update_apply, ite_eq_right hxu']; exact hnotS x hxS
                have hBinv1 : BlueNbrsResolved G S nbrOrder C1 :=
                  BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hBinv
                have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                  resolvedMeasure_update_lt (Or.inl hu5.2) (by decide)
                have hbound1 : fuelBound C1 (nbrOrder u') ≤ m :=
                  fuelBound_of_resolvedMeasure_lt hwc1 (nbrOrder u') (hlen u') (by omega)
                set C2 := AlgC G S nbrOrder m C1 u' (nbrOrder u') with hC2def
                have hC2red : ∀ x, C2 x = red → x ∉ S :=
                  AlgC_preserves_red_notS G S nbrOrder m C1 u' (nbrOrder u') hC1red
                have hnotS2 : ∀ x ∉ S, C2 x = white ∨ C2 x = red :=
                  AlgC_preserves_notS_white_or_red G S nbrOrder m C1 u' (nbrOrder u') hnotS1
                have hBinv2 : BlueNbrsResolved G S nbrOrder C2 :=
                  AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hBinv1
                have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                  le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1 u' (nbrOrder u'))
                    (le_of_lt hwc1)
                have hfuel' : fuelBound C2 rest ≤ m :=
                  fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
                have hCp1 : C1 p ≠ blue := by
                  by_cases hpu' : p = u'
                  · rw [hC1def, hpu', Function.update_apply, ite_eq_left rfl]; decide
                  · rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                by_cases hCp2 : C2 p = blue
                · have hstep := ih m (by omega) C1 u' (nbrOrder u') (hirrefl u')
                    hC1red hnotS1 hBinv1 hbound1 p hCp1 hCp2
                  intro w hw hwS
                  rcases hstep w hw hwS with h | h
                  · left; exact black_absorb G S nbrOrder m C2 v rest w h
                  · right; exact blue_absorb G S nbrOrder m C2 v rest w h
                · exact ih m (by omega) C2 v rest hrestwf hC2red hnotS2 hBinv2 hfuel'
                    p hCp2 hresp
              · by_cases hu6 : u' ∈ S ∧ C u' = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu5 hu6] at hresp ⊢
                  set C1 := Function.update C u' blue with hC1def
                  have hC1u' : C1 u' = blue := by
                    rw [hC1def, Function.update_apply, ite_eq_left rfl]
                  have hC1red : ∀ x, C1 x = red → x ∉ S := by
                    intro x hx
                    by_cases hxu' : x = u'
                    · rw [hC1def, hxu', Function.update_apply, ite_eq_left rfl] at hx
                      exact absurd hx (by decide)
                    · rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hCSred x hx
                  have hnotS1 : ∀ x ∉ S, C1 x = white ∨ C1 x = red := by
                    intro x hxS
                    have hxu' : x ≠ u' := fun h => hxS (h ▸ hu6.1)
                    rw [hC1def, Function.update_apply, ite_eq_right hxu']; exact hnotS x hxS
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u') with hC1'def
                  have hBinv1' : BlueNbrsResolved G S nbrOrder C1' :=
                    hC1'def ▸ BlueNbrsResolved_new_blue G S nbrOrder (u := u') hBinv
                  have hC1'u' : C1' u' = blue := by
                    rw [hC1'def, yellowRest_preserves_nonwhite S (nbrOrder u') C1 u'
                      (by rw [hC1u']; decide)]
                    exact hC1u'
                  have hC1'red : ∀ x, C1' x = red → x ∉ S := by
                    intro x hx
                    exact hC1red x
                      (yellowRest_eq_c_imp S (nbrOrder u') C1 x (by decide) (by decide) hx)
                  have hnotS1' : ∀ x ∉ S, C1' x = white ∨ C1' x = red := by
                    intro x hxS
                    rw [hC1'def, yellowRest_preserves_notS S (nbrOrder u') C1 x hxS]
                    exact hnotS1 x hxS
                  have hwc1 : resolvedMeasure C1 < resolvedMeasure C :=
                    resolvedMeasure_update_lt (Or.inl hu6.2) (by decide)
                  have hwc1' : resolvedMeasure C1' ≤ resolvedMeasure C1 :=
                    yellowRest_resolvedMeasure_le S (nbrOrder u') C1
                  have hwc1'' : resolvedMeasure C1' < resolvedMeasure C :=
                    lt_of_le_of_lt hwc1' hwc1
                  have hbound1 : fuelBound C1' (nbrOrder u') ≤ m :=
                    fuelBound_of_resolvedMeasure_lt hwc1'' (nbrOrder u') (hlen u') (by omega)
                  set C2 := AlgC G S nbrOrder m C1' u' (nbrOrder u') with hC2def
                  have hC2red : ∀ x, C2 x = red → x ∉ S :=
                    AlgC_preserves_red_notS G S nbrOrder m C1' u' (nbrOrder u') hC1'red
                  have hnotS2 : ∀ x ∉ S, C2 x = white ∨ C2 x = red :=
                    AlgC_preserves_notS_white_or_red G S nbrOrder m C1' u' (nbrOrder u') hnotS1'
                  have hBinv2 : BlueNbrsResolved G S nbrOrder C2 :=
                    AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1' u' (nbrOrder u') hBinv1'
                  have hwc2 : resolvedMeasure C2 ≤ resolvedMeasure C :=
                    le_trans (AlgC_resolvedMeasure_le G S nbrOrder m C1' u' (nbrOrder u'))
                      (le_of_lt hwc1'')
                  have hfuel' : fuelBound C2 rest ≤ m :=
                    fuelBound_of_resolvedMeasure_le hwc2 rest (by omega)
                  by_cases hpu' : p = u'
                  · rw [hpu']
                    intro w hw hwS
                    have hResolve := AlgC_blue_resolves_own_list G S nbrOrder hlen m C1' u'
                      (nbrOrder u') (fun y hy => hirrefl u' y hy) hC1'u' hC1'red hnotS1'
                      hBinv1' (fun y hy => hy) hbound1 w hw
                    rcases hResolve.1 hwS with h | h
                    · left; exact black_absorb G S nbrOrder m C2 v rest w h
                    · right; exact blue_absorb G S nbrOrder m C2 v rest w h
                  · have hCp1 : C1 p ≠ blue := by
                      rw [hC1def, Function.update_apply, ite_eq_right hpu']; exact hCp
                    have hCp1' : C1' p ≠ blue := by
                      intro hcontra
                      exact hCp1
                        (yellowRest_eq_c_imp S (nbrOrder u') C1 p (by decide) (by decide) hcontra)
                    by_cases hCp2 : C2 p = blue
                    · have hstep := ih m (by omega) C1' u' (nbrOrder u') (hirrefl u')
                        hC1'red hnotS1' hBinv1' hbound1 p hCp1' hCp2
                      intro w hw hwS
                      rcases hstep w hw hwS with h | h
                      · left; exact black_absorb G S nbrOrder m C2 v rest w h
                      · right; exact blue_absorb G S nbrOrder m C2 v rest w h
                    · exact ih m (by omega) C2 v rest hrestwf hC2red hnotS2 hBinv2 hfuel'
                        p hCp2 hresp
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu5 hu6] at hresp ⊢
                  have hfuel' : fuelBound C rest ≤ m :=
                    fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
                  exact ih m (by omega) C v rest hrestwf hCSred hnotS hBinv hfuel' p hCp hresp
            · rw [AlgC_other G S nbrOrder hvb hvr hvk] at hresp ⊢
              have hfuel' : fuelBound C rest ≤ m :=
                fuelBound_of_resolvedMeasure_le (le_refl _) rest (by omega)
              exact ih m (by omega) C v rest hrestwf hCSred hnotS hBinv hfuel' p hCp hresp

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. `NoBlueBlue` — no two adjacent vertices are ever simultaneously
--     blue. FIXED (v8.3): the two "fresh transition here" cases
--     (red-branch's / black-branch's `u ∈ S ∧ white → blue` rules) no
--     longer use `by_cases hxu' : x = u'` + `subst`, which silently
--     eliminated `u'`; every `= u'` fact is now consumed via `rw`
--     directly on the specific hypothesis needed, never via `subst`.
-- ═══════════════════════════════════════════════════════════════════════════

/-- No two adjacent vertices are simultaneously blue under `C`. -/
public def NoBlueBlue (G : SimpleGraph V) (C : Coloring V) : Prop :=
  ∀ x y, G.Adj x y → C x = blue → C y = blue → False

public theorem AlgC_preserves_NoBlueBlue
    (hOrder : OrderMatchesAdj G nbrOrder) :
    ∀ n C v us, BlueNbrsResolved G S nbrOrder C → NoBlueBlue G C →
      NoBlueBlue G (AlgC G S nbrOrder n C v us) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C v us hBinv hNBB
    cases n with
    | zero => rw [AlgC_zero]; exact hNBB
    | succ m =>
      cases us with
      | nil => rw [AlgC_nil]; exact hNBB
      | cons u' rest =>
        by_cases hvb : C v = blue
        · by_cases hu1 : u' ∉ S ∧ C u' = white
          · rw [AlgC_blue_red_recurse G S nbrOrder hvb hu1]
            set C1 := Function.update C u' red with hC1def
            have hC1u' : C1 u' = red := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
            have hNBB1 : NoBlueBlue G C1 := by
              intro x y hadj hx hy
              have hxu' : x ≠ u' := fun h => by rw [h, hC1u'] at hx; exact absurd hx (by decide)
              have hyu' : y ≠ u' := fun h => by rw [h, hC1u'] at hy; exact absurd hy (by decide)
              have hCx : C x = blue := by
                rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hx
              have hCy : C y = blue := by
                rw [hC1def, Function.update_apply, ite_eq_right hyu'] at hy; exact hy
              exact hNBB x y hadj hCx hCy
            have hBinv1 : BlueNbrsResolved G S nbrOrder C1 :=
              BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hBinv
            have hNBB2 := ih m (by omega) C1 u' (nbrOrder u') hBinv1 hNBB1
            have hBinv2 :
                BlueNbrsResolved G S nbrOrder (AlgC G S nbrOrder m C1 u' (nbrOrder u')) :=
              AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hBinv1
            exact ih m (by omega) (AlgC G S nbrOrder m C1 u' (nbrOrder u')) v rest hBinv2 hNBB2
          · by_cases hu2 : u' ∈ S ∧ C u' = yellow
            · rw [AlgC_blue_black_recurse G S nbrOrder hvb hu1 hu2]
              set C1 := Function.update C u' black with hC1def
              have hC1u' : C1 u' = black := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
              have hNBB1 : NoBlueBlue G C1 := by
                intro x y hadj hx hy
                have hxu' : x ≠ u' := fun h => by rw [h, hC1u'] at hx; exact absurd hx (by decide)
                have hyu' : y ≠ u' := fun h => by rw [h, hC1u'] at hy; exact absurd hy (by decide)
                have hCx : C x = blue := by
                  rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hx
                have hCy : C y = blue := by
                  rw [hC1def, Function.update_apply, ite_eq_right hyu'] at hy; exact hy
                exact hNBB x y hadj hCx hCy
              have hBinv1 : BlueNbrsResolved G S nbrOrder C1 :=
                BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hBinv
              have hNBB2 := ih m (by omega) C1 u' (nbrOrder u') hBinv1 hNBB1
              have hBinv2 :
                  BlueNbrsResolved G S nbrOrder (AlgC G S nbrOrder m C1 u' (nbrOrder u')) :=
                AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hBinv1
              exact ih m (by omega) (AlgC G S nbrOrder m C1 u' (nbrOrder u')) v rest hBinv2 hNBB2
            · rw [AlgC_blue_noop G S nbrOrder hvb hu1 hu2]
              exact ih m (by omega) C v rest hBinv hNBB
        · by_cases hvr : C v = red
          · by_cases hu3 : u' ∈ S ∧ C u' = white
            · rw [AlgC_red_blue_recurse G S nbrOrder hvb hvr hu3]
              set C1 := Function.update C u' blue with hC1def
              have hC1u' : C1 u' = blue := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
              -- `NoBlueBlue` for `C1`: the ONE new blue vertex is `u'`
              -- itself. Any pair (x,y) both blue in `C1`, adjacent: if
              -- NEITHER is `u'`, they were already both blue in `C`,
              -- contradicting `hNBB` directly. If ONE of them is `u'`,
              -- the OTHER (call it `z`, `≠ u'`, adjacent to `u'`,
              -- blue-in-C) forces — via `BlueNbrsResolved` applied to
              -- `z` and its `S`-neighbor `u'` (`hu3.1 : u' ∈ S`) —
              -- `C u' ≠ white`, directly contradicting `hu3.2`.
              have hNBB1 : NoBlueBlue G C1 := by
                intro x y hadj hx hy
                by_cases hxu' : x = u'
                · rw [hxu'] at hadj
                  by_cases hyu' : y = u'
                  · rw [hyu'] at hadj; exact G.loopless.irrefl u' hadj
                  · have hCy : C y = blue := by
                      rw [hC1def, Function.update_apply, ite_eq_right hyu'] at hy; exact hy
                    have hu'nbrY : u' ∈ nbrOrder y := (hOrder y u').mpr hadj.symm
                    exact (hBinv y hCy u' hu'nbrY hu3.1) hu3.2
                · by_cases hyu' : y = u'
                  · rw [hyu'] at hadj
                    have hCx : C x = blue := by
                      rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hx
                    have hu'nbrX : u' ∈ nbrOrder x := (hOrder x u').mpr hadj
                    exact (hBinv x hCx u' hu'nbrX hu3.1) hu3.2
                  · have hCx : C x = blue := by
                      rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hx
                    have hCy : C y = blue := by
                      rw [hC1def, Function.update_apply, ite_eq_right hyu'] at hy; exact hy
                    exact hNBB x y hadj hCx hCy
              set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u') with hC1'def
              have hNBB1' : NoBlueBlue G C1' := by
                intro x y hadj hx hy
                have hCx : C1 x = blue :=
                  yellowRest_eq_c_imp S (nbrOrder u') C1 x (by decide) (by decide) hx
                have hCy : C1 y = blue :=
                  yellowRest_eq_c_imp S (nbrOrder u') C1 y (by decide) (by decide) hy
                exact hNBB1 x y hadj hCx hCy
              have hBinv1' : BlueNbrsResolved G S nbrOrder C1' :=
                hC1'def ▸ BlueNbrsResolved_new_blue G S nbrOrder (u := u') hBinv
              have hNBB2 := ih m (by omega) C1' u' (nbrOrder u') hBinv1' hNBB1'
              have hBinv2 :
                  BlueNbrsResolved G S nbrOrder (AlgC G S nbrOrder m C1' u' (nbrOrder u')) :=
                AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1' u' (nbrOrder u') hBinv1'
              exact ih m (by omega) (AlgC G S nbrOrder m C1' u' (nbrOrder u')) v rest hBinv2 hNBB2
            · by_cases hu4 : u' ∈ S ∧ C u' = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu3 hu4]
                set C1 := Function.update C u' black with hC1def
                have hC1u' : C1 u' = black := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
                have hNBB1 : NoBlueBlue G C1 := by
                  intro x y hadj hx hy
                  have hxu' : x ≠ u' := fun h => by
                    rw [h, hC1u'] at hx; exact absurd hx (by decide)
                  have hyu' : y ≠ u' := fun h => by
                    rw [h, hC1u'] at hy; exact absurd hy (by decide)
                  have hCx : C x = blue := by
                    rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hx
                  have hCy : C y = blue := by
                    rw [hC1def, Function.update_apply, ite_eq_right hyu'] at hy; exact hy
                  exact hNBB x y hadj hCx hCy
                have hBinv1 : BlueNbrsResolved G S nbrOrder C1 :=
                  BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hBinv
                have hNBB2 := ih m (by omega) C1 u' (nbrOrder u') hBinv1 hNBB1
                have hBinv2 :
                    BlueNbrsResolved G S nbrOrder (AlgC G S nbrOrder m C1 u' (nbrOrder u')) :=
                  AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hBinv1
                exact ih m (by omega) (AlgC G S nbrOrder m C1 u' (nbrOrder u')) v rest hBinv2 hNBB2
              · rw [AlgC_red_noop G S nbrOrder hvb hvr hu3 hu4]
                exact ih m (by omega) C v rest hBinv hNBB
          · by_cases hvk : C v = black
            · by_cases hu5 : u' ∉ S ∧ C u' = white
              · rw [AlgC_black_red_recurse G S nbrOrder hvb hvr hvk hu5]
                set C1 := Function.update C u' red with hC1def
                have hC1u' : C1 u' = red := by rw [hC1def, Function.update_apply, ite_eq_left rfl]
                have hNBB1 : NoBlueBlue G C1 := by
                  intro x y hadj hx hy
                  have hxu' : x ≠ u' := fun h => by
                    rw [h, hC1u'] at hx; exact absurd hx (by decide)
                  have hyu' : y ≠ u' := fun h => by
                    rw [h, hC1u'] at hy; exact absurd hy (by decide)
                  have hCx : C x = blue := by
                    rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hx
                  have hCy : C y = blue := by
                    rw [hC1def, Function.update_apply, ite_eq_right hyu'] at hy; exact hy
                  exact hNBB x y hadj hCx hCy
                have hBinv1 : BlueNbrsResolved G S nbrOrder C1 :=
                  BlueNbrsResolved_update_absorbing G S nbrOrder (by decide) (by decide) hBinv
                have hNBB2 := ih m (by omega) C1 u' (nbrOrder u') hBinv1 hNBB1
                have hBinv2 :
                    BlueNbrsResolved G S nbrOrder (AlgC G S nbrOrder m C1 u' (nbrOrder u')) :=
                  AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1 u' (nbrOrder u') hBinv1
                exact ih m (by omega) (AlgC G S nbrOrder m C1 u' (nbrOrder u')) v rest hBinv2 hNBB2
              · by_cases hu6 : u' ∈ S ∧ C u' = white
                · rw [AlgC_black_blue_recurse G S nbrOrder hvb hvr hvk hu5 hu6]
                  set C1 := Function.update C u' blue with hC1def
                  have hC1u' : C1 u' = blue := by
                    rw [hC1def, Function.update_apply, ite_eq_left rfl]
                  have hNBB1 : NoBlueBlue G C1 := by
                    intro x y hadj hx hy
                    by_cases hxu' : x = u'
                    · rw [hxu'] at hadj
                      by_cases hyu' : y = u'
                      · rw [hyu'] at hadj; exact G.loopless.irrefl u' hadj
                      · have hCy : C y = blue := by
                          rw [hC1def, Function.update_apply, ite_eq_right hyu'] at hy; exact hy
                        have hu'nbrY : u' ∈ nbrOrder y := (hOrder y u').mpr hadj.symm
                        exact (hBinv y hCy u' hu'nbrY hu6.1) hu6.2
                    · by_cases hyu' : y = u'
                      · rw [hyu'] at hadj
                        have hCx : C x = blue := by
                          rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hx
                        have hu'nbrX : u' ∈ nbrOrder x := (hOrder x u').mpr hadj
                        exact (hBinv x hCx u' hu'nbrX hu6.1) hu6.2
                      · have hCx : C x = blue := by
                          rw [hC1def, Function.update_apply, ite_eq_right hxu'] at hx; exact hx
                        have hCy : C y = blue := by
                          rw [hC1def, Function.update_apply, ite_eq_right hyu'] at hy; exact hy
                        exact hNBB x y hadj hCx hCy
                  set C1' := yellowRestOfWhiteSNbrs S C1 (nbrOrder u') with hC1'def
                  have hNBB1' : NoBlueBlue G C1' := by
                    intro x y hadj hx hy
                    have hCx : C1 x = blue :=
                      yellowRest_eq_c_imp S (nbrOrder u') C1 x (by decide) (by decide) hx
                    have hCy : C1 y = blue :=
                      yellowRest_eq_c_imp S (nbrOrder u') C1 y (by decide) (by decide) hy
                    exact hNBB1 x y hadj hCx hCy
                  have hBinv1' : BlueNbrsResolved G S nbrOrder C1' :=
                    hC1'def ▸ BlueNbrsResolved_new_blue G S nbrOrder (u := u') hBinv
                  have hNBB2 := ih m (by omega) C1' u' (nbrOrder u') hBinv1' hNBB1'
                  have hBinv2 :
                      BlueNbrsResolved G S nbrOrder (AlgC G S nbrOrder m C1' u' (nbrOrder u')) :=
                    AlgC_preserves_BlueNbrsResolved G S nbrOrder m C1' u' (nbrOrder u') hBinv1'
                  exact ih m (by omega) (AlgC G S nbrOrder m C1' u' (nbrOrder u')) v rest
                    hBinv2 hNBB2
                · rw [AlgC_black_noop G S nbrOrder hvb hvr hvk hu5 hu6]
                  exact ih m (by omega) C v rest hBinv hNBB
            · rw [AlgC_other G S nbrOrder hvb hvr hvk]
              exact ih m (by omega) C v rest hBinv hNBB

/-- `initColoring` has exactly one blue vertex, so trivially `NoBlueBlue`. -/
public theorem initColoring_NoBlueBlue (v0 : V) :
    NoBlueBlue G (initColoring G S nbrOrder v0) := by
  intro x y hadj hx hy
  unfold initColoring at hx hy
  have hx' : (Function.update (fun _ : V => white) v0 blue) x = blue :=
    yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) x
      (by decide) (by decide) hx
  have hy' : (Function.update (fun _ : V => white) v0 blue) y = blue :=
    yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) y
      (by decide) (by decide) hy
  by_cases hxv : x = v0
  · by_cases hyv : y = v0
    · rw [hxv, hyv] at hadj; exact G.loopless.irrefl v0 hadj
    · rw [Function.update_apply, ite_eq_right hyv] at hy'; exact absurd hy' (by decide)
  · rw [Function.update_apply, ite_eq_right hxv] at hx'; exact absurd hx' (by decide)

/-- **Top-level `NoBlueBlue`**: under the actual `runAlgC` output, no two
    adjacent vertices are simultaneously blue. -/
public theorem runAlgC_NoBlueBlue
    (hOrder : OrderMatchesAdj G nbrOrder) (fuel : ℕ) (v0 : V) :
    NoBlueBlue G (runAlgC G S nbrOrder fuel v0) := by
  unfold runAlgC
  exact AlgC_preserves_NoBlueBlue G S nbrOrder hOrder fuel (initColoring G S nbrOrder v0) v0
    (nbrOrder v0) (initColoring_BlueNbrsResolved G S nbrOrder v0)
    (initColoring_NoBlueBlue G S nbrOrder v0)

/-- The same fact, stated for `ValidColoring`'s coloring `C` directly. -/
public theorem ValidColoring_NoBlueBlue
    {v0 : V} {fuel : ℕ} {C : Coloring V}
    (hOrder : OrderMatchesAdj G nbrOrder)
    (hVC : ValidColoring G S nbrOrder v0 fuel C) :
    NoBlueBlue G C := by
  unfold ValidColoring at hVC
  rw [hVC]
  exact runAlgC_NoBlueBlue G S nbrOrder hOrder fuel v0

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Top-level packagings for the actual `runAlgC` call.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem runAlgC_red_neighbors_resolved
    (hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {v0 : V} {fuel : ℕ}
    (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {p : V} (hp : runAlgC G S nbrOrder fuel v0 p = red) :
    ∀ w ∈ nbrOrder p, w ∈ S →
      (runAlgC G S nbrOrder fuel v0 w = blue ∨
       runAlgC G S nbrOrder fuel v0 w = black) := by
  unfold runAlgC at hp ⊢
  have hus : ∀ y ∈ nbrOrder v0, y ≠ v0 := hirrefl v0
  have hinit_ne_red : ∀ x, initColoring G S nbrOrder v0 x ≠ red := by
    intro x hx
    unfold initColoring at hx
    have hx' : (Function.update (fun _ : V => white) v0 blue) x = red :=
      yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) x
        (by decide) (by decide) hx
    by_cases hxv : x = v0
    · rw [hxv, Function.update_apply, ite_eq_left rfl] at hx'; exact absurd hx' (by decide)
    · rw [Function.update_apply, ite_eq_right hxv] at hx'; exact absurd hx' (by decide)
  have hCSred0 : ∀ x, initColoring G S nbrOrder v0 x = red → x ∉ S :=
    fun x hx => absurd hx (hinit_ne_red x)
  exact AlgC_correct_red G S nbrOrder hirrefl hlen fuel (initColoring G S nbrOrder v0) v0
    (nbrOrder v0) hus hCSred0 hfuel p (hinit_ne_red p) hp

public theorem runAlgC_blue_neighbors_resolved_general
    (hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {v0 : V} (hv0 : v0 ∈ S) {fuel : ℕ}
    (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {p : V} (hp : runAlgC G S nbrOrder fuel v0 p = blue) :
    ∀ w ∈ nbrOrder p, w ∈ S →
      (runAlgC G S nbrOrder fuel v0 w = black ∨
       runAlgC G S nbrOrder fuel v0 w = blue) := by
  unfold runAlgC at hp ⊢
  have hus : ∀ y ∈ nbrOrder v0, y ≠ v0 := hirrefl v0
  have hinit_ne_red : ∀ x, initColoring G S nbrOrder v0 x ≠ red := by
    intro x hx
    unfold initColoring at hx
    have hx' : (Function.update (fun _ : V => white) v0 blue) x = red :=
      yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) x
        (by decide) (by decide) hx
    by_cases hxv : x = v0
    · rw [hxv, Function.update_apply, ite_eq_left rfl] at hx'; exact absurd hx' (by decide)
    · rw [Function.update_apply, ite_eq_right hxv] at hx'; exact absurd hx' (by decide)
  have hCSred0 : ∀ x, initColoring G S nbrOrder v0 x = red → x ∉ S :=
    fun x hx => absurd hx (hinit_ne_red x)
  have hwhite0 : ∀ x ∉ S, initColoring G S nbrOrder v0 x = white := by
    intro x hxS
    have hxv0 : x ≠ v0 := fun h => hxS (h ▸ hv0)
    unfold initColoring
    rw [yellowRest_preserves_notS S (nbrOrder v0)
      (Function.update (fun _ : V => white) v0 blue) x hxS]
    rw [Function.update_apply, ite_eq_right hxv0]
  have hnotS0 : ∀ x ∉ S,
      initColoring G S nbrOrder v0 x = white ∨ initColoring G S nbrOrder v0 x = red :=
    fun x hxS => Or.inl (hwhite0 x hxS)
  have hBinv0 : BlueNbrsResolved G S nbrOrder (initColoring G S nbrOrder v0) :=
    initColoring_BlueNbrsResolved G S nbrOrder v0
  by_cases hpv0 : p = v0
  · rw [hpv0]
    intro w hw hwS
    rcases (runAlgC_seed_neighbors_resolved G S nbrOrder hirrefl hlen hv0 hfuel w hw).1 hwS
      with h | h
    · left; exact h
    · right; exact h
  · have hCp0 : initColoring G S nbrOrder v0 p ≠ blue := by
      unfold initColoring
      intro hcontra
      have hc' : (Function.update (fun _ : V => white) v0 blue) p = blue :=
        yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) p
          (by decide) (by decide) hcontra
      rw [Function.update_apply, ite_eq_right hpv0] at hc'
      exact absurd hc' (by decide)
    exact AlgC_correct_blue G S nbrOrder hirrefl hlen fuel (initColoring G S nbrOrder v0) v0
      (nbrOrder v0) hus hCSred0 hnotS0 hBinv0 hfuel p hCp0 hp

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. `hV3_derived` and Theorem 1 (Conflict Resolution) — UNCONDITIONAL
--     `black` conclusion, fixed to pass `nbrOrder` explicitly to
--     `ValidColoring_NoBlueBlue`.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem hV3_derived
    {v0 : V} {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    {p q : V} (hadj : G.Adj p q) (hCp : C p = red) (hqS : q ∈ S)
    (hqNotBlack : C q ≠ black) :
    C q = blue := by
  unfold ValidColoring at hVC
  have hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x := hOrder.irrefl
  have hCp' : runAlgC G S nbrOrder fuel v0 p = red := hVC ▸ hCp
  have key := runAlgC_red_neighbors_resolved G S nbrOrder hirrefl hlen hfuel hCp'
  have hqOrder : q ∈ nbrOrder p := (hOrder p q).mpr hadj
  have hqNotBlack' : runAlgC G S nbrOrder fuel v0 q ≠ black := by
    intro hbb; exact hqNotBlack (hVC ▸ hbb)
  rcases key q hqOrder hqS with h | h
  · exact hVC ▸ h
  · exact absurd h hqNotBlack'

/-- **Theorem 1 (Conflict Resolution)**: if `w ∈ S` has a neighbor `u`
    that ends up blue in the final coloring `C` (seeded at `v0 ∈ S`),
    then `w` itself is forced black, unconditionally. -/
public theorem Lemma12_Part2b_conflict
    {v0 : V} (hv0 : v0 ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    {w u : V} (hwS : w ∈ S)
    (hadj : G.Adj u w) (hCu : C u = blue) :
    C w = black := by
  unfold ValidColoring at hVC
  have hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x := hOrder.irrefl
  have hCu' : runAlgC G S nbrOrder fuel v0 u = blue := hVC ▸ hCu
  have key := runAlgC_blue_neighbors_resolved_general G S nbrOrder hirrefl hlen hv0 hfuel hCu'
  have hwOrder : w ∈ nbrOrder u := (hOrder u w).mpr hadj
  rcases key w hwOrder hwS with h | h
  · exact hVC ▸ h
  · exfalso
    have hCw_blue : C w = blue := hVC ▸ h
    -- have hNoBlueBlue : NoBlueBlue G C :=
    --   ValidColoring_NoBlueBlue G S nbrOrder hOrder hVC
    -- exact hNoBlueBlue u w hadj hCu hCw_blue
    exact ValidColoring_NoBlueBlue G S nbrOrder hOrder hVC u w hadj hCu hCw_blue


-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Theorem 2 — Odd cycles resist proper 2-coloring. Pure
--     combinatorics, unchanged from every prior version.
-- ═══════════════════════════════════════════════════════════════════════════

public def BR (C : Coloring V) (x : V) : Prop := C x = blue ∨ C x = red

private theorem BR_eq_of_ne_ne
    {C : Coloring V} {x y z : V}
    (hx : BR C x) (hy : BR C y) (hz : BR C z)
    (hxy : C x ≠ C y) (hxz : C x ≠ C z) :
    C y = C z := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
    simp only [hx, hy, hz] at hxy hxz ⊢ <;>
    first | rfl | exact absurd rfl hxy | exact absurd rfl hxz

private theorem parity_alternation
    {n : ℕ} {C : Coloring V} {c : ℕ → V}
    (hBR : ∀ k, k < n → BR C (c k))
    (hne : ∀ k, k + 1 < n → C (c k) ≠ C (c (k + 1))) :
    ∀ k, k < n →
      (k % 2 = 0 → C (c k) = C (c 0)) ∧ (k % 2 = 1 → C (c k) ≠ C (c 0)) := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨fun _ => rfl, fun h => absurd h (by decide)⟩
  | succ m ih =>
      intro hbound
      have hm_lt : m < n := by omega
      have hm1_lt : m + 1 < n := hbound
      obtain ⟨ihE, ihO⟩ := ih hm_lt
      have hstep : C (c m) ≠ C (c (m + 1)) := hne m hm1_lt
      have hBR0   : BR C (c 0)       := hBR 0 (by omega)
      have hBRm   : BR C (c m)       := hBR m hm_lt
      have hBRm1  : BR C (c (m + 1)) := hBR (m + 1) hm1_lt
      constructor
      · intro heq
        have hmodd : m % 2 = 1 := by omega
        have hCm_ne : C (c m) ≠ C (c 0) := ihO hmodd
        exact (BR_eq_of_ne_ne hBRm hBR0 hBRm1 hCm_ne hstep).symm
      · intro hodd
        have hmeven : m % 2 = 0 := by omega
        have hCm_eq : C (c m) = C (c 0) := ihE hmeven
        intro hcontra
        exact hstep (hCm_eq.trans hcontra.symm)

public theorem Lemma12_Part2b_oddcycle_no_proper_2coloring
    {n : ℕ} (hn_odd : n % 2 = 1) (hn_pos : 0 < n)
    {C : Coloring V} {c : ℕ → V}
    (hBR : ∀ k, k < n → BR C (c k))
    (hadj_wrap : C (c (n - 1)) ≠ C (c 0))
    (hne : ∀ k, k + 1 < n → C (c k) ≠ C (c (k + 1))) :
    False := by
  have hlast_lt : n - 1 < n := by omega
  obtain ⟨hE, _⟩ := parity_alternation hBR hne (n - 1) hlast_lt
  have hlast_even : (n - 1) % 2 = 0 := by omega
  exact hadj_wrap (hE hlast_even)

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. Corollary: at least one cycle vertex must be black.
-- ═══════════════════════════════════════════════════════════════════════════

public theorem Lemma12_Part2b_some_black
    {v0 : V} (hv0 : v0 ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    {n : ℕ} (hn_odd : n % 2 = 1) (hn_pos : 0 < n)
    {c : ℕ → V}
    (hadj : ∀ k, G.Adj (c k) (c ((k + 1) % n)))
    (hBR : ∀ k, k < n → BR C (c k))
    (hSVC : VCover G S) :
    False := by
  have hVC' := hVC
  unfold ValidColoring at hVC'
  have hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x := hOrder.irrefl
  have hNBB : NoBlueBlue G C := ValidColoring_NoBlueBlue G S nbrOrder hOrder hVC
  have hRedNotS : ∀ {p : V}, C p = red → p ∉ S := by
    intro p hp
    exact ValidColoring_red_not_S G S nbrOrder hVC hp
  have hne : ∀ k, k + 1 < n → C (c k) ≠ C (c (k + 1)) := by
    intro k hk
    have hk' : (k + 1) % n = k + 1 := Nat.mod_eq_of_lt hk
    have hadjk : G.Adj (c k) (c (k + 1)) := hk' ▸ hadj k
    rcases hBR k (by omega) with hCk | hCk
    · intro heq
      have hCk' : runAlgC G S nbrOrder fuel v0 (c k) = blue := hVC' ▸ hCk
      have key := runAlgC_blue_neighbors_resolved_general G S nbrOrder hirrefl hlen hv0 hfuel hCk'
      have hOrderMem : c (k + 1) ∈ nbrOrder (c k) := (hOrder (c k) (c (k + 1))).mpr hadjk
      rcases hBR (k + 1) hk with hCk1 | hCk1
      · by_cases hS : c (k + 1) ∈ S
        · rcases key (c (k + 1)) hOrderMem hS with h | h
          · have h' : C (c (k + 1)) = black := hVC' ▸ h
            exact color_clash h' hCk1 (by decide)
          · have h' : C (c (k + 1)) = blue := hVC' ▸ h
            exact hNBB (c k) (c (k + 1)) hadjk hCk h'
        · exact hNBB (c k) (c (k + 1)) hadjk hCk hCk1
          -- have hcontra : C (c (k + 1)) = blue := heq.symm.trans hCk
          -- rw [hcontra] at hCk1
          -- -- have hne : blue ≠ red := by decide
          -- -- exact hne hCk1
          -- exact absurd hCk1 (by decide)
      · have hcontra : C (c (k + 1)) = blue := heq.symm.trans hCk
        exact color_clash hcontra hCk1 (by decide)
    · intro heq
      by_cases hS : c (k + 1) ∈ S
      · have hqNotBlack : C (c (k + 1)) ≠ black := by
          intro hb
          rcases hBR (k + 1) hk with h | h
          · exact color_clash hb h (by decide)
          · exact color_clash hb h (by decide)
        have hblue : C (c (k + 1)) = blue :=
          hV3_derived G S hOrder hlen hfuel hVC hadjk hCk hS hqNotBlack
        have hred : C (c (k + 1)) = red := heq.symm.trans hCk
        exact color_clash hblue hred (by decide)
      · have hckNotS : c k ∉ S := hRedNotS hCk
        rcases hSVC hadjk with h | h
        · exact hckNotS h
        · exact hS h
  have hwrap : C (c (n - 1)) ≠ C (c 0) := by
    have hn1 : n - 1 + 1 = n := by omega
    have hmod : (n - 1 + 1) % n = 0 := by rw [hn1]; exact Nat.mod_self n
    have hadj' : G.Adj (c (n - 1)) (c ((n - 1 + 1) % n)) := hadj (n - 1)
    have hadjwrap : G.Adj (c (n - 1)) (c 0) := hmod ▸ hadj'
    rcases hBR (n - 1) (by omega) with hC1 | hC1 <;> rcases hBR 0 hn_pos with hC0 | hC0
    · intro heq
      have hC1' : runAlgC G S nbrOrder fuel v0 (c (n - 1)) = blue := hVC' ▸ hC1
      have key := runAlgC_blue_neighbors_resolved_general G S nbrOrder hirrefl hlen hv0 hfuel hC1'
      have hOrderMem : c 0 ∈ nbrOrder (c (n - 1)) := (hOrder (c (n - 1)) (c 0)).mpr hadjwrap
      by_cases hS : c 0 ∈ S
      · rcases key (c 0) hOrderMem hS with h | h
        · have h' : C (c 0) = black := hVC' ▸ h
          exact color_clash h' (heq.symm.trans hC1) (by decide)
        · have h' : C (c 0) = blue := hVC' ▸ h
          exact hNBB (c (n - 1)) (c 0) hadjwrap hC1 h'
      -- · have hc0blue : C (c 0) = blue := heq.symm.trans hC1
      --   rw [hc0blue] at hC0
      --   exact absurd hC0 (by decide)
      · exact hNBB (c (n - 1)) (c 0) hadjwrap hC1 hC0
    · rw [hC1, hC0]; decide
    · rw [hC1, hC0]; decide
    · intro heq
      by_cases hS : c 0 ∈ S
      · have hqNotBlack : C (c 0) ≠ black := by
          intro hb; exact color_clash hb hC0 (by decide)
        have hblue : C (c 0) = blue :=
          hV3_derived G S hOrder hlen hfuel hVC hadjwrap hC1 hS hqNotBlack
        exact color_clash hblue (heq.symm.trans hC1) (by decide)
      · have hlastNotS : c (n - 1) ∉ S := hRedNotS hC1
        rcases hSVC hadjwrap with h | h
        · exact hlastNotS h
        · exact hS h
  exact Lemma12_Part2b_oddcycle_no_proper_2coloring hn_odd hn_pos hBR hwrap hne

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Proof map:
    color_clash                        — trivial Color-equality helper
    red_absorb / blue_absorb / black_absorb
                                        — local shorthands
                                          absorbing-color exports
    AlgC_red_resolves_own_list         — a red vertex resolves every
                                          `S`-neighbor it visits
                                          directly; needs no auxiliary
                                          invariant (unlike blue's
                                          `BlueNbrsResolved`), since the
                                          red-branch's rule is
                                          unconditional on the target
                                          being currently white/yellow.
    AlgC_correct_red                   — the general "some vertex
                                          transitions to red anywhere in
                                          this call" analogue; ten-branch
                                          strong induction on fuel,
                                          mirroring `lemma12_1`'s own
                                          `AlgC_preserves_red_notS`
                                          structure, combined with "does
                                          p transition here, in the
                                          dive, or in the continuation."
    AlgC_correct_blue                  — the structural mirror for blue,
                                          threading THREE invariants
                                          (red∉S, ∉S⟹white∨red,
                                          BlueNbrsResolved).
    NoBlueBlue / AlgC_preserves_NoBlueBlue / initColoring_NoBlueBlue /
    runAlgC_NoBlueBlue / ValidColoring_NoBlueBlue
                                        — THE KEY PIECE: no two adjacent
                                          vertices are ever
                                          simultaneously blue. Proved by
                                          strong induction, using ONLY
                                          `BlueNbrsResolved` (already
                                          forward-preserved by `lemma12_1`)
                                          plus `OrderMatchesAdj`'s
                                          symmetric adjacency — NOT a
                                          temporal/ordering argument.
                                          If a vertex `u'` transitions
                                          white→blue and some neighbor
                                          `y` were already blue,
                                          `BlueNbrsResolved` applied to
                                          `y` (blue) and its S-neighbor
                                          `u'` forces `C u' ≠ white`,
                                          directly contradicting the
                                          transition's own hypothesis
                                          `C u' = white`. FIXED (v8.3):
                                          the "fresh transition" cases
                                          now consume `x = u'` /
                                          `y = u'` facts via `rw`
                                          directly, never `subst`
                                          (which was silently
                                          eliminating `u'`). Base case
                                          (`initColoring`) is trivial:
                                          exactly one blue vertex.
    runAlgC_red_neighbors_resolved /
    runAlgC_blue_neighbors_resolved_general
                                        — top-level packagings for the
                                          actual `runAlgC` call.
    hV3_derived                        — a red vertex's S-neighbor, if
                                          not black, is blue.
    Lemma12_Part2b_conflict            — UNCONDITIONAL `C w = black`
                                          form, matching the original
                                          four-color v7 statement, via
                                          `ValidColoring_NoBlueBlue`
    Theorem 2 (parity)                 — pure combinatorics, unchanged.
    Lemma12_Part2b_some_black          — both `blue`-alternative
                                          sub-cases (non-wraparound and
                                          wraparound) closed directly
                                          via `hNBB`
                                          (`ValidColoring_NoBlueBlue`,
                                          FIXED, v8.3: `nbrOrder` now
                                          passed explicitly).
-/
