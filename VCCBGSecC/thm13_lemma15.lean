/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Lean 4 / Mathlib — Lemma 15   [using the FIVE-COLOR
  Algorithm-C model (white/blue/red/black/yellow), matching
  `thm13_lemma14.lean` and its predecessor chain:
  `thm13_lemma12_1` / `thm13_lemma12_2a` /
  `thm13_lemma12_2b` / `thm13_lemma12_overall` /
  `thm13_lemma13`.]

  "Given an alternating bipartite graph w.r.t. S, then the
   S-alternating bipartite graph is an S-diminishing bipartite graph if
   the S-alternating bipartite graph consists of a higher number of
   blue vertices than the number of red vertices."

  Source: paper §C.2.2, lines 2636–2656.
-/

public import VCCBGSecC.thm13_lemma14

/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Color

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. NEW MACHINERY: the missing "blue vertex's non-S neighbor is red"
--     half, built by mirroring `thm13_lemma12_2b.lean`'s own
--     `AlgC_correct_blue` branch-for-branch.
-- ═══════════════════════════════════════════════════════════════════════════

variable (G : SimpleGraph V) (S : Finset V) (nbrOrder : V → List V)

/-- **The non-`S` half of blue-neighbor resolution**: for ANY vertex `p`
    (not just the top-level seed) that transitions to `blue` SOMEWHERE
    during this call, every non-`S` `nbrOrder`-neighbor of `p` ends up
    `red` by the time this call returns.

    Proved by mirroring `thm13_lemma12_2b.lean`'s own
    `AlgC_correct_blue` case-by-case, using the `.2` conjunct of
    `AlgC_blue_resolves_own_list` — "u ∉ S → red" —
    at the two "p transitions to blue right here" sites (the
    red-branch's and black-branch's `u ∈ S ∧ white → blue` rules),
    instead of the `.1` conjunct `_2b` uses for its own S-side
    theorem. -/
public theorem AlgC_correct_blue_notS
    (hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V) :
    ∀ n C v us, (∀ y ∈ us, y ≠ v) →
      (∀ x, C x = red → x ∉ S) →
      (∀ x ∉ S, C x = white ∨ C x = red) →
      BlueNbrsResolved G S nbrOrder C →
      fuelBound C us ≤ n →
      ∀ p, C p ≠ blue → AlgC G S nbrOrder n C v us p = blue →
        ∀ w ∈ nbrOrder p, w ∉ S →
          AlgC G S nbrOrder n C v us w = red := by
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
              exact AlgC_red_preserved G S nbrOrder m C2 v rest w hwS (hstep w hw hwS)
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
                exact AlgC_red_preserved G S nbrOrder m C2 v rest w hwS (hstep w hw hwS)
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
                exact AlgC_red_preserved G S nbrOrder m C2 v rest w hwS
                  (hResolve.2 hwS)
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
                  exact AlgC_red_preserved G S nbrOrder m C2 v rest w hwS (hstep w hw hwS)
                · exact ih m (by omega) C2 v rest hrestwf hC2red hnotS2 hBinv2 hfuel'
                    p hCp2 hresp
            · by_cases hu4 : u' ∈ S ∧ C u' = yellow
              · rw [AlgC_red_black_recurse G S nbrOrder hvb hvr hu3 hu4] at hresp ⊢
                set C1 := Function.update C u' black with hC1def
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
                  exact AlgC_red_preserved G S nbrOrder m C2 v rest w hwS (hstep w hw hwS)
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
                  exact AlgC_red_preserved G S nbrOrder m C2 v rest w hwS (hstep w hw hwS)
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
                    exact AlgC_red_preserved G S nbrOrder m C2 v rest w hwS
                      (hResolve.2 hwS)
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
                      exact AlgC_red_preserved G S nbrOrder m C2 v rest w hwS (hstep w hw hwS)
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

/-- **Top-level packaging** of `AlgC_correct_blue_notS` for the actual
    `runAlgC` call seeded at `v0 ∈ S`, mirroring
    `runAlgC_blue_neighbors_resolved_general`'s own two-case split. -/
public theorem runAlgC_blue_notS_neighbor_red
    (hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {v0 : V} (hv0 : v0 ∈ S) {fuel : ℕ}
    (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {p : V} (hp : runAlgC G S nbrOrder fuel v0 p = blue) :
    ∀ w ∈ nbrOrder p, w ∉ S → runAlgC G S nbrOrder fuel v0 w = red := by
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
    exact (runAlgC_seed_neighbors_resolved G S nbrOrder hirrefl hlen hv0 hfuel w hw).2 hwS
  · have hCp0 : initColoring G S nbrOrder v0 p ≠ blue := by
      unfold initColoring
      intro hcontra
      have hc' : (Function.update (fun _ : V => white) v0 blue) p = blue :=
        yellowRest_eq_c_imp S (nbrOrder v0) (Function.update (fun _ : V => white) v0 blue) p
          (by decide) (by decide) hcontra
      rw [Function.update_apply, ite_eq_right hpv0] at hc'
      exact absurd hc' (by decide)
    exact AlgC_correct_blue_notS G S nbrOrder hirrefl hlen fuel (initColoring G S nbrOrder v0) v0
      (nbrOrder v0) hus hCSred0 hnotS0 hBinv0 hfuel p hCp0 hp

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. The field: U_ne (the seed witnesses U's nonemptiness)
-- ═══════════════════════════════════════════════════════════════════════════
-- The following variables are made implicit to be coherent with previous version
-- of the code. Without this, there will be type (Line 669) or application type mistmatch
-- (Lines 671, 686), and these will require that variable(s) be explicitly passed.
variable {G : SimpleGraph V} {S : Finset V} {nbrOrder : V → List V}

/-- **Lemma 15, field (1)**: `reachU G S C v0` is nonempty.

    Paper: "the seed vertex selected by the loop... is colored blue
    because it is in the given vertex cover S... It satisfies the first
    condition stated in Definition 25: G' contains at least one vertex
    from S."

    Needs NO hypothesis about any particular vertex's color: it follows
    purely from `hgt : |W| < |U|` by cardinality arithmetic. -/
public theorem Lemma15_U_ne
    {S : Finset V} {v0 : V} {C : Coloring V}
    (hgt : (reachW G S C v0).card < (reachU G S C v0).card) :
    (reachU G S C v0).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  rw [hemp, Finset.card_empty] at hgt
  omega

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The field: flip_vc (the swap is a smaller vertex cover)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 15, field (3)**: `(S \ reachU G S C v0) ∪ reachW G S C v0`
    is a vertex cover.

    Paper: "when the blue vertices are removed, and red vertices added
    to S (Line 19 of Algorithm B), the resultant set is a vertex cover
    of a smaller size."

    Proof: for any edge `(a, b)`, `VCover G S` puts at least one
    endpoint in `S`. If that endpoint is not blue (`∉ reachU`), it lies
    in `S \ reachU` directly. If it IS blue: for the other endpoint `b`,
    case on `b ∈ S`:
      • `b ∈ S` — `runAlgC_blue_neighbors_resolved_general` gives
        `black ∨ blue`; `NoBlueBlue` (via `ValidColoring_NoBlueBlue`)
        excludes `blue` (both endpoints being blue would violate it
        directly), leaving `black`, hence `b ∉ reachU`, hence
        `b ∈ S \ reachU`.
      • `b ∉ S` — `runAlgC_blue_notS_neighbor_red` (§0, new) gives
        `b` is `red` directly, hence `b ∈ reachW`. -/
public theorem Lemma15_flip_vc
    {S : Finset V} {v0 : V} (hv0 : v0 ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S) :
    VCover G ((S \ reachU G S C v0) ∪ reachW G S C v0) := by
  have hirrefl : ∀ x y, y ∈ nbrOrder x → y ≠ x := hOrder.irrefl
  have hNBB : NoBlueBlue G C := ValidColoring_NoBlueBlue G S nbrOrder hOrder hVC
  intro a b hadj
  rcases hSVC hadj with haS | hbS
  · -- a ∈ S
    by_cases haU : a ∈ reachU G S C v0
    · -- a is blue: resolve b
      simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at haU
      have hCa' : runAlgC G S nbrOrder fuel v0 a = blue := by
        unfold ValidColoring at hVC; exact hVC ▸ haU
      have hbOrder : b ∈ nbrOrder a := (hOrder a b).mpr hadj
      by_cases hbS' : b ∈ S
      · -- b ∈ S: black ∨ blue, then exclude blue via NoBlueBlue
        have key := runAlgC_blue_neighbors_resolved_general G S nbrOrder hirrefl hlen hv0 hfuel
          hCa' b hbOrder hbS'
        rcases key with hblack | hblue
        · have hCb_black' : C b = black := by unfold ValidColoring at hVC; exact hVC ▸ hblack
          have hbU : b ∉ reachU G S C v0 := by
            simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and]
            intro hCb_blue
            rw [hCb_black'] at hCb_blue
            exact absurd hCb_blue (by decide)
          exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hbS', hbU⟩))
        · exfalso
          have hCb_blue' : C b = blue := by unfold ValidColoring at hVC; exact hVC ▸ hblue
          exact hNBB a b hadj haU hCb_blue'
      · -- b ∉ S: forced red
        have hred := runAlgC_blue_notS_neighbor_red G S nbrOrder hirrefl hlen hv0 hfuel
          hCa' b hbOrder hbS'
        have hCb_red' : C b = red := by unfold ValidColoring at hVC; exact hVC ▸ hred
        have hbW : b ∈ reachW G S C v0 := by
          simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hCb_red'
        exact Or.inr (Finset.mem_union_right _ hbW)
    · -- a ∉ U: a ∈ S \ U directly
      exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haS, haU⟩))
  · -- b ∈ S (symmetric)
    by_cases hbU : b ∈ reachU G S C v0
    · simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and] at hbU
      have hCb' : runAlgC G S nbrOrder fuel v0 b = blue := by
        unfold ValidColoring at hVC; exact hVC ▸ hbU
      have hadj' : G.Adj b a := hadj.symm
      have haOrder : a ∈ nbrOrder b := (hOrder b a).mpr hadj'
      by_cases haS' : a ∈ S
      · have key := runAlgC_blue_neighbors_resolved_general G S nbrOrder hirrefl hlen hv0 hfuel
          hCb' a haOrder haS'
        rcases key with hblack | hblue
        · have hCa_black' : C a = black := by unfold ValidColoring at hVC; exact hVC ▸ hblack
          have haU : a ∉ reachU G S C v0 := by
            simp only [reachU, Finset.mem_filter, Finset.mem_univ, true_and]
            intro hCa_blue
            rw [hCa_black'] at hCa_blue
            exact absurd hCa_blue (by decide)
          exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨haS', haU⟩))
        · exfalso
          have hCa_blue' : C a = blue := by unfold ValidColoring at hVC; exact hVC ▸ hblue
          exact hNBB b a hadj' hbU hCa_blue'
      · have hred := runAlgC_blue_notS_neighbor_red G S nbrOrder hirrefl hlen hv0 hfuel
          hCb' a haOrder haS'
        have hCa_red' : C a = red := by unfold ValidColoring at hVC; exact hVC ▸ hred
        have haW : a ∈ reachW G S C v0 := by
          simp only [reachW, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hCa_red'
        exact Or.inl (Finset.mem_union_right _ haW)
    · -- b ∉ U: b ∈ S \ U directly
      exact Or.inr (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hbS, hbU⟩))

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Lemma 15 — assembling the complete DimBip.
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 15**: an `AltBip` (from `Lemma14_witness`, seeded at
    `v0 ∈ S`) with more blue than red vertices upgrades to a full
    `DimBip` (Definition 25). -/
public noncomputable def Lemma15_witness
    {S : Finset V} {v0 : V} (hv0 : v0 ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S)
    (hgt : (reachW G S C v0).card < (reachU G S C v0).card) :
    DimBip G S where
  toAltBip := Lemma14_witness G S nbrOrder hv0 hOrder hVC hSVC
  U_ne    := Lemma15_U_ne hgt
  U_gt_W  := hgt
  flip_vc := Lemma15_flip_vc hv0 hOrder hlen hfuel hVC hSVC

/-- **Lemma 15** (theorem form), matching `Lemma14`'s style: wraps the
    witness in an existential, restoring `theorem` status. -/
public theorem Lemma15
    {S : Finset V} {v0 : V} (hv0 : v0 ∈ S)
    {nbrOrder : V → List V} (hOrder : OrderMatchesAdj G nbrOrder)
    (hlen : ∀ x, (nbrOrder x).length ≤ Fintype.card V)
    {fuel : ℕ} (hfuel : fuelBound (initColoring G S nbrOrder v0) (nbrOrder v0) ≤ fuel)
    {C : Coloring V} (hVC : ValidColoring G S nbrOrder v0 fuel C)
    (hSVC : VCover G S)
    (hgt : (reachW G S C v0).card < (reachU G S C v0).card) :
    ∃ D : DimBip G S,
      D.toAltBip.toBipSub.U = reachU G S C v0 ∧
      D.toAltBip.toBipSub.W = reachW G S C v0 :=
  ⟨Lemma15_witness hv0 hOrder hlen hfuel hVC hSVC hgt, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Proof map:
    AlgC_correct_blue_notS            — NEW: mirrors `_2b`'s own
                                         `AlgC_correct_blue`, tracking
                                         "∉S ⟹ red" instead of
                                         "∈S ⟹ black∨blue", using the
                                         `.2` conjunct of `lemma12_1`'s
                                         `AlgC_blue_resolves_own_list`.
    runAlgC_blue_notS_neighbor_red    — NEW: top-level packaging,
                                         mirroring
                                         `runAlgC_blue_neighbors_resolved_general`'s
                                         own `p = v0` / `p ≠ v0` split.
    Lemma15_U_ne                      —  pure
                                         `Finset.card` arithmetic.
    Lemma15_flip_vc                   — UPDATED: S-side via
                                         `runAlgC_blue_neighbors_resolved_general`
                                         + `NoBlueBlue` (excluding the
                                         `blue` disjunct that theorem now
                                         leaves open); non-S-side via the
                                         two new theorems above.
    Lemma15_witness / Lemma15         —  calling `Lemma14_witness`'s
                                         current signature
                                         (`G S nbrOrder hv0 hOrder hVC
                                         hSVC`, no `hlen`/`hfuel`).
-/
