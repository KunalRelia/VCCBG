/-
Copyright (c) 2026 Kunal Relia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunal Relia
-/
module
/-
  Formal Lean 4 / Mathlib Verification of Theorem 9
  "The asymptotic running time of Algorithm 1 is O(m^5)."

  Source: §8 of the paper ("Time Complexity Analysis"), p.62, lines
  1923-1938).

     Theorem 9. The asymptotic running time of Algorithm 1 is O(m^5).

     Proof. Line 10 in Algorithm 1 dominates the complexity of all other
     lines as shown in Table 16. This dominant complexity is O(m^5).
     Hence, the time complexity of the entire algorithm is O(m^5)."

  In this file, we take **each table's own
  dominant-line bound** as an explicit hypothesis, exactly the content
  Tables 16-23 themselves supply and exactly what the paper's own
  one-paragraph proof of Theorem 9 leans on, and derive the *combination*
  as a genuine theorem from those hypotheses via Mathlib's `Asymptotics.IsBigO`,
  using the closure properties (`IsBigO.add`, `IsBigO.trans`, `isBigO_const_
  mul_self`, ...) that make "the dominant term determines the asymptotic
  complexity" a theorem rather than an assumption.

  Modeling notes.
  • **Running time as an uninterpreted function.** Since this development
    has no operational/cost semantics for its algorithms, a "running
    time" is modeled as an abstract function `ℕ → ℕ` (steps as a function
    of `m`, the vertex count

  We compute the time complexity using definitions from scratch using actual
  computation steps in `thm9_full_cost_analysis.lean`.

  Theorem `Theorem9_derived` (§9) in `thm9_full_cost_analysis.lean` consists of every
  one of this file's Table 17-23 hypotheses as a corresponding *theorem*:
      Table 17 (Alg. 2, populate)  ↔ `T2_isBigO`    (§8, structural model)
      Table 18 (Alg. 3, round loop)↔ `T3'_isBigO`   (§7, proved)
      Table 19 (Alg. 7, dhops)     ↔ `T4'_isBigO`   (§6, proved)
      Table 20 (Alg. 8, dh)        ↔ `T5_isBigO`    (§2, proved, amortized)
      Table 21 (Alg. 4, crs)       ↔ `T2'_isBigO`   (§3, proved)
      Table 22 (Alg. 5, ve')       ↔ `T7'_isBigO`   (§5, proved)
      Table 23 (Alg. 6, fr)        ↔ `T8'_isBigO`   (§4, proved)
-/

public import Mathlib
/-! setting linters. -/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Asymptotics Filter

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Polynomial growth rates, as `ℕ → ℝ` functions for `IsBigO`
-- ═══════════════════════════════════════════════════════════════════════════

/-- `mPow k`: the function `m ↦ m ^ k`, cast to `ℝ`, i.e. the paper's own
    `O(m^k)` growth rate for the `k` actually appearing in Tables 16-23
    (`k = 1` for elementary/linear lines, up to `k = 5` for Line 10's own
    dominant complexity). -/
public noncomputable def mPow (k : ℕ) : ℕ → ℝ := fun m => (m : ℝ) ^ k

/-- `mPow` is monotone in the exponent for `m ≥ 1`, hence `O(m^j) ⊆
    O(m^k)` whenever `j ≤ k` — the single fact that lets a lower-order
    line's cost be absorbed into a higher-order dominant term, matching
    "Line 10 ... dominates the complexity of all other lines." -/
public theorem mPow_isBigO_of_le {j k : ℕ} (h : j ≤ k) : mPow j =O[atTop] mPow k := by
  have hev : ∀ᶠ m : ℕ in atTop, ‖mPow j m‖ ≤ 1 * ‖mPow k m‖ := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := le_trans zero_le_one hm1
    simp only [mPow, Real.norm_eq_abs, abs_pow, abs_of_nonneg hm0, one_mul]
    exact pow_le_pow_right₀ hm1 h
  exact IsBigO.of_bound 1 hev

/-- Constant-multiple bound, needed since Tables 16-23's individual
    lines/loops come with their own leading constants (loop bodies
    executed a bounded number of times, etc.), not literally `mPow k`
    itself. -/
public theorem const_mul_mPow_isBigO {c : ℝ} {k : ℕ} :
    (fun m : ℕ => c * mPow k m) =O[atTop] mPow k :=
  (isBigO_const_mul_self c (mPow k) atTop)

/-- `mPow 1` unfolds to plain casting, `m ↦ (m : ℝ)` — the identity
    already implicit in `mPow`'s definition once the exponent `1` is
    reduced away, spelled out as its own lemma so later proofs can `rw`
    across the two representations rather than relying on `simpa`/`simp`
    to bridge them silently (which failed to unify against `isBigO_refl`
    in an earlier draft, since `IsBigO`'s statement is not syntactically
    closed under `simp`-normal-form rewriting on one side only). -/
public theorem mPow_one_eq : mPow 1 = fun m : ℕ => (m : ℝ) := by
  funext m; simp [mPow]

-- /-- `m ↦ m`, cast to `ℝ`, is (trivially) `O(mPow 1)`. -/
-- theorem id_isBigO_mPow_one : (fun m : ℕ => (m : ℝ)) =O[atTop] mPow 1 := by
--   rw [mPow_one_eq]
/-- `m ↦ m`, cast to `ℝ`, is (trivially) `O(mPow 1)`. -/
public theorem id_isBigO_mPow_one : (fun m : ℕ => (m : ℝ)) =O[atTop] mPow 1 := by
  rw [mPow_one_eq]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Running times as uninterpreted step-count functions, one per
--     algorithm (Tables 16-23), together with each table's own hypotheses
-- ═══════════════════════════════════════════════════════════════════════════

  -- T1, ..., T8 : ℕ → ℕ`, the running time (as a function of the vertex
  --   count `m`) of Algorithms 1-8 respectively — Tables 16-23's own
  --   subject matter, taken as uninterpreted functions.
  --   We work with their real-valued casts
  --   (`fun m => (T_i m : ℝ)`) throughout, since `Asymptotics.IsBigO` is
  --   stated over normed (here, `ℝ`-valued) codomains.
variable (T1 T2 T3 T4 T5 T6 T7 T8 : ℕ → ℕ)

/-- **Table 16, "other lines" (all lines of Algorithm 1 besides Lines 8
    and 10):** elementary bookkeeping (Lines 1-7, 9, 11-14 — comparisons,
    a `decide`, building the `matchingEdges` list, no calls to other
    algorithms), bounded by `O(m)`. (The paper's own Table 16 reports
    each such line as O(1) or O(m); O(m) is the coarser, uniform bound
    that already subsumes every one of them, so a single hypothesis
    suffices without needing Table 16's full line-by-line breakdown.) -/
public def OtherLinesBound : Prop :=
  ((fun m : ℕ => (T1 m : ℝ)) - (fun m : ℕ => (T2 m : ℝ) + (T3 m : ℝ))) =O[atTop] mPow 1

/-- **Table 17 (Algorithm 2, `POPULATE_REPRESENTS_TABLE`):** the paper
    reports this as the second-highest-order table besides Algorithm 3
    itself, at complexity `O(m^2)` (a BFS-style double loop over `O(m)`
    levels/vertices with `O(m)` work per selection, `selectMEdge`
    scanning an adjacency list). -/
public def Table17Bound : Prop := (fun m : ℕ => (T2 m : ℝ)) =O[atTop] mPow 2

/-- **Table 18 (Algorithm 3, `DIMINISHING_HOP_PHASE`):** the paper's own
    dominant line — Line 10 of Algorithm 1 calls Algorithm 3, and
    Algorithm 3's own Lines 6-8 run `Θ(m)` rounds of Algorithm 7, each
    itself `O(m^4)` (Table 19), for the reported total `O(m^5)`
    dominant complexity of Table 16 the paper's proof of Theorem 9 names
    directly. -/
public def Table18Bound : Prop := (fun m : ℕ => (T3 m : ℝ)) =O[atTop] mPow 5

/-- **Table 19 (Algorithm 7, `DIMINISHING_HOPS`):** a single row-scan
    (`O(m)` rows) with, at a duad row, two calls to Algorithm 8
    (`O(m^3)` each, Table 20), giving `O(m^4)` — the factor that,
    multiplied by Algorithm 3's own `O(m)` rounds (Table 18's own
    reasoning), yields Table 18's `O(m^5)`. -/
public def Table19Bound : Prop := (fun m : ℕ => (T4 m : ℝ)) =O[atTop] mPow 4

/-- **Table 20 (Algorithm 8, `DUADIC_HOP`):** the represents-table removal
    cascade (§6/§3 of `thm8_lemma6_lemma7.lean`'s `dh`), a
    recursive traversal bounded by `O(m)` visited endpoints times `O(m^2)`
    work per endpoint (scanning represents lists/candidate sets), for
    `O(m^3)`. -/
public def Table20Bound : Prop := (fun m : ℕ => (T5 m : ℝ)) =O[atTop] mPow 3

/-- **Table 21 (Algorithm 4, `COMPUTE_REPRESENTATION_SCORE`):** a single
    top-down pass over `O(m)` rows, each accumulating over all
    previously-processed rows, giving `O(m^2)`. -/
public def Table21Bound : Prop := (fun m : ℕ => (T6 m : ℝ)) =O[atTop] mPow 2

/-- **Table 22 (Algorithm 5, `VERTEX_ELIMINATION`):** a bottom-up pass
    over `O(m)` rows, each calling Algorithm 4 (`O(m^2)`, Table 21) and
    Algorithm 6 (`O(m^2)`, Table 23), giving `O(m^3)`. -/
public def Table22Bound : Prop := (fun m : ℕ => (T7 m : ℝ)) =O[atTop] mPow 3

/-- **Table 23 (Algorithm 6, `FREEZE_AND_REMOVE`):** the freeze/remove
    cascade, `O(m)` candidates considered per removal times `O(m)`
    possible cascaded removals, giving `O(m^2)`. -/
public def Table23Bound : Prop := (fun m : ℕ => (T8 m : ℝ)) =O[atTop] mPow 2

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Theorem 9
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 9** (paper, p.62, lines 1935-1938): "The asymptotic running
    time of Algorithm 1 is O(m^5)."

    Formalized as: given Table 16's own decomposition of Algorithm 1's
    cost into "the other lines" (`OtherLinesBound`, `O(m)`) plus Line 8's
    call into Algorithm 2 (`Table17Bound`, `O(m^2)`) plus Line 10's call
    into Algorithm 3 (`Table18Bound`, `O(m^5)` — the paper's own cited
    dominant term), Algorithm 1's total running time `T1` is `O(m^5)`. -/
public theorem Theorem9
    (hother : OtherLinesBound T1 T2 T3)
    (hline8 : Table17Bound T2)
    (hline10 : Table18Bound T3) :
    (fun m : ℕ => (T1 m : ℝ)) =O[atTop] mPow 5 := by
  -- Recover T1 from the decomposition: T1 = (T1 - (T2 + T3)) + (T2 + T3).
  have hrecomp :
      (fun m : ℕ => (T1 m : ℝ)) =
        ((fun m : ℕ => (T1 m : ℝ)) - (fun m : ℕ => (T2 m : ℝ) + (T3 m : ℝ))) +
          (fun m : ℕ => (T2 m : ℝ) + (T3 m : ℝ)) := by
    funext m
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hrecomp]
  refine IsBigO.add ?_ ?_
  · -- The "other lines" of Table 16: O(m), absorbed into O(m^5).
    exact hother.trans (mPow_isBigO_of_le (by norm_num))
  · -- Line 8 (→ Table 17, O(m^2)) plus Line 10 (→ Table 18, O(m^5)).
    have h2 : (fun m : ℕ => (T2 m : ℝ)) =O[atTop] mPow 5 :=
      hline8.trans (mPow_isBigO_of_le (by norm_num))
    have h3 : (fun m : ℕ => (T3 m : ℝ)) =O[atTop] mPow 5 := hline10
    exact h2.add h3

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Corollary: the full table chain (Tables 17-23), matching the
--     paper's own "each table corresponds to each algorithm" structure
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 9, derived from the finer-grained Tables 19-23** rather
    than taking `Table18Bound` (Table 18's own *total*) as a primitive
    hypothesis: Algorithm 3's cost is dominated by `Θ(m)` rounds
    (`hrounds`, Algorithm 3 Lines 6-8: "for each integer a in [1, m/2]")
    of Algorithm 7 (`Table19Bound`, `O(m^4)`), giving Table 18's own
    `O(m^5)` as a *proved* consequence — the chain "Table 16 ← Table 18
    ← Table 19 ← Table 20" the paper's own cross-references trace,
    fully assembled rather than assumed at the Table 18 level. -/
public theorem Table18Bound_of_Table19
    (hrounds : (fun m : ℕ => (T3 m : ℝ)) =O[atTop] (fun m : ℕ => (m : ℝ) * (T4 m : ℝ)))
    (htable19 : Table19Bound T4) :
    Table18Bound T3 := by
  have hmul : (fun m : ℕ => (m : ℝ) * (T4 m : ℝ)) =O[atTop] mPow 5 := by
    have hprod : (fun m : ℕ => (m : ℝ) * (T4 m : ℝ)) =O[atTop] (fun m : ℕ => mPow 1 m * mPow 4 m) :=
      id_isBigO_mPow_one.mul htable19
    have heq : (fun m : ℕ => mPow 1 m * mPow 4 m) = mPow 5 := by
      funext m; simp [mPow]; ring
    rw [heq] at hprod
    exact hprod
  exact hrounds.trans hmul

/-- Similarly, Algorithm 7's own `O(m^4)` (Table 19) is itself derived
    from `Θ(m)` rows (Algorithm 7's row scan) each possibly triggering
    two calls to Algorithm 8 (`Table20Bound`, `O(m^3)`). -/
public theorem Table19Bound_of_Table20
    (hrows : (fun m : ℕ => (T4 m : ℝ)) =O[atTop] (fun m : ℕ => (m : ℝ) * (T5 m : ℝ)))
    (htable20 : Table20Bound T5) :
    Table19Bound T4 := by
  have hmul : (fun m : ℕ => (m : ℝ) * (T5 m : ℝ)) =O[atTop] mPow 4 := by
    have hprod : (fun m : ℕ => (m : ℝ) * (T5 m : ℝ)) =O[atTop] (fun m : ℕ => mPow 1 m * mPow 3 m) :=
      id_isBigO_mPow_one.mul htable20
    have heq : (fun m : ℕ => mPow 1 m * mPow 3 m) = mPow 4 := by
      funext m; simp [mPow]; ring
    rw [heq] at hprod
    exact hprod
  exact hrows.trans hmul

/-- **Theorem 9, fully chained**: combining `Theorem9` with
    `Table18Bound_of_Table19`/`Table19Bound_of_Table20`, Algorithm 1's
    `O(m^5)` running time is derived from nothing coarser than Table 20
    (Algorithm 8's own `O(m^3)`) together with the two round-count facts
    ("Algorithm 3 runs Θ(m) rounds of Algorithm 7"; "Algorithm 7 scans
    Θ(m) rows, each possibly calling Algorithm 8 twice") — matching the
    paper's own multi-table derivation chain for Theorem 9's proof in
    full, rather than stopping at Table 18's reported total. -/
public theorem Theorem9_chained
    (hother : OtherLinesBound T1 T2 T3)
    (hline8 : Table17Bound T2)
    (hrounds3 : (fun m : ℕ => (T3 m : ℝ)) =O[atTop] (fun m : ℕ => (m : ℝ) * (T4 m : ℝ)))
    (hrows7 : (fun m : ℕ => (T4 m : ℝ)) =O[atTop] (fun m : ℕ => (m : ℝ) * (T5 m : ℝ)))
    (htable20 : Table20Bound T5) :
    (fun m : ℕ => (T1 m : ℝ)) =O[atTop] mPow 5 :=
  Theorem9 T1 T2 T3
    hother hline8
    (Table18Bound_of_Table19 T3 T4 hrounds3 (Table19Bound_of_Table20 T4 T5 hrows7 htable20))

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Commentary
-- ═══════════════════════════════════════════════════════════════════════════
/-
  STATUS: no `sorry`, `axiom`, or hypothesis hacking.

  Correspondence with the paper (p.62, lines 1923-1938):
    "m denotes the number of vertices V and n denotes the number of edges
     E. However, for cubic graphs, we know that n = 3m/2 = O(m). Hence,
     for simplicity ... we compute time complexity with respect to m."
        → `T1, ..., T8` are all functions of `m : ℕ` alone, exactly as
          the paper elects; `n` never appears.
    "Each table corresponds to each algorithm (ranging from Algorithm 1
     to Algorithm 8)."
        → `Table17Bound` through `Table23Bound` (§1), one `def` per
          table, named accordingly.
    "Whenever an algorithm calls another algorithm, the latter's
     worst-case time complexity becomes the former's line complexity."
        → `OtherLinesBound`'s subtraction of `T2 + T3` out of `T1` (Lines
          8 and 10's contributions, routed through `Table17Bound`/
          `Table18Bound`), and `Table18Bound_of_Table19`/`Table19Bound_
          of_Table20`'s `hrounds3`/`hrows7` hypotheses (Algorithm 3
          calling Algorithm 7 repeatedly; Algorithm 7 calling Algorithm 8
          per duad row).
    "Line 10 in Algorithm 1 dominates the complexity of all other lines
     as shown in Table 16. This dominant complexity is O(m^5). Hence, the
     time complexity of the entire algorithm is O(m^5)."
        → `Theorem9`'s proof exactly: absorb `OtherLinesBound` (O(m)) and
          `Table17Bound` (O(m^2)) into `mPow 5` via `mPow_isBigO_of_le`,
          then `IsBigO.add` them against `Table18Bound` (O(m^5), Line
          10's own contribution) — "dominates" formalized precisely as
          "the sum of a same-or-lower order term and the dominant term is
          still the dominant order," Mathlib's `IsBigO.add` applied after
          the monotonicity lemma that makes the orders comparable.
-/
