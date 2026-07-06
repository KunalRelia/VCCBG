/-
  Lean 4 / Mathlib — Lemma 12, Part 2(b)
  "When a black vertex is in an odd cycle"

  Source: paper §C.2.2, lines 2546–2591.

  ═══════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE PROVES
  ═══════════════════════════════════════════════════════════════════════════

  Part 2(a) (separate file) handled the structural case: a black vertex
  arising purely from cubic-degree counting, with no genuine conflict.

  Part 2(b) is qualitatively different: an ODD CYCLE forces a genuine
  conflict under the alternating rules V1/V3. We isolate and prove the
  two precise mathematical claims behind the paper's bullet points:

  THEOREM 1 (Conflict Resolution / "black breaks the alternation"):
    No vertex w ∈ S can simultaneously have a BLUE neighbor and a RED
    neighbor under a valid coloring. V1 would force w = black while V3
    would force w = blue — a direct contradiction.

  THEOREM 2 (Optimal Sub-structure / odd cycles resist clean 2-coloring):
    An odd cycle cannot be properly colored using only {blue, red} with
    no two cycle-adjacent vertices sharing a color. This forces at least
    one cycle vertex into the black "breaker" role. Proved as a
    self-contained parity argument (omega for arithmetic, no Mathlib
    bipartiteness API dependency).

  We do NOT formalize the paper's algorithm-level completeness claim
  ("iterating over each vertex... eventually seeded at a vertex that
  allows Algorithm C to fully map it") — that belongs to Lemma 16.
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
import MyGraphProject.vccbg.Thm13Lemma12_2a


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Colors, vertex cover, valid colorings (imported from Part 1 / 2(a))
-- ═══════════════════════════════════════════════════════════════════════════

open Color

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. A robust helper: two forced colors on the same vertex clash
-- ═══════════════════════════════════════════════════════════════════════════

/-- If `x` is forced to color `c1` by one rule and to `c2` by another,
    and `c1 ≠ c2`, this is a contradiction. Built with `▸` applied
    directly to `h2`'s own type (never `rw` against an external goal),
    so it is robust regardless of the surrounding goal's syntactic shape. -/
private theorem color_clash
    {C : Coloring V} {x : V} {c1 c2 : Color}
    (h1 : C x = c1) (h2 : C x = c2) (hne : c1 ≠ c2) : False :=
  hne (h1 ▸ h2)

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Theorem 1 — Conflict Resolution
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Theorem 1 (Conflict Resolution)**:
    No vertex `w ∈ S` can have both a blue neighbor and a red neighbor
    under a valid coloring.

    Paper (lines 2553–2556): "If the algorithm encounters an edge
    connecting vertices v and u where v is blue and u is already in the
    vertex cover S, then the algorithm labels u as black because
    assigning u a color would violate the alternating property." -/
theorem Lemma12_Part2b_conflict
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C)
    {w u₁ u₂ : V} (hwS : w ∈ S)
    (hadj₁ : G.Adj u₁ w) (hCu₁ : C u₁ = blue)
    (hadj₂ : G.Adj u₂ w) (hCu₂ : C u₂ = red) :
    False :=
  color_clash (hVC.V1 hadj₁ hCu₁ hwS) (hVC.V3 hadj₂ hCu₂ hwS) (by decide)

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. A binary case-bash helper
-- ═══════════════════════════════════════════════════════════════════════════

/-- `BR C x`: vertex `x` is colored either blue or red under `C`. -/
def BR (C : Coloring V) (x : V) : Prop := C x = blue ∨ C x = red

/-- If `x`, `y`, `z` are each blue-or-red, `x` differs from `y`, and `x`
    differs from `z`, then `y` and `z` must be equal — only two values
    are possible once white/black are excluded.

    Proof: case on each of `hx`, `hy`, `hz` (8 branches total). In any
    branch where `x` and `y` (or `x` and `z`) end up the same literal
    color, `hxy` (resp. `hxz`) becomes a self-contradictory `c ≠ c`,
    closing the goal via `absurd rfl`. In the two remaining branches,
    `y` and `z` are forced to the SAME literal color, closing the goal
    by `rfl`. -/
private theorem BR_eq_of_ne_ne
    {C : Coloring V} {x y z : V}
    (hx : BR C x) (hy : BR C y) (hz : BR C z)
    (hxy : C x ≠ C y) (hxz : C x ≠ C z) :
    C y = C z := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
    simp only [hx, hy, hz] at hxy hxz ⊢ <;>
    first | rfl | exact absurd rfl hxy | exact absurd rfl hxz

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Theorem 2 — Odd cycles resist proper 2-coloring
-- ═══════════════════════════════════════════════════════════════════════════

/-
  We represent an odd cycle by:
    n    : ℕ        the cycle length, with `n % 2 = 1` (odd) and `n ≥ 1`
    c    : ℕ → V     the cyclic vertex sequence (only c 0, ..., c (n-1)
                      matter; cyclicity is enforced via `% n`)
    hadj : ∀ k, G.Adj (c k) (c ((k + 1) % n))
                      the cycle's edges, wrapping at index n-1 → 0
-/

/-- **Parity-alternation lemma**: if every cycle vertex (index < n) is
    blue-or-red, and no two CONSECUTIVE indices below `n - 1` share a
    color, then the color at index `k` is forced by the color at index 0
    together with the parity of `k`. -/
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

/-- **Theorem 2 (Optimal Sub-structure)**:
    An odd cycle of length `n` cannot be properly colored with only
    {blue, red} such that no two cycle-adjacent vertices share a color.

    Proof: by `parity_alternation`, the color at the LAST index (n-1,
    which is EVEN since n is odd) must equal the color at index 0. But
    the wraparound edge demands they DIFFER. Contradiction. -/
theorem Lemma12_Part2b_oddcycle_no_proper_2coloring
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
-- §6. Corollary: at least one cycle vertex must be black
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary (Part 2(b) main conclusion)**:
    Given a valid coloring and an odd cycle, it is impossible for ALL
    cycle vertices to be blue-or-red: at least one must be black.

    Paper (lines 2546–2548): "at least one vertex in an odd cycle must
    be colored black." -/
theorem Lemma12_Part2b_some_black
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C)
    {n : ℕ} (hn_odd : n % 2 = 1) (hn_pos : 0 < n)
    {c : ℕ → V}
    (hadj : ∀ k, G.Adj (c k) (c ((k + 1) % n)))
    (hBR : ∀ k, k < n → BR C (c k)) :
    False := by
  -- Step 1: no two consecutive (non-wraparound) cycle vertices share a color.
  have hne : ∀ k, k + 1 < n → C (c k) ≠ C (c (k + 1)) := by
    intro k hk
    have hk' : (k + 1) % n = k + 1 := Nat.mod_eq_of_lt hk
    have hadjk : G.Adj (c k) (c (k + 1)) := hk' ▸ hadj k
    rcases hBR k (by omega) with hCk | hCk
    · -- C (c k) = blue
      intro heq
      rcases hBR (k + 1) hk with hCk1 | hCk1
      · -- c(k+1) also blue: case on S-membership to force black or red
        by_cases hS : c (k + 1) ∈ S
        · exact color_clash (hVC.V1 hadjk hCk hS) hCk1 (by decide)
        · exact color_clash (hVC.V2 hadjk hCk hS) hCk1 (by decide)
      · -- c(k+1) is red: but heq forces c(k+1) to equal c k's color (blue)
        have hcontra : C (c (k + 1)) = blue := heq.symm.trans hCk
        exact color_clash hcontra hCk1 (by decide)
    · -- C (c k) = red
      intro heq
      by_cases hS : c (k + 1) ∈ S
      · have hblue : C (c (k + 1)) = blue := hVC.V3 hadjk hCk hS
        have hred : C (c (k + 1)) = red := heq.symm.trans hCk
        exact color_clash hblue hred (by decide)
      · exact hVC.V4 hadjk hCk hS
  -- Step 2: the wraparound edge also forbids a shared color.
  have hwrap : C (c (n - 1)) ≠ C (c 0) := by
    have hn1 : n - 1 + 1 = n := by omega
    have hmod : (n - 1 + 1) % n = 0 := by rw [hn1]; exact Nat.mod_self n
    have hadj' : G.Adj (c (n - 1)) (c ((n - 1 + 1) % n)) := hadj (n - 1)
    have hadjwrap : G.Adj (c (n - 1)) (c 0) := hmod ▸ hadj'
    rcases hBR (n - 1) (by omega) with hC1 | hC1 <;> rcases hBR 0 hn_pos with hC0 | hC0
    · -- both blue: derive contradiction via S-membership case split
      intro heq
      by_cases hS : c 0 ∈ S
      · exact color_clash (hVC.V1 hadjwrap hC1 hS) (heq.symm.trans hC1) (by decide)
      · exact color_clash (hVC.V2 hadjwrap hC1 hS) (heq.symm.trans hC1) (by decide)
    · -- blue, red: genuinely different, close directly
      rw [hC1, hC0]; decide
    · -- red, blue: genuinely different, close directly
      rw [hC1, hC0]; decide
    · -- both red: derive contradiction
      intro heq
      by_cases hS : c 0 ∈ S
      · have hblue : C (c 0) = blue := hVC.V3 hadjwrap hC1 hS
        exact color_clash hblue (heq.symm.trans hC1) (by decide)
      · exact hVC.V4 hadjwrap hC1 hS
  exact Lemma12_Part2b_oddcycle_no_proper_2coloring hn_odd hn_pos hBR hwrap hne

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  AXIOM COUNT:  0
  SORRY COUNT:  0  (every proof step is complete)

  Proof map:
    color_clash                       — h1 ▸ h2, then hne applied      (2 lines)
    Lemma12_Part2b_conflict           — color_clash on V1/V3 outputs   (1 line)
    BR_eq_of_ne_ne                    — 8-way case bash, simp + first  (3 lines)
    parity_alternation                — induction on k, omega +        (~20 lines)
                                         BR_eq_of_ne_ne / color_clash
    Lemma12_Part2b_oddcycle_no_proper_2coloring
                                       — parity_alternation at n-1      (5 lines)
    Lemma12_Part2b_some_black         — derive hne, hwrap via           (~25 lines)
                                         color_clash case splits,
                                         then invoke the above theorem
-/
