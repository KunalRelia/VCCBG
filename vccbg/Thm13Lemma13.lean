/-
  Lean 4 / Mathlib — Lemma 13
  "Given a cubic bridgeless graph G and a vertex v from the vertex cover
   S, if the graph is colored using Algorithm C by seeding on vertex v,
   then the red and blue vertices form a bipartite graph."

  Source: paper §C.2.2, lines 2592–2614 (and footnote 52).

  ═══════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE PROVES
  ═══════════════════════════════════════════════════════════════════════════

  Paper's proof, condensed (lines 2599–2611):
    "A neighboring vertex of a blue vertex that is also in the vertex
     cover S is colored black. By design, no adjacent vertices can be
     colored blue."
    "A neighboring vertex of a red vertex that is also not in the
     vertex cover S is not possible... its neighbor must be in the
     vertex cover S."
    "Overall... the induced subgraph of red and blue vertices is a
     bipartite graph. This is because a graph is bipartite if and only
     if it is 2-colorable."
  Footnote 52: "any edge connecting vertices u and v that would violate
     bipartiteness in S results in v being assigned to the set of black
     vertices."

  This reduces to exactly two claims about any `ValidColoring`:

  (NO-BLUE-BLUE) No two adjacent vertices are both blue.
    Proof: if `G.Adj u w`, `C u = blue`, `C w = blue`, case on `w ∈ S`:
      • `w ∈ S` → V1 forces `C w = black`, contradicting `C w = blue`.
      • `w ∉ S` → V2 forces `C w = red`,   contradicting `C w = blue`.
    Either way, False. This uses only V1 and V2 — no procedural
    (Algorithm-C-traversal) argument is needed; it is an immediate
    consequence of the flat `ValidColoring` constraints, since V1 and
    V2 are jointly exhaustive over `w ∈ S` vs. `w ∉ S` and BOTH force a
    non-blue color on `w`.

  (NO-RED-RED) No two adjacent vertices are both red.
    Proof: if `G.Adj u w`, `C u = red`, `C w = red`, then by V4,
    `w ∈ S` (else immediate False); by V3, `C w = blue`, contradicting
    `C w = red`.

  These two facts are packaged as a `BipColoring` structure — the
  predicate-level statement that the blue-class and red-class form a
  bipartition with no internal edges, i.e. exactly "the induced
  subgraph of red and blue vertices is a bipartite graph."

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
import MyGraphProject.vccbg.Thm13Lemma12_overall

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {V : Type*} [DecidableEq V] [Fintype V]
-- variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V}

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. Colors, vertex cover, valid colorings (imported from the other files)
-- ═══════════════════════════════════════════════════════════════════════════

open Color

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. The two structural facts
-- ═══════════════════════════════════════════════════════════════════════════

/-- **No-blue-blue**: no two adjacent vertices are both blue.

    Paper (lines 2603–2604): "A neighboring vertex of a blue vertex that
    is also in the vertex cover S is colored black. By design, no
    adjacent vertices can be colored blue."

    Proof: case on `w ∈ S`. Either branch (V1 or V2) forces `w` to a
    color other than blue, contradicting the hypothesis `C w = blue`. -/
theorem Lemma13_no_blue_blue
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C)
    {u w : V} (hadj : G.Adj u w) (hCu : C u = blue) (hCw : C w = blue) :
    False := by
  by_cases hwS : w ∈ S
  · have hblack : C w = black := hVC.V1 hadj hCu hwS
    rw [hCw] at hblack
    exact absurd hblack (by decide)
  · have hred : C w = red := hVC.V2 hadj hCu hwS
    rw [hCw] at hred
    exact absurd hred (by decide)

/-- **No-red-red**: no two adjacent vertices are both red.

    Paper (lines 2605–2608): "A neighboring vertex of a red vertex that
    is also not in the vertex cover S is not possible because the red
    vertex, by design, is not in the vertex cover S. Therefore, its
    neighbor must be in the vertex cover S for it to be a valid vertex
    cover."

    Proof: by V4, `w ∈ S` (else immediate False). By V3, `C w = blue`,
    contradicting the hypothesis `C w = red`. -/
theorem Lemma13_no_red_red
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C)
    {u w : V} (hadj : G.Adj u w) (hCu : C u = red) (hCw : C w = red) :
    False := by
  by_cases hwS : w ∈ S
  · have hblue : C w = blue := hVC.V3 hadj hCu hwS
    rw [hCw] at hblue
    exact absurd hblue (by decide)
  · exact hVC.V4 hadj hCu hwS

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Bipartite-structure packaging
-- ═══════════════════════════════════════════════════════════════════════════

/-- `BipColoring G U W`: the predicates `U`, `W` form a bipartition of
    (a subset of) the vertices of `G` with no internal edges — the
    precise structural content of "the induced subgraph on `U ∪ W` is
    bipartite." -/
structure BipColoring (G : SimpleGraph V) (U W : V → Prop) : Prop where
  /-- No vertex is both `U` and `W`. -/
  disj : ∀ x, ¬ (U x ∧ W x)
  /-- No two adjacent vertices are both `U`. -/
  noU  : ∀ ⦃u w⦄, G.Adj u w → U u → ¬ U w
  /-- No two adjacent vertices are both `W`. -/
  noW  : ∀ ⦃u w⦄, G.Adj u w → W u → ¬ W w

/-- **Lemma 13**: under any valid coloring, the blue vertices and the
    red vertices form a bipartite graph.

    Paper (lines 2609–2611): "the 2-coloring (red and blue) of the
    graph G done by Algorithm C, by definition, implies that the
    induced subgraph of red and blue vertices is a bipartite graph."

    Proof: `disj` is immediate (a vertex's color is a single value, so
    it cannot be both `blue` and `red` at once — `Color.noConfusion`).
    `noU` is `Lemma13_no_blue_blue`; `noW` is `Lemma13_no_red_red`. -/
theorem Lemma13
    {S : Finset V} {v : V} {C : Coloring V}
    (hVC : ValidColoring G S v C) :
    BipColoring G (fun x => C x = blue) (fun x => C x = red) where
  disj := fun x ⟨hb, hr⟩ => by rw [hb] at hr; exact absurd hr (by decide)
  noU  := fun u w hadj hCu hCw => Lemma13_no_blue_blue hVC hadj hCu hCw
  noW  := fun u w hadj hCu hCw => Lemma13_no_red_red hVC hadj hCu hCw

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Status
-- ═══════════════════════════════════════════════════════════════════════════
/-
  AXIOM COUNT:  0
  SORRY COUNT:  0  (every proof step is complete)

  Proof map:
    Lemma13_no_blue_blue — by_cases w∈S; V1 or V2 forces a non-blue
                           color on w, contradicting C w = blue.  (7 lines)
    Lemma13_no_red_red   — by_cases w∈S; V4 gives False directly when
                           w∉S; V3 forces blue when w∈S, contradicting
                           C w = red.                              (6 lines)
    BipColoring          — predicate-level bipartition structure,
                           no [Fintype V] required.
    Lemma13              — disj trivial (Color.noConfusion via decide);
                           noU/noW are exactly the two theorems above.

  This is the complete formalization of Lemma 13: the four forcing rules
  V1–V4 of `ValidColoring` are jointly exhaustive over S-membership at
  every neighbor, and BOTH exhaustive branches force a non-matching
  color whenever an edge would otherwise create a monochromatic
  blue-blue or red-red pair. No procedural (Algorithm-C-traversal)
  argument — e.g. `AltReachActive` from Lemma12_Part1_Bipartite.lean —
  is needed for this lemma; it follows directly from the flat
  `ValidColoring` constraint set.
-/
