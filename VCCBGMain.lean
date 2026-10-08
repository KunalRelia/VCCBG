module

-- ═══════════════════════════════════════════════════════════════════════════
-- `Theorem1` : VCCBG is NP-complete.
-- ═══════════════════════════════════════════════════════════════════════════
public import VCCBGPartI.thm1
/-
`Theorem1` depends on the following axioms in
  addition to the three standard Lean axioms:
  - [`VC_CG_NPHard`, `VC_InNP`, `NPHard_of_reduction`]
    We discuss the details of these published results in
    `§9. Commentary` of `VCCBGPartI.thm1.lean`.
-/


-- ═══════════════════════════════════════════════════════════════════════════
-- `Theorem2` : VCCBG is in P.
-- ═══════════════════════════════════════════════════════════════════════════
public import VCCBGPartII.thm2
/-
`Theorem2` does not depend on any additional axioms.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- `Theorem1` : Alternative VCCBG is NP-complete.
-- ═══════════════════════════════════════════════════════════════════════════
public import VCCBGSecB.thm1
/-
`Theorem1` depends on the following axioms in
  addition to the three standard Lean axioms:
  - [`NPHard_of_restriction`, `Theorem10`, `VC_InNP`, `Whitney`]
    We discuss the details of these published results in
    `§6. Commentary` of `VCCBGSecB.thm1.lean`.
-/


-- ═══════════════════════════════════════════════════════════════════════════
-- `Theorem13` : The alternative algorithm returns Yes
--   if and only if VC-CBG is a Yes instance.
-- ═══════════════════════════════════════════════════════════════════════════
public import VCCBGSecC.thm13
/-
`Theorem13` depends on the following axioms in
  addition to the three standard Lean axioms:

  - [`PetersenMatching`, `AlgB_spec`, `MatchingLowerBound`]
    We discuss the details of these published results in
    `§8. Axiom inventory and discharge guide` of `thm13_lemma9.lean`.

  - [`seed_robustness`]
    We discuss the details of this new result in
    `§3. THE AXIOM.` of `thm13_lemma16_proof.lean`.
-/
