/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Valuation.ClusterBasic
import HahnKaplanskyRealClosedness.Puiseux.Lift.Residue

/-!
# Fixed-level Puiseux valuation clusters

This file contains the fixed-denominator valuation-level odd-cluster predicates used as the
next staging point for the Newton-Puiseux / omega-continuation route.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- Odd-cluster side conditions inside one fixed-denominator valuation level.

The coefficient-ring bookkeeping is the generic local-ring package; this alias only supplies the
fixed-level coefficient ring while retaining the original four-field tuple shape.
-/
abbrev FixedLevelOddCluster (N : ℕ+)
    (F : Polynomial (fixedDenominatorValuationSubring k N)) (m : ℕ) : Prop :=
  LocalOddClusterHypotheses (R := fixedDenominatorValuationSubring k N) F m

theorem FixedLevelOddCluster.residue_coeff_eq_zero_of_lt {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m i : ℕ}
    (h : FixedLevelOddCluster k N F m) (hi : i < m) :
    (fixedLevelResiduePolynomial k N F).coeff i = 0 := by
  have hsmall := h.small i hi
  rw [← fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) N,
    RingHom.mem_ker] at hsmall
  simpa using hsmall

theorem FixedLevelOddCluster.residue_coeff_ne_zero {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ}
    (h : FixedLevelOddCluster k N F m) :
    (fixedLevelResiduePolynomial k N F).coeff m ≠ 0 := by
  simpa using
    fixedDenominatorConstantCoeffRingHom_ne_zero_of_isUnit (k := k) h.unit

theorem FixedLevelOddCluster.residuePolynomial_ne_zero {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ}
    (h : FixedLevelOddCluster k N F m) :
    fixedLevelResiduePolynomial k N F ≠ 0 := by
  intro hzero
  exact h.residue_coeff_ne_zero (k := k) (by simp [hzero])

theorem FixedLevelOddCluster.residue_rootMultiplicity_zero_eq {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ}
    (h : FixedLevelOddCluster k N F m) :
    (fixedLevelResiduePolynomial k N F).rootMultiplicity 0 = m := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  apply le_antisymm
  · exact Polynomial.natTrailingDegree_le_of_ne_zero (h.residue_coeff_ne_zero (k := k))
  · exact Polynomial.le_natTrailingDegree
      (h.residuePolynomial_ne_zero (k := k))
      (fun i hi => h.residue_coeff_eq_zero_of_lt (k := k) hi)

theorem FixedLevelOddCluster.zero_residueBranchMultiplicity {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ}
    (h : FixedLevelOddCluster k N F m) :
    FixedLevelResidueBranchMultiplicity k N F m 0 m :=
  h.residue_rootMultiplicity_zero_eq (k := k)

theorem FixedLevelOddCluster.exists_translatedZeroBranchInMaximalIdeal {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ}
    (h : FixedLevelOddCluster k N F m) :
    ∃ y : fixedDenominatorValuationSubring k N, ∃ r : ℕ,
      y ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N) ∧
        fixedDenominatorConstantCoeffRingHom k N y = 0 ∧
          0 < r ∧ Odd r ∧ r ≤ m ∧
            FixedLevelResidueBranchMultiplicity k N
              (F.comp (Polynomial.X + Polynomial.C y)) m 0 r := by
  have hbranch : FixedLevelResidueBranchMultiplicity k N F m 0 m :=
    h.zero_residueBranchMultiplicity (k := k)
  rcases hbranch.exists_translated_zero_branch (k := k) with ⟨y, hy, htranslated⟩
  have hymem : y ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N) := by
    rw [← fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) N,
      RingHom.mem_ker]
    exact hy
  exact ⟨y, m, hymem, hy, h.pos, h.odd, le_rfl, htranslated⟩

theorem fixedLevelOddCluster_of_zero_residueBranchMultiplicity {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m r : ℕ}
    (hrpos : 0 < r) (hrodd : Odd r)
    (hbranch : FixedLevelResidueBranchMultiplicity k N F m 0 r) :
    FixedLevelOddCluster k N F r := by
  have htrail :
      (fixedLevelResiduePolynomial k N F).natTrailingDegree = r := by
    simpa [FixedLevelResidueBranchMultiplicity,
      Polynomial.rootMultiplicity_eq_natTrailingDegree'] using hbranch
  have hres_ne : fixedLevelResiduePolynomial k N F ≠ 0 := by
    intro hzero
    have hrzero : r = 0 := by
      simpa [FixedLevelResidueBranchMultiplicity, hzero] using hbranch.symm
    exact (Nat.ne_of_gt hrpos) hrzero
  refine ⟨hrpos, hrodd, ?_, ?_⟩
  · intro i hi
    rw [← fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) N,
      RingHom.mem_ker]
    rw [← coeff_fixedLevelResiduePolynomial]
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by simpa [htrail] using hi)
  · refine fixedDenominator_isUnit_of_constantCoeffRingHom_ne_zero (k := k) (F.coeff r) ?_
    rw [← coeff_fixedLevelResiduePolynomial]
    simpa [htrail] using
      (Polynomial.coeff_natTrailingDegree_ne_zero
        (p := fixedLevelResiduePolynomial k N F)).2 hres_ne

/-- A fixed-level polynomial has a root after passing to a finite ramified level. -/
def FixedLevelRamifiedRoot (N : ℕ+)
    (F : Polynomial (fixedDenominatorValuationSubring k N)) : Prop :=
  ∃ q : ℕ+,
    ∃ x : fixedDenominatorValuationSubring k (N * q),
      x ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k (N * q)) ∧
        (F.map (fixedDenominatorValuationSubringMapMulRight k N q)).IsRoot x

/-- Fixed-level odd clusters of one fixed multiplicity have ramified roots.  This is the local
form used for induction on the cluster multiplicity. -/
def FixedLevelOddClusterRootAt (M : ℕ) : Prop :=
  ∀ {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)},
    FixedLevelOddCluster k N F M → FixedLevelRamifiedRoot k N F

/-- Fixed-level odd clusters of multiplicity strictly below `M` have ramified roots. -/
def FixedLevelOddClusterRootBelow (M : ℕ) : Prop :=
  ∀ {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)} {r : ℕ},
    r < M → FixedLevelOddCluster k N F r → FixedLevelRamifiedRoot k N F

/-- The simple translated zero-branch case.  This is the part intended to be discharged by
fixed-level simple-root / Hensel lifting. -/
def FixedLevelTranslatedSimpleZeroBranchRootHypothesis : Prop :=
  ∀ {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ}
    {y : fixedDenominatorValuationSubring k N},
    y ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N) →
      fixedDenominatorConstantCoeffRingHom k N y = 0 →
        FixedLevelResidueBranchMultiplicity k N
          (F.comp (Polynomial.X + Polynomial.C y)) m 0 1 →
            FixedLevelRamifiedRoot k N (F.comp (Polynomial.X + Polynomial.C y))

/-- Same-multiplicity translated zero branches at one fixed multiplicity.  This is the local
omega-continuation input for the induction step at `M`. -/
def FixedLevelTranslatedSameMultiplicityZeroBranchRootAt (M : ℕ) : Prop :=
  ∀ {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)}
    {y : fixedDenominatorValuationSubring k N},
    y ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N) →
      fixedDenominatorConstantCoeffRingHom k N y = 0 →
        1 < M → Odd M →
          FixedLevelResidueBranchMultiplicity k N
            (F.comp (Polynomial.X + Polynomial.C y)) M 0 M →
              FixedLevelRamifiedRoot k N (F.comp (Polynomial.X + Polynomial.C y))

/-- Bundled same-multiplicity branch data.  This is the fixed-level input that the
omega-continuation argument still has to discharge. -/
def FixedLevelTranslatedSameMultiplicityZeroBranch (N : ℕ+)
    (F : Polynomial (fixedDenominatorValuationSubring k N)) (M : ℕ)
    (y : fixedDenominatorValuationSubring k N) : Prop :=
  y ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N) ∧
    fixedDenominatorConstantCoeffRingHom k N y = 0 ∧
      1 < M ∧ Odd M ∧
        FixedLevelResidueBranchMultiplicity k N
          (F.comp (Polynomial.X + Polynomial.C y)) M 0 M

theorem FixedLevelTranslatedSameMultiplicityZeroBranch.mem {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y) :
    y ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N) :=
  hbranch.1

theorem FixedLevelTranslatedSameMultiplicityZeroBranch.one_lt {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y) :
    1 < M :=
  hbranch.2.2.1

theorem FixedLevelTranslatedSameMultiplicityZeroBranch.pos {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y) :
    0 < M :=
  Nat.lt_trans Nat.zero_lt_one (hbranch.one_lt (k := k))

theorem FixedLevelTranslatedSameMultiplicityZeroBranch.odd {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y) :
    Odd M :=
  hbranch.2.2.2.1

theorem FixedLevelTranslatedSameMultiplicityZeroBranch.branchMultiplicity {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y) :
    FixedLevelResidueBranchMultiplicity k N (F.comp (Polynomial.X + Polynomial.C y)) M 0 M :=
  hbranch.2.2.2.2

theorem FixedLevelTranslatedSameMultiplicityZeroBranch.translatedOddCluster {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y) :
    FixedLevelOddCluster k N (F.comp (Polynomial.X + Polynomial.C y)) M :=
  fixedLevelOddCluster_of_zero_residueBranchMultiplicity (k := k)
    (hbranch.pos (k := k)) (hbranch.odd (k := k))
    (hbranch.branchMultiplicity (k := k))

end

end Puiseux

end HahnKaplanskyRealClosedness
