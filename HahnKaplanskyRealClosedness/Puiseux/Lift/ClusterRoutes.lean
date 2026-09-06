/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Lift.Hensel
import HahnKaplanskyRealClosedness.Puiseux.Lift.ClusterBasic

/-!
# Fixed-level Puiseux valuation-cluster routes

This module contains the root, ramification, and ambient-Hahn bridges for the fixed-level cluster
package.  The coefficient-ring and residue branch API lives in the Basic module.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

theorem fixedLevelTranslatedSimpleZeroBranchRootHypothesis_of_levelSimpleRootLift
    (hlift : LevelSimpleRootLiftHypothesis k) :
    FixedLevelTranslatedSimpleZeroBranchRootHypothesis k := by
  intro N F m y _hymem _hy0 hbranch
  let P : Polynomial (fixedDenominatorValuationSubring k N) :=
    F.comp (Polynomial.X + Polynomial.C y)
  have hbranchP :
      (fixedLevelResiduePolynomial k N P).rootMultiplicity 0 = 1 := by
    simpa [P, FixedLevelResidueBranchMultiplicity] using hbranch
  have hpos :
      0 < (fixedLevelResiduePolynomial k N P).rootMultiplicity 0 := by
    rw [hbranchP]
    norm_num
  have hroot_res : (fixedLevelResiduePolynomial k N P).IsRoot 0 :=
    (Polynomial.rootMultiplicity_pos'.mp hpos).2
  have hpne : fixedLevelResiduePolynomial k N P ≠ 0 :=
    (Polynomial.rootMultiplicity_pos'.mp hpos).1
  have hder_res : ((fixedLevelResiduePolynomial k N P).derivative).eval 0 ≠ 0 := by
    intro hzero
    have hder_root : ((fixedLevelResiduePolynomial k N P).derivative).IsRoot 0 := by
      simpa [Polynomial.IsRoot] using hzero
    have hlt :
        1 < (fixedLevelResiduePolynomial k N P).rootMultiplicity 0 :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hpne).mpr ⟨hroot_res, hder_root⟩
    rw [hbranchP] at hlt
    exact (Nat.lt_irrefl 1) hlt
  have hroot_eval :
      P.eval₂ (fixedDenominatorConstantCoeffRingHom k N) 0 = 0 := by
    simpa [fixedLevelResiduePolynomial, Polynomial.IsRoot, Polynomial.eval_map] using hroot_res
  have hder_eval :
      P.derivative.eval₂ (fixedDenominatorConstantCoeffRingHom k N) 0 ≠ 0 := by
    simpa [fixedLevelResiduePolynomial, Polynomial.derivative_map, Polynomial.eval_map] using
      hder_res
  rcases hlift N P 0 hroot_eval hder_eval with ⟨a, haroot, ha0⟩
  let aq : fixedDenominatorValuationSubring k (N * 1) :=
    fixedDenominatorValuationSubringMapMulRight k N 1 a
  refine ⟨1, aq, ?_, ?_⟩
  · have hamem : a ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N) := by
      rw [← fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) N,
        RingHom.mem_ker]
      exact ha0
    exact fixedDenominatorValuationSubringMapMulRight_mem_maximalIdeal (k := k) hamem
  · change (P.map (fixedDenominatorValuationSubringMapMulRight k N 1)).IsRoot aq
    exact Polynomial.IsRoot.map_fixedDenominatorValuationSubringMapMulRight (k := k) haroot

theorem fixedLevelTranslatedLowerMultipleZeroBranchRootAt_of_below {M : ℕ}
    (hbelow : FixedLevelOddClusterRootBelow k M) :
    ∀ {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)}
      {y : fixedDenominatorValuationSubring k N} {r : ℕ},
      y ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N) →
        fixedDenominatorConstantCoeffRingHom k N y = 0 →
          1 < r → Odd r → r < M →
            FixedLevelResidueBranchMultiplicity k N
              (F.comp (Polynomial.X + Polynomial.C y)) M 0 r →
                FixedLevelRamifiedRoot k N (F.comp (Polynomial.X + Polynomial.C y)) := by
  intro N F y r _hymem _hy0 hmultiple hrodd hrlt hbranch
  exact hbelow hrlt
    (fixedLevelOddCluster_of_zero_residueBranchMultiplicity (k := k)
      (Nat.lt_trans Nat.zero_lt_one hmultiple) hrodd hbranch)

theorem FixedLevelRamifiedRoot.of_translated_root {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)}
    {y : fixedDenominatorValuationSubring k N}
    (hymem : y ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k N))
    (hroot : FixedLevelRamifiedRoot k N (F.comp (Polynomial.X + Polynomial.C y))) :
    FixedLevelRamifiedRoot k N F := by
  rcases hroot with ⟨q, x, hxmem, hxroot⟩
  let yq : fixedDenominatorValuationSubring k (N * q) :=
    fixedDenominatorValuationSubringMapMulRight k N q y
  refine ⟨q, x + yq, ?_, ?_⟩
  · exact add_mem hxmem
      (fixedDenominatorValuationSubringMapMulRight_mem_maximalIdeal (k := k) hymem)
  · rw [Polynomial.IsRoot] at hxroot ⊢
    simpa [yq, Polynomial.map_comp, Polynomial.eval_comp] using hxroot

theorem fixedLevelOddClusterRootAt_of_below_levelSimpleRootLift_or_same {M : ℕ}
    (hlift : LevelSimpleRootLiftHypothesis k)
    (hbelow : FixedLevelOddClusterRootBelow k M)
    (hsame : FixedLevelTranslatedSameMultiplicityZeroBranchRootAt k M) :
    FixedLevelOddClusterRootAt k M := by
  intro N F hF
  rcases hF.exists_translatedZeroBranchInMaximalIdeal (k := k) with
    ⟨y, r, hymem, hy0, hrpos, hrodd, hrle, hbranch⟩
  have hsimple : FixedLevelTranslatedSimpleZeroBranchRootHypothesis k :=
    fixedLevelTranslatedSimpleZeroBranchRootHypothesis_of_levelSimpleRootLift
      (k := k) hlift
  rcases (Nat.succ_le_of_lt hrpos).eq_or_lt with hr_one | hmultiple
  · have hbranch_one :
        FixedLevelResidueBranchMultiplicity k N
          (F.comp (Polynomial.X + Polynomial.C y)) M 0 1 := by
      simpa [← hr_one] using hbranch
    exact FixedLevelRamifiedRoot.of_translated_root (k := k) hymem
      (hsimple hymem hy0 hbranch_one)
  · rcases lt_or_eq_of_le hrle with hrlt | hr_eq
    · exact FixedLevelRamifiedRoot.of_translated_root (k := k) hymem
        (fixedLevelTranslatedLowerMultipleZeroBranchRootAt_of_below (k := k) hbelow
          hymem hy0 hmultiple hrodd hrlt hbranch)
    · have hbranch_same :
          FixedLevelResidueBranchMultiplicity k N
            (F.comp (Polynomial.X + Polynomial.C y)) M 0 M := by
        simpa [hr_eq] using hbranch
      exact FixedLevelRamifiedRoot.of_translated_root (k := k) hymem
        (hsame hymem hy0 (by simpa [hr_eq] using hmultiple)
          (by simpa [hr_eq] using hrodd) hbranch_same)

theorem FixedLevelRamifiedRoot.boundedRootInMaximalIdeal {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)}
    (hroot : FixedLevelRamifiedRoot k N F) :
    BoundedRootInMaximalIdeal k
      (F.map (fixedDenominatorValuationToHahnValuationSubring k N)) := by
  rcases hroot with ⟨q, x, hxmem, hxroot⟩
  let y : HahnField.valuationSubring k ℚ :=
    fixedDenominatorValuationToHahnValuationSubring k (N * q) x
  refine ⟨y, ?_, ?_, ?_⟩
  · have hxpos :
        (0 : WithTop ℚ) < addVal k (x : Series k) :=
      (mem_fixedDenominator_maximalIdeal_iff_pos_addVal (k := k) x).mp hxmem
    exact (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ y).mpr (by
      simpa [y, addVal_apply] using hxpos)
  · change HasBoundedDenominatorSupport k ((x : Series k) : HahnField k ℚ)
    exact ⟨N * q, x.property.2⟩
  · have hxroot_hahn :
        (((F.map (fixedDenominatorValuationSubringMapMulRight k N q)).map
          (fixedDenominatorValuationToHahnValuationSubring k (N * q))).IsRoot y) :=
      Polynomial.IsRoot.map hxroot
    simpa [y, Polynomial.map_map] using hxroot_hahn

theorem FixedLevelOddCluster.boundedValuationSubringHypotheses {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    (hcluster : FixedLevelOddCluster k N F M) :
    BoundedValuationSubringOddClusterHypotheses k
      (F.map (fixedDenominatorValuationToHahnValuationSubring k N)) M := by
  refine ⟨hcluster.pos, hcluster.odd, ?_, ?_, ?_⟩
  · intro i
    rw [Polynomial.coeff_map]
    change HasBoundedDenominatorSupport k ((F.coeff i : Series k) : HahnField k ℚ)
    exact ⟨N, (F.coeff i).property.2⟩
  · intro i hi
    rw [Polynomial.coeff_map]
    have hpos :
        (0 : WithTop ℚ) < addVal k (F.coeff i : Series k) :=
      (mem_fixedDenominator_maximalIdeal_iff_pos_addVal (k := k) (F.coeff i)).mp
        (hcluster.small i hi)
    exact (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ
      (fixedDenominatorValuationToHahnValuationSubring k N (F.coeff i))).mpr (by
        simpa [addVal_apply] using hpos)
  · rw [Polynomial.coeff_map]
    refine HahnField.isUnit_of_constantCoeffRingHom_ne_zero k ℚ
      (fixedDenominatorValuationToHahnValuationSubring k N (F.coeff M)) ?_
    simpa [fixedDenominatorConstantCoeffRingHom] using
      fixedDenominatorConstantCoeffRingHom_ne_zero_of_isUnit
        (k := k) hcluster.unit

theorem FixedLevelTranslatedSameMultiplicityZeroBranch.translatedBoundedValuationSubringHypotheses
    {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y) :
    BoundedValuationSubringOddClusterHypotheses k
      ((F.comp (Polynomial.X + Polynomial.C y)).map
        (fixedDenominatorValuationToHahnValuationSubring k N)) M :=
  (hbranch.translatedOddCluster (k := k)).boundedValuationSubringHypotheses (k := k)

theorem fixedDenominatorValuationToHahnValuationSubring_map_comp_X_add_C {N : ℕ+}
    (F : Polynomial (fixedDenominatorValuationSubring k N))
    (y : fixedDenominatorValuationSubring k N) :
    (F.comp (Polynomial.X + Polynomial.C y)).map
        (fixedDenominatorValuationToHahnValuationSubring k N) =
      (F.map (fixedDenominatorValuationToHahnValuationSubring k N)).comp
        (Polynomial.X +
          Polynomial.C (fixedDenominatorValuationToHahnValuationSubring k N y)) := by
  rw [Polynomial.map_comp]
  congr
  ext i
  simp

theorem FixedLevelTranslatedSameMultiplicityZeroBranch.translatedBoundedValuationHypotheses_comp
    {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y) :
    BoundedValuationSubringOddClusterHypotheses k
      ((F.map (fixedDenominatorValuationToHahnValuationSubring k N)).comp
        (Polynomial.X +
          Polynomial.C (fixedDenominatorValuationToHahnValuationSubring k N y))) M := by
  simpa [fixedDenominatorValuationToHahnValuationSubring_map_comp_X_add_C (k := k) F y]
    using hbranch.translatedBoundedValuationSubringHypotheses (k := k)

theorem BoundedRootInMaximalIdeal.fixedLevelRamifiedRoot {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)}
    (hroot : BoundedRootInMaximalIdeal k
      (F.map (fixedDenominatorValuationToHahnValuationSubring k N))) :
    FixedLevelRamifiedRoot k N F := by
  rcases hroot with ⟨y, hymem, hybd, hyroot⟩
  rcases hybd with ⟨q, hyden⟩
  let xS : Series k := ofHahnField k (y : HahnField k ℚ) ⟨q, hyden⟩
  have hxmem_fixed : xS ∈ fixedDenominatorValuationSubring k (N * q) := by
    constructor
    · rw [mem_valuationSubring_iff]
      change (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (y : HahnField k ℚ)
      exact (HahnField.mem_valuationSubring_iff k ℚ y).mp y.property
    · change HasDenominatorSupport k (N * q) (xS : HahnField k ℚ)
      change HasDenominatorSupport k (N * q) (y : HahnField k ℚ)
      exact hasDenominatorSupport_mono_den k
        (fun _ hden => by
          simpa [mul_comm] using (hasDenominator_mul_right (n' := N) hden)) hyden
  let x : fixedDenominatorValuationSubring k (N * q) := ⟨xS, hxmem_fixed⟩
  have hxmem :
      x ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k (N * q)) := by
    rw [mem_fixedDenominator_maximalIdeal_iff_pos_addVal]
    have hypos :
        (0 : WithTop ℚ) < HahnField.addVal k ℚ (y : HahnField k ℚ) :=
      (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ y).mp hymem
    change (0 : WithTop ℚ) < HahnField.addVal k ℚ (y : HahnField k ℚ)
    exact hypos
  have hxy :
      fixedDenominatorValuationToHahnValuationSubring k (N * q) x = y := by
    apply Subtype.ext
    change (y : HahnField k ℚ) = (y : HahnField k ℚ)
    rfl
  have hmap :
      (F.map (fixedDenominatorValuationSubringMapMulRight k N q)).map
          (fixedDenominatorValuationToHahnValuationSubring k (N * q)) =
        F.map (fixedDenominatorValuationToHahnValuationSubring k N) := by
    rw [Polynomial.map_map]
    simp
  have hroot_mapped :
      (((F.map (fixedDenominatorValuationSubringMapMulRight k N q)).map
        (fixedDenominatorValuationToHahnValuationSubring k (N * q))).IsRoot
          (fixedDenominatorValuationToHahnValuationSubring k (N * q) x)) := by
    simpa [hmap, hxy] using hyroot
  have hinj :
      Function.Injective (fixedDenominatorValuationToHahnValuationSubring k (N * q)) := by
    intro a b hab
    ext
    exact congrArg (fun z : HahnField.valuationSubring k ℚ => (z : HahnField k ℚ)) hab
  refine ⟨q, x, hxmem, ?_⟩
  rw [Polynomial.IsRoot] at hroot_mapped ⊢
  apply hinj
  simpa [Polynomial.eval_map] using hroot_mapped

end

end Puiseux

end HahnKaplanskyRealClosedness
