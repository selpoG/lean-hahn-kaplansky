/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Support.FiniteLevel
import HahnKaplanskyRealClosedness.Puiseux.Valuation.ClusterHypotheses
import HahnKaplanskyRealClosedness.Puiseux.Newton.PolynomialSupport

/-!
# Scaled odd-cluster hypotheses and root bridges

This file contains the bridge that scales Puiseux polynomials into the ambient Hahn field
and packages the resulting side conditions as odd-cluster hypotheses.
-/

namespace HahnKaplanskyRealClosedness
namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

/-- Rational slope data that turns an odd-degree Puiseux polynomial into an integral
nat-degree cluster problem after Hahn-field scaling. -/
theorem exists_natDegree_scaling_conditions
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (Series k)} (hodd : Odd F.natDegree) :
    ∃ (nδ nlam : ℕ+) (δ lam : ℚ),
      ∃ (_hδ : HasDenominator nδ δ) (_hlam : HasDenominator nlam lam),
        (∀ i,
          (0 : WithTop ℚ) ≤
            (-(lam : ℚ) : WithTop ℚ) + HahnField.addVal k ℚ (F.coeff i : HahnField k ℚ) +
              i • (δ : WithTop ℚ)) ∧
        (∀ i, i < F.natDegree →
          (0 : WithTop ℚ) <
            (-(lam : ℚ) : WithTop ℚ) + HahnField.addVal k ℚ (F.coeff i : HahnField k ℚ) +
              i • (δ : WithTop ℚ)) ∧
        (-(lam : ℚ) : WithTop ℚ) +
            HahnField.addVal k ℚ (F.coeff F.natDegree : HahnField k ℚ) +
            F.natDegree • (δ : WithTop ℚ) =
          0 := by
  let FH : Polynomial (HahnField k ℚ) := mapPolynomialToHahnField k F
  have hdeg : FH.natDegree = F.natDegree := by
    simp [FH]
  have hFHodd : Odd FH.natDegree := by
    simpa [FH] using hodd
  have hFH : FH ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hFHodd
    exact Nat.not_odd_zero hFHodd
  rcases HahnField.exists_natDegree_dominating_slope k ℚ hFH with ⟨δ, γn, hγn, hdom⟩
  let lam : ℚ := γn + F.natDegree • δ
  rcases exists_hasDenominator δ with ⟨nδ, hδ⟩
  rcases exists_hasDenominator lam with ⟨nlam, hlam⟩
  refine ⟨nδ, nlam, δ, lam, hδ, hlam, ?_, ?_, ?_⟩
  · intro i
    have hi :
        (0 : WithTop ℚ) ≤
          (-(lam : ℚ) : WithTop ℚ) + HahnField.addVal k ℚ (FH.coeff i) +
            i • (δ : WithTop ℚ) := by
      by_cases hi_lt : i < FH.natDegree
      · exact le_of_lt (by
          by_cases hisupp : i ∈ FH.support
          · have hierase : i ∈ FH.support.erase FH.natDegree := by
              exact Finset.mem_erase.mpr ⟨ne_of_lt hi_lt, hisupp⟩
            have hpos := HahnField.withTop_scaledValue_pos_of_dominating
              (Γ := ℚ) (Nat.le_of_lt hi_lt) (hdom i hierase)
            simpa [lam, hdeg, HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ FH hisupp]
              using hpos
          · have hcoeff : FH.coeff i = 0 := Polynomial.notMem_support_iff.mp hisupp
            simp [lam, hcoeff])
      · by_cases hi_eq : i = FH.natDegree
        · subst i
          exact le_of_eq (by
            rw [hγn]
            simpa [lam, FH] using
              (HahnField.withTop_scaledValue_natDegree_eq_zero
                (Γ := ℚ) F.natDegree γn δ).symm)
        · have hn_lt : FH.natDegree < i := lt_of_le_of_ne (le_of_not_gt hi_lt) (Ne.symm hi_eq)
          have hcoeff : FH.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn_lt
          simp [lam, hcoeff]
    simpa [FH, coeff_mapPolynomialToHahnField] using hi
  · intro i hiF
    have hi : i < FH.natDegree := by
      simpa [FH] using hiF
    have hlt :
        (0 : WithTop ℚ) <
          (-(lam : ℚ) : WithTop ℚ) + HahnField.addVal k ℚ (FH.coeff i) +
            i • (δ : WithTop ℚ) := by
      by_cases hisupp : i ∈ FH.support
      · have hierase : i ∈ FH.support.erase FH.natDegree := by
          exact Finset.mem_erase.mpr ⟨ne_of_lt hi, hisupp⟩
        have hpos := HahnField.withTop_scaledValue_pos_of_dominating
          (Γ := ℚ) (Nat.le_of_lt hi) (hdom i hierase)
        simpa [lam, hdeg, HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ FH hisupp]
          using hpos
      · have hcoeff : FH.coeff i = 0 := Polynomial.notMem_support_iff.mp hisupp
        simp [lam, hcoeff]
    simpa [FH, coeff_mapPolynomialToHahnField] using hlt
  · have hmain :
        (-(lam : ℚ) : WithTop ℚ) +
            HahnField.addVal k ℚ (FH.coeff FH.natDegree) +
            FH.natDegree • (δ : WithTop ℚ) =
          0 := by
      rw [hγn]
      simpa [lam, FH] using
        HahnField.withTop_scaledValue_natDegree_eq_zero
          (Γ := ℚ) F.natDegree γn δ
    simpa [FH, coeff_mapPolynomialToHahnField] using hmain

theorem exists_natDegree_boundedCoeffKOddClusterHypotheses
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (Series k)} (hodd : Odd F.natDegree) :
    ∃ (nδ nlam : ℕ+) (δ lam : ℚ),
      ∃ (_hδ : HasDenominator nδ δ) (_hlam : HasDenominator nlam lam),
        BoundedCoeffKOddClusterHypotheses k
          (HahnField.scalePolynomial k ℚ (mapPolynomialToHahnField k F) δ lam)
          F.natDegree := by
  rcases exists_natDegree_scaling_conditions (k := k) (F := F) hodd with
    ⟨nδ, nlam, δ, lam, hδ, hlam, hintegral, hlower, hmain⟩
  refine ⟨nδ, nlam, δ, lam, hδ, hlam, ?_⟩
  exact boundedCoeffKOddClusterHypotheses_scale_mapPolynomialToHahnField
    (k := k) (F := F) hδ hlam
    (Nat.pos_of_ne_zero (by
      intro hzero
      exact Nat.not_odd_zero (hzero ▸ hodd)))
    hodd hintegral hlower hmain

theorem exists_positive_hahn_root_of_boundedCoeff_KOddCluster_of_odd_natDegree
    [LinearOrder k] [IsStrictOrderedRing k]
    (hCluster : BoundedCoeffKOddClusterRootHypothesis k)
    {F : Polynomial (Series k)} (hodd : Odd F.natDegree) :
    ScaledPositiveHahnRootWitness k F := by
  rcases exists_natDegree_boundedCoeffKOddClusterHypotheses (k := k) (F := F) hodd with
    ⟨nδ, nlam, δ, lam, hδ, hlam, hFH⟩
  refine ⟨nδ, nlam, δ, lam, hδ, hlam, ?_⟩
  exact BoundedCoeffKOddClusterRootHypothesis.exists_positive_hahn_root
    (k := k) hCluster hFH

end

end Puiseux

end HahnKaplanskyRealClosedness
