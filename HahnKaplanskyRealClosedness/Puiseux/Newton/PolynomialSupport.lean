/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Valuation.ClusterHypotheses
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Puiseux bounded polynomial support

This file contains bounded-support polynomial closure lemmas used by the root bridges.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

theorem hasBoundedDenominatorSupportPolynomial_C {x : HahnField k ℚ}
    (hx : HasBoundedDenominatorSupport k x) :
    HasBoundedDenominatorSupportPolynomial k (Polynomial.C x) := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [Polynomial.coeff_C_zero]
    exact hx
  · rw [Polynomial.coeff_C, if_neg hi]
    exact hasBoundedDenominatorSupport_zero k

theorem hasBoundedDenominatorSupportPolynomial_X :
    HasBoundedDenominatorSupportPolynomial k (Polynomial.X : Polynomial (HahnField k ℚ)) := by
  intro i
  by_cases hi : i = 1
  · subst i
    rw [Polynomial.coeff_X_one]
    exact hasBoundedDenominatorSupport_one k
  · rw [Polynomial.coeff_X, if_neg (fun h => hi h.symm)]
    exact hasBoundedDenominatorSupport_zero k

theorem hasBoundedDenominatorSupportPolynomial_add {F G : Polynomial (HahnField k ℚ)}
    (hF : HasBoundedDenominatorSupportPolynomial k F)
    (hG : HasBoundedDenominatorSupportPolynomial k G) :
    HasBoundedDenominatorSupportPolynomial k (F + G) := by
  intro i
  rw [Polynomial.coeff_add]
  exact hasBoundedDenominatorSupport_add k (hF i) (hG i)

theorem hasBoundedDenominatorSupportPolynomial_finset_sum {α : Type*}
    (s : Finset α) (F : α → Polynomial (HahnField k ℚ))
    (hF : ∀ a ∈ s, HasBoundedDenominatorSupportPolynomial k (F a)) :
    HasBoundedDenominatorSupportPolynomial k (∑ a ∈ s, F a) := by
  classical
  intro i
  rw [Polynomial.finsetSum_coeff]
  exact hasBoundedDenominatorSupport_finset_sum_of_boundedSupport k s
    (fun a => (F a).coeff i) (by
      intro a ha
      exact hF a ha i)

theorem hasBoundedDenominatorSupportPolynomial_mul {F G : Polynomial (HahnField k ℚ)}
    (hF : HasBoundedDenominatorSupportPolynomial k F)
    (hG : HasBoundedDenominatorSupportPolynomial k G) :
    HasBoundedDenominatorSupportPolynomial k (F * G) := by
  intro i
  rw [Polynomial.coeff_mul]
  exact hasBoundedDenominatorSupport_finset_sum_of_boundedSupport k
    (Finset.HasAntidiagonal.antidiagonal i)
    (fun p : ℕ × ℕ => F.coeff p.1 * G.coeff p.2) (by
      intro p _hp
      exact hasBoundedDenominatorSupport_mul k (hF p.1) (hG p.2))

theorem hasBoundedDenominatorSupportPolynomial_pow {F : Polynomial (HahnField k ℚ)}
    (hF : HasBoundedDenominatorSupportPolynomial k F) :
    ∀ m : ℕ, HasBoundedDenominatorSupportPolynomial k (F ^ m)
  | 0 => by
      simpa using hasBoundedDenominatorSupportPolynomial_C k
        (hasBoundedDenominatorSupport_one k)
  | m + 1 => by
      rw [pow_succ]
      exact hasBoundedDenominatorSupportPolynomial_mul k
        (hasBoundedDenominatorSupportPolynomial_pow hF m) hF

theorem hasBoundedDenominatorSupportPolynomial_sum
    (F : Polynomial (HahnField k ℚ))
    (hF : HasBoundedDenominatorSupportPolynomial k F)
    (G : ℕ → HahnField k ℚ → Polynomial (HahnField k ℚ))
    (hG : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i) →
      HasBoundedDenominatorSupportPolynomial k (G i (F.coeff i))) :
    HasBoundedDenominatorSupportPolynomial k (F.sum G) := by
  rw [Polynomial.sum_def]
  exact hasBoundedDenominatorSupportPolynomial_finset_sum k F.support
    (fun i => G i (F.coeff i)) (by
      intro i _hi
      exact hG i (hF i))

theorem hasBoundedDenominatorSupportPolynomial_comp_X_add_C
    {F : Polynomial (HahnField k ℚ)}
    (hF : HasBoundedDenominatorSupportPolynomial k F)
    {y : HahnField k ℚ} (hy : HasBoundedDenominatorSupport k y) :
    HasBoundedDenominatorSupportPolynomial k (F.comp (Polynomial.X + Polynomial.C y)) := by
  rw [Polynomial.comp_eq_sum_left]
  apply hasBoundedDenominatorSupportPolynomial_sum k F hF
  intro i hi
  exact hasBoundedDenominatorSupportPolynomial_mul k
    (hasBoundedDenominatorSupportPolynomial_C k hi)
    (hasBoundedDenominatorSupportPolynomial_pow k
      (hasBoundedDenominatorSupportPolynomial_add k
        (hasBoundedDenominatorSupportPolynomial_X k)
        (hasBoundedDenominatorSupportPolynomial_C k hy)) i)

theorem hasBoundedDenominatorSupportPolynomial_scale
    {F : Polynomial (HahnField k ℚ)} {nδ nlam : ℕ+}
    {δ lam : ℚ} (hF : HasBoundedDenominatorSupportPolynomial k F)
    (hδ : HasDenominator nδ δ) (hlam : HasDenominator nlam lam) :
    HasBoundedDenominatorSupportPolynomial k
      (HahnField.scalePolynomial k ℚ F δ lam) := by
  intro i
  rw [HahnField.coeff_scalePolynomial]
  exact hasBoundedDenominatorSupport_mul k
    (hasBoundedDenominatorSupport_mul k
      (hasBoundedDenominatorSupport_hahnMonomial k (hasDenominator_neg hlam))
      (hF i))
    (hasBoundedDenominatorSupport_pow k
      (hasBoundedDenominatorSupport_hahnMonomial k hδ) i)

theorem hasBoundedDenominatorSupportPolynomial_scale_mapPolynomialToHahnField
    (F : Polynomial (Series k)) {nδ nlam : ℕ+}
    {δ lam : ℚ} (hδ : HasDenominator nδ δ) (hlam : HasDenominator nlam lam) :
    HasBoundedDenominatorSupportPolynomial k
      (HahnField.scalePolynomial k ℚ (mapPolynomialToHahnField k F) δ lam) := by
  intro i
  rw [HahnField.coeff_scalePolynomial, coeff_mapPolynomialToHahnField]
  exact hasBoundedDenominatorSupport_mul k
    (hasBoundedDenominatorSupport_mul k
      (hasBoundedDenominatorSupport_hahnMonomial k (hasDenominator_neg hlam))
      (hasBoundedDenominatorSupport_coe k (F.coeff i)))
    (hasBoundedDenominatorSupport_pow k
      (hasBoundedDenominatorSupport_hahnMonomial k hδ) i)

theorem boundedCoeffKOddClusterHypotheses_scale_mapPolynomialToHahnField
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (Series k)} {m : ℕ} {nδ nlam : ℕ+} {δ lam : ℚ}
    (hδ : HasDenominator nδ δ) (hlam : HasDenominator nlam lam)
    (hmpos : 0 < m) (hmodd : Odd m)
    (hintegral : ∀ i,
      (0 : WithTop ℚ) ≤
        (-(lam : ℚ) : WithTop ℚ) + HahnField.addVal k ℚ (F.coeff i : HahnField k ℚ) +
          i • (δ : WithTop ℚ))
    (hlower : ∀ i, i < m →
      (0 : WithTop ℚ) <
        (-(lam : ℚ) : WithTop ℚ) + HahnField.addVal k ℚ (F.coeff i : HahnField k ℚ) +
          i • (δ : WithTop ℚ))
    (hmain :
      (-(lam : ℚ) : WithTop ℚ) + HahnField.addVal k ℚ (F.coeff m : HahnField k ℚ) +
          m • (δ : WithTop ℚ) =
        0) :
    BoundedCoeffKOddClusterHypotheses k
      (HahnField.scalePolynomial k ℚ (mapPolynomialToHahnField k F) δ lam) m := by
  refine ⟨hmpos, hmodd, ?_, ?_, ?_, ?_⟩
  · exact hasBoundedDenominatorSupportPolynomial_scale_mapPolynomialToHahnField
      k F hδ hlam
  · intro i
    simpa [HahnField.addVal_coeff_scalePolynomial, coeff_mapPolynomialToHahnField]
      using hintegral i
  · intro i hi
    simpa [HahnField.addVal_coeff_scalePolynomial, coeff_mapPolynomialToHahnField]
      using hlower i hi
  · simpa [HahnField.addVal_coeff_scalePolynomial, coeff_mapPolynomialToHahnField]
      using hmain

end

end Puiseux

end HahnKaplanskyRealClosedness
