/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Support.RootWitnesses
import HahnKaplanskyRealClosedness.Puiseux.Valuation.Core
import HahnKaplanskyRealClosedness.Basic.ClusterProperty

/-!
# Puiseux bounded-coefficient cluster hypotheses

This file contains the bounded-coefficient Hahn cluster hypotheses and the lift from nonnegative
Hahn coefficients to the Hahn valuation subring. Valuation-subring root predicates and bridges
live in `Puiseux.ValuationCluster`. Root witness predicates live in `Puiseux.RootWitnesses`.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

/-- Puiseux-relevant odd-cluster hypothesis: the cluster theorem is only required for
Hahn-polynomials whose coefficients already have bounded-denominator support. -/
def BoundedCoeffKOddClusterRootHypothesis [LinearOrder k] [IsStrictOrderedRing k] : Prop :=
  ∀ {F : Polynomial (HahnField k ℚ)} {m : ℕ},
    0 < m → Odd m →
    (∀ i, HasBoundedDenominatorSupport k (F.coeff i)) →
    (∀ i, (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (F.coeff i)) →
    (∀ i, i < m → (0 : WithTop ℚ) < HahnField.addVal k ℚ (F.coeff i)) →
    HahnField.addVal k ℚ (F.coeff m) = 0 →
    ∃ y : HahnField k ℚ,
      (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
        HasBoundedDenominatorSupport k y ∧ F.IsRoot y

/-- All coefficients of a Hahn polynomial have bounded-denominator support. -/
def HasBoundedDenominatorSupportPolynomial (F : Polynomial (HahnField k ℚ)) : Prop :=
  ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i)

/-- Bundled side conditions for the bounded-coefficient `K[X]` odd-cluster statement. -/
abbrev BoundedCoeffKOddClusterHypotheses [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField k ℚ)) (m : ℕ) : Prop :=
  HahnField.KOddClusterHypothesesWithCoeffProperty k ℚ
    (fun x => HasBoundedDenominatorSupport k x) F m

theorem BoundedCoeffKOddClusterRootHypothesis.exists_positive_hahn_root
    [LinearOrder k] [IsStrictOrderedRing k]
    (hCluster : BoundedCoeffKOddClusterRootHypothesis k)
    {F : Polynomial (HahnField k ℚ)} {m : ℕ}
    (h : BoundedCoeffKOddClusterHypotheses k F m) :
    ∃ y : HahnField k ℚ,
      (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
        HasBoundedDenominatorSupport k y ∧ F.IsRoot y :=
  hCluster h.pos h.odd h.coeff h.nonneg h.lower h.main

noncomputable def valuationSubringPolynomialOfNonnegCoeffs
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField k ℚ))
    (hFnonneg : ∀ i : ℕ, (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (F.coeff i)) :
    Polynomial (HahnField.valuationSubring k ℚ) :=
  F.sum fun i _ =>
    Polynomial.C
      (⟨F.coeff i, (HahnField.mem_valuationSubring_iff k ℚ (F.coeff i)).mpr
        (hFnonneg i)⟩ : HahnField.valuationSubring k ℚ) * Polynomial.X ^ i

theorem map_valuationSubringPolynomialOfNonnegCoeffs
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField k ℚ))
    (hFnonneg : ∀ i : ℕ, (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (F.coeff i)) :
    (valuationSubringPolynomialOfNonnegCoeffs k F hFnonneg).map
      (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)) = F := by
  rw [valuationSubringPolynomialOfNonnegCoeffs, Polynomial.sum_def]
  rw [Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  exact Polynomial.sum_C_mul_X_pow_eq F

theorem coeff_valuationSubringPolynomialOfNonnegCoeffs
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField k ℚ))
    (hFnonneg : ∀ i : ℕ, (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (F.coeff i))
    (i : ℕ) :
    ((valuationSubringPolynomialOfNonnegCoeffs k F hFnonneg).coeff i :
        HahnField k ℚ) = F.coeff i := by
  have hmap := congrArg (fun P : Polynomial (HahnField k ℚ) => P.coeff i)
    (map_valuationSubringPolynomialOfNonnegCoeffs (k := k) F hFnonneg)
  simpa [Polynomial.coeff_map, Algebra.algebraMap_ofSubsemiring_apply] using hmap

end

end Puiseux

end HahnKaplanskyRealClosedness
