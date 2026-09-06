/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Valuation.ClusterHypotheses

/-!
# Puiseux valuation-root predicates

This file contains valuation-subring root predicates and their basic accessors.  Cluster
hypotheses and bridges live in `Puiseux.ValuationCluster`.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

/-- A bundled bounded element of the Hahn valuation subring maximal ideal. This subtype is
useful when a recursive construction must remember the center together with its bounded-support
side conditions. -/
abbrev BoundedMaximalIdealElement
    [LinearOrder k] [IsStrictOrderedRing k] :=
  { y : HahnField.valuationSubring k ℚ //
    y ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) ∧
      HasBoundedDenominatorSupport k (y : HahnField k ℚ) }

namespace BoundedMaximalIdealElement

theorem mem
    [LinearOrder k] [IsStrictOrderedRing k]
    (y : BoundedMaximalIdealElement k) :
    (y : HahnField.valuationSubring k ℚ) ∈
      IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) :=
  y.property.1

/-- The zero center as a bundled bounded maximal-ideal element. -/
def zero
    [LinearOrder k] [IsStrictOrderedRing k] :
    BoundedMaximalIdealElement k :=
  ⟨0,
    Ideal.zero_mem (IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ)),
    by
      change HasBoundedDenominatorSupport k (0 : HahnField k ℚ)
      exact hasBoundedDenominatorSupport_zero k⟩

theorem coe_zero
    [LinearOrder k] [IsStrictOrderedRing k] :
    ((zero k : BoundedMaximalIdealElement k) : HahnField.valuationSubring k ℚ) = 0 :=
  rfl

end BoundedMaximalIdealElement

/-- An ambient Hahn-field root of a valuation-subring polynomial, with positive valuation and
bounded-denominator support. -/
abbrev PositiveHahnRootInMap
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField.valuationSubring k ℚ)) : Prop :=
  ∃ y : HahnField k ℚ,
    (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
      HasBoundedDenominatorSupport k y ∧
        (F.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).IsRoot y

/-- An ambient Hahn-field root of a valuation-subring polynomial with bounded-denominator
support, without the positive-valuation side condition. -/
abbrev BoundedHahnRootInMap
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField.valuationSubring k ℚ)) : Prop :=
  ∃ y : HahnField k ℚ,
    HasBoundedDenominatorSupport k y ∧
      (F.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).IsRoot y

theorem BoundedHahnRootInMap.of_root_valuationSubringPolynomialOfHahn
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (HahnField.valuationSubring k ℚ)}
    (hcoeff : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i : HahnField k ℚ))
    {a : valuationSubring k}
    (haroot : (valuationSubringPolynomialOfHahn k F hcoeff).IsRoot a) :
    BoundedHahnRootInMap k F := by
  refine ⟨(toHahnValuationSubring k a : HahnField k ℚ), ?_, ?_⟩
  · change HasBoundedDenominatorSupport k ((a : Series k) : HahnField k ℚ)
    exact hasBoundedDenominatorSupport_coe k (a : Series k)
  · have hrootF :
        F.IsRoot (toHahnValuationSubring k a) := by
      have hroot_map :
          ((valuationSubringPolynomialOfHahn k F hcoeff).map
            (toHahnValuationSubring k)).IsRoot (toHahnValuationSubring k a) :=
        Polynomial.IsRoot.map haroot
      simpa [map_valuationSubringPolynomialOfHahn] using hroot_map
    exact Polynomial.IsRoot.map hrootF

/-- A root in the Hahn valuation subring maximal ideal whose Hahn-field image has
bounded-denominator support. -/
def BoundedRootInMaximalIdeal
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField.valuationSubring k ℚ)) : Prop :=
  ∃ y : HahnField.valuationSubring k ℚ,
    y ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) ∧
      HasBoundedDenominatorSupport k (y : HahnField k ℚ) ∧ F.IsRoot y

theorem PositiveHahnRootInMap.boundedRootInMaximalIdeal
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (HahnField.valuationSubring k ℚ)}
    (hroot : PositiveHahnRootInMap k F) :
    BoundedRootInMaximalIdeal k F := by
  rcases hroot with ⟨y, hypos, hybd, hyroot⟩
  let yv : HahnField.valuationSubring k ℚ :=
    ⟨y, (HahnField.mem_valuationSubring_iff k ℚ y).mpr (le_of_lt hypos)⟩
  refine ⟨yv, ?_, hybd, ?_⟩
  · exact (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ yv).mpr (by
      simpa [yv] using hypos)
  · rw [Polynomial.IsRoot] at hyroot ⊢
    have hcoe : ((F.eval yv : HahnField.valuationSubring k ℚ) : HahnField k ℚ) = 0 := by
      calc
        ((F.eval yv : HahnField.valuationSubring k ℚ) : HahnField k ℚ) =
            (F.map (algebraMap (HahnField.valuationSubring k ℚ)
              (HahnField k ℚ))).eval (yv : HahnField k ℚ) := by
              exact (HahnField.eval_map_algebraMap_eq_coe_eval k ℚ F yv).symm
        _ = 0 := by
              simpa [yv] using hyroot
    exact Subtype.ext hcoe

theorem BoundedRootInMaximalIdeal.of_root_valuationSubringPolynomialOfHahn
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (HahnField.valuationSubring k ℚ)}
    (hcoeff : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i : HahnField k ℚ))
    {a : valuationSubring k}
    (hamem : a ∈ IsLocalRing.maximalIdeal (valuationSubring k))
    (haroot : (valuationSubringPolynomialOfHahn k F hcoeff).IsRoot a) :
    BoundedRootInMaximalIdeal k F := by
  refine ⟨toHahnValuationSubring k a, ?_, ?_, ?_⟩
  · exact (mem_maximalIdeal_iff_toHahnValuationSubring k a).mp hamem
  · change HasBoundedDenominatorSupport k ((a : Series k) : HahnField k ℚ)
    exact hasBoundedDenominatorSupport_coe k (a : Series k)
  · have hroot_map :
        ((valuationSubringPolynomialOfHahn k F hcoeff).map
          (toHahnValuationSubring k)).IsRoot (toHahnValuationSubring k a) :=
      Polynomial.IsRoot.map haroot
    simpa [map_valuationSubringPolynomialOfHahn] using hroot_map

theorem BoundedRootInMaximalIdeal.exists_positive_hahn_root
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (HahnField.valuationSubring k ℚ)}
    (hroot : BoundedRootInMaximalIdeal k F) :
    ∃ y : HahnField k ℚ,
      (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
        HasBoundedDenominatorSupport k y ∧
          (F.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).IsRoot y := by
  rcases hroot with ⟨y, hy_mem, hy_bd, hy_root⟩
  exact ⟨(y : HahnField k ℚ),
    (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ y).mp hy_mem,
    hy_bd, Polynomial.IsRoot.map hy_root⟩

end

end Puiseux

end HahnKaplanskyRealClosedness
