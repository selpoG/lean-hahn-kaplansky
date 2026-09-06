/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Support.Base

/-!
# Puiseux root witnesses

This file contains root-extraction predicates and odd-degree root hypotheses that do not
depend on the cluster-specific valuation-subring packaging.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

/-- A Hahn-field root with positive valuation and bounded-denominator support. -/
abbrev PositiveHahnRoot
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField k ℚ)) : Prop :=
  ∃ y : HahnField k ℚ,
    (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
      HasBoundedDenominatorSupport k y ∧ F.IsRoot y

/-- A Hahn-field root with bounded-denominator support, without a positivity side condition. -/
abbrev BoundedHahnRoot (F : Polynomial (HahnField k ℚ)) : Prop :=
  ∃ y : HahnField k ℚ, HasBoundedDenominatorSupport k y ∧ F.IsRoot y

theorem PositiveHahnRoot.boundedHahnRoot
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (HahnField k ℚ)}
    (hroot : PositiveHahnRoot k F) :
    BoundedHahnRoot k F := by
  rcases hroot with ⟨y, _hypos, hybd, hyroot⟩
  exact ⟨y, hybd, hyroot⟩

/-- A positive bounded Hahn-field root of the mapped polynomial gives a Puiseux root. -/
theorem isRoot_scalePolynomial_of_mapped_scalePolynomial_root_of_bounded_support
    (F : Polynomial (Series k)) {nδ nlam : ℕ+}
    {δ lam : ℚ} {hδ : HasDenominator nδ δ} {hlam : HasDenominator nlam lam}
    {y : HahnField k ℚ} (hy : HasBoundedDenominatorSupport k y)
    (hroot :
      (HahnField.scalePolynomial k ℚ (mapPolynomialToHahnField k F) δ lam).IsRoot y) :
    (scalePolynomial k F δ lam hδ hlam).IsRoot (ofHahnField k y hy) := by
  apply isRoot_of_mapped_root_of_bounded_support k
  rw [mapPolynomialToHahnField_scalePolynomial]
  exact hroot

theorem exists_root_of_exists_mapped_scalePolynomial_root_with_bounded_support
    (F : Polynomial (Series k)) {nδ nlam : ℕ+}
    {δ lam : ℚ} {hδ : HasDenominator nδ δ} {hlam : HasDenominator nlam lam}
    (hroot :
      BoundedHahnRoot k
        (HahnField.scalePolynomial k ℚ (mapPolynomialToHahnField k F) δ lam)) :
    ∃ x : Series k, F.IsRoot x := by
  rcases hroot with ⟨y, hy, hFy⟩
  exact exists_root_of_scalePolynomial_root (k := k) (F := F) (δ := δ) (lam := lam)
    (hδ := hδ) (hlam := hlam)
    ⟨ofHahnField k y hy,
      isRoot_scalePolynomial_of_mapped_scalePolynomial_root_of_bounded_support
        (k := k) (F := F) (hδ := hδ) (hlam := hlam) hy hFy⟩

/-- A scaled ambient Hahn-field root witness for a Puiseux polynomial. -/
def ScaledPositiveHahnRootWitness
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (Series k)) : Prop :=
  ∃ (nδ nlam : ℕ+) (δ lam : ℚ),
    ∃ (_hδ : HasDenominator nδ δ) (_hlam : HasDenominator nlam lam),
      PositiveHahnRoot k
        (HahnField.scalePolynomial k ℚ (mapPolynomialToHahnField k F) δ lam)

/-- A scaled ambient Hahn-field root witness for a Puiseux polynomial, using only
bounded-denominator support for the root. -/
def ScaledBoundedHahnRootWitness
    (F : Polynomial (Series k)) : Prop :=
  ∃ (nδ nlam : ℕ+) (δ lam : ℚ),
    ∃ (_hδ : HasDenominator nδ δ) (_hlam : HasDenominator nlam lam),
      BoundedHahnRoot k
        (HahnField.scalePolynomial k ℚ (mapPolynomialToHahnField k F) δ lam)

theorem ScaledPositiveHahnRootWitness.scaledBoundedHahnRootWitness
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (Series k)}
    (hroot : ScaledPositiveHahnRootWitness k F) :
    ScaledBoundedHahnRootWitness k F := by
  rcases hroot with ⟨nδ, nlam, δ, lam, hδ, hlam, hscaled⟩
  exact ⟨nδ, nlam, δ, lam, hδ, hlam, hscaled.boundedHahnRoot⟩

theorem exists_root_of_scaledBoundedHahnRootWitness
    {F : Polynomial (Series k)}
    (hroot : ScaledBoundedHahnRootWitness k F) :
    ∃ x : Series k, F.IsRoot x := by
  rcases hroot with ⟨nδ, nlam, δ, lam, hδ, hlam, hscaled⟩
  exact exists_root_of_exists_mapped_scalePolynomial_root_with_bounded_support
    (k := k) (F := F) (hδ := hδ) (hlam := hlam) hscaled

end

end Puiseux

end HahnKaplanskyRealClosedness
