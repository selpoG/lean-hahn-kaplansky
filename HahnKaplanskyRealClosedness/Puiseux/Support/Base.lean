/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Support.Core

/-!
# Puiseux series inside the rational Hahn field

This file defines the Puiseux subfield of the rational Hahn field and the polynomial/root
bridges built on top of bounded-denominator support.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

/-- The subring of `HahnField k ℚ` consisting of series with bounded-denominator support. -/
def subring : Subring (HahnField k ℚ) where
  carrier := {x | HasBoundedDenominatorSupport k x}
  zero_mem' := hasBoundedDenominatorSupport_zero k
  one_mem' := hasBoundedDenominatorSupport_one k
  add_mem' := by
    intro x y hx hy
    exact hasBoundedDenominatorSupport_add k hx hy
  mul_mem' := by
    intro x y hx hy
    exact hasBoundedDenominatorSupport_mul k hx hy
  neg_mem' := by
    intro x hx
    exact hasBoundedDenominatorSupport_neg k hx

/-- The subfield of `HahnField k ℚ` consisting of series with bounded-denominator support. -/
def subfield : Subfield (HahnField k ℚ) where
  __ := subring k
  inv_mem' := by
    intro x hx
    exact hasBoundedDenominatorSupport_inv k hx

/-- The Puiseux series over `k`, represented as the bounded-denominator subfield of
`HahnField k ℚ`. -/
abbrev Series :=
  subfield k

@[ext]
theorem ext {x y : Series k} (h : (x : HahnField k ℚ) = y) : x = y :=
  Subtype.ext h

theorem hasBoundedDenominatorSupport_coe (x : Series k) :
    HasBoundedDenominatorSupport k (x : HahnField k ℚ) :=
  x.2

/-- Regard a Hahn-field element with bounded-denominator support as a Puiseux series. -/
def ofHahnField (x : HahnField k ℚ) (hx : HasBoundedDenominatorSupport k x) : Series k :=
  ⟨x, show x ∈ subfield k from hx⟩

@[simp]
theorem coe_ofHahnField (x : HahnField k ℚ) (hx : HasBoundedDenominatorSupport k x) :
    (ofHahnField k x hx : HahnField k ℚ) = x :=
  rfl

/-- The inclusion of Puiseux series into the ambient rational Hahn field. -/
def toHahnField : Series k →+* HahnField k ℚ :=
  (subfield k).subtype

@[simp]
theorem toHahnField_apply (x : Series k) :
    toHahnField k x = (x : HahnField k ℚ) :=
  rfl

@[simp]
theorem coe_zero : ((0 : Series k) : HahnField k ℚ) = 0 :=
  rfl

@[simp]
theorem coe_neg (x : Series k) :
    ((-x : Series k) : HahnField k ℚ) = -(x : HahnField k ℚ) :=
  rfl

@[simp]
theorem coe_add (x y : Series k) :
    ((x + y : Series k) : HahnField k ℚ) =
      (x : HahnField k ℚ) + (y : HahnField k ℚ) :=
  rfl

@[simp]
theorem coe_pow (x : Series k) (m : ℕ) :
    ((x ^ m : Series k) : HahnField k ℚ) = (x : HahnField k ℚ) ^ m :=
  rfl

/-- A Hahn monomial whose rational exponent has denominator `n`, regarded as a Puiseux series. -/
def monomial {n : ℕ+} (γ : ℚ) (hγ : HasDenominator n γ) : Series k :=
  ⟨HahnField.hahnMonomial k ℚ γ,
    show HahnField.hahnMonomial k ℚ γ ∈ subfield k from
      hasBoundedDenominatorSupport_hahnMonomial k hγ⟩

@[simp]
theorem coe_monomial {n : ℕ+} (γ : ℚ) (hγ : HasDenominator n γ) :
    (monomial k γ hγ : HahnField k ℚ) = HahnField.hahnMonomial k ℚ γ :=
  rfl

@[simp]
theorem monomial_ne_zero {n : ℕ+} (γ : ℚ) (hγ : HasDenominator n γ) :
    monomial k γ hγ ≠ 0 := by
  intro h
  have hcoe := congrArg (fun x : Series k => (x : HahnField k ℚ)) h
  exact HahnSeries.single_ne_zero (a := γ) (r := (1 : k)) one_ne_zero (by
    simpa using congrArg ofLex hcoe)

/-- Puiseux-polynomial normalization matching `HahnField.scalePolynomial`: replace `X` by
`t^δ X` and multiply by `t^(-lam)`. -/
noncomputable def scalePolynomial (F : Polynomial (Series k)) {nδ nlam : ℕ+}
    (δ lam : ℚ) (hδ : HasDenominator nδ δ) (hlam : HasDenominator nlam lam) :
    Polynomial (Series k) :=
  Polynomial.C (monomial k (-lam) (hasDenominator_neg hlam)) *
    F.comp (Polynomial.C (monomial k δ hδ) * Polynomial.X)

@[simp]
theorem eval_scalePolynomial (F : Polynomial (Series k)) {nδ nlam : ℕ+}
    (δ lam : ℚ) (hδ : HasDenominator nδ δ) (hlam : HasDenominator nlam lam)
    (y : Series k) :
    (scalePolynomial k F δ lam hδ hlam).eval y =
      monomial k (-lam) (hasDenominator_neg hlam) *
        F.eval (monomial k δ hδ * y) := by
  simp [scalePolynomial, Polynomial.eval_comp]

@[simp]
theorem coeff_scalePolynomial (F : Polynomial (Series k)) {nδ nlam : ℕ+}
    (δ lam : ℚ) (hδ : HasDenominator nδ δ) (hlam : HasDenominator nlam lam)
    (i : ℕ) :
    (scalePolynomial k F δ lam hδ hlam).coeff i =
      monomial k (-lam) (hasDenominator_neg hlam) * F.coeff i *
        (monomial k δ hδ) ^ i := by
  rw [scalePolynomial, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  ring

theorem isRoot_of_scalePolynomial_isRoot {F : Polynomial (Series k)} {nδ nlam : ℕ+}
    {δ lam : ℚ} {hδ : HasDenominator nδ δ} {hlam : HasDenominator nlam lam}
    {y : Series k} (hy : (scalePolynomial k F δ lam hδ hlam).IsRoot y) :
    F.IsRoot (monomial k δ hδ * y) := by
  rw [Polynomial.IsRoot, eval_scalePolynomial] at hy
  exact (mul_eq_zero.mp hy).resolve_left (monomial_ne_zero k (-lam) (hasDenominator_neg hlam))

/-- Existential root transport for Puiseux polynomial normalization. -/
theorem exists_root_of_scalePolynomial_root {F : Polynomial (Series k)} {nδ nlam : ℕ+}
    {δ lam : ℚ} {hδ : HasDenominator nδ δ} {hlam : HasDenominator nlam lam}
    (hroot : ∃ y : Series k, (scalePolynomial k F δ lam hδ hlam).IsRoot y) :
    ∃ x : Series k, F.IsRoot x := by
  rcases hroot with ⟨y, hy⟩
  exact ⟨monomial k δ hδ * y, isRoot_of_scalePolynomial_isRoot k hy⟩

/-- Map a Puiseux-polynomial to the ambient Hahn field. -/
def mapPolynomialToHahnField : Polynomial (Series k) →+* Polynomial (HahnField k ℚ) :=
  Polynomial.mapRingHom (toHahnField k)

@[simp]
theorem mapPolynomialToHahnField_apply (P : Polynomial (Series k)) :
    mapPolynomialToHahnField k P = P.map (toHahnField k) :=
  rfl

@[simp]
theorem coeff_mapPolynomialToHahnField (P : Polynomial (Series k)) (i : ℕ) :
    (mapPolynomialToHahnField k P).coeff i = (P.coeff i : HahnField k ℚ) := by
  rw [mapPolynomialToHahnField_apply, Polynomial.coeff_map]
  rfl

theorem mapPolynomialToHahnField_scalePolynomial (F : Polynomial (Series k)) {nδ nlam : ℕ+}
    (δ lam : ℚ) (hδ : HasDenominator nδ δ) (hlam : HasDenominator nlam lam) :
    mapPolynomialToHahnField k (scalePolynomial k F δ lam hδ hlam) =
      HahnField.scalePolynomial k ℚ (mapPolynomialToHahnField k F) δ lam := by
  ext i
  rw [coeff_mapPolynomialToHahnField, HahnField.coeff_scalePolynomial, coeff_scalePolynomial,
    coeff_mapPolynomialToHahnField]
  simp [mul_assoc]

theorem eval_mapPolynomialToHahnField (P : Polynomial (Series k)) (x : Series k) :
    (mapPolynomialToHahnField k P).eval (x : HahnField k ℚ) =
      ((P.eval x : Series k) : HahnField k ℚ) := by
  rw [mapPolynomialToHahnField_apply]
  change (P.map (toHahnField k)).eval (toHahnField k x) = toHahnField k (P.eval x)
  exact Polynomial.eval_map_apply (p := P) (f := toHahnField k) (x := x)

theorem isRoot_mapPolynomialToHahnField_iff (P : Polynomial (Series k)) (x : Series k) :
    (mapPolynomialToHahnField k P).IsRoot (x : HahnField k ℚ) ↔ P.IsRoot x := by
  rw [Polynomial.IsRoot, Polynomial.IsRoot, eval_mapPolynomialToHahnField]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg (toHahnField k) h

/-- A bounded-denominator Hahn-field root of the mapped polynomial gives a Puiseux root. -/
theorem isRoot_of_mapped_root_of_bounded_support
    (P : Polynomial (Series k)) {x : HahnField k ℚ}
    (hx : HasBoundedDenominatorSupport k x)
    (hroot : (mapPolynomialToHahnField k P).IsRoot x) :
    P.IsRoot (ofHahnField k x hx) := by
  rw [← isRoot_mapPolynomialToHahnField_iff k P (ofHahnField k x hx)]
  simpa using hroot

end

end Puiseux

end HahnKaplanskyRealClosedness
