/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Support.FiniteLevel

/-!
# Valuation API for Puiseux series

This file starts the valuation-theoretic route for `Puiseux.Series k`.  The valuation is the
ambient rational Hahn valuation restricted along the inclusion into `HahnField k ℚ`.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- The natural additive valuation on Puiseux series, induced from the ambient rational Hahn
field. -/
def addVal : AddValuation (Series k) (WithTop ℚ) :=
  (HahnField.addVal k ℚ).comap (toHahnField k)

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem addVal_apply (x : Series k) :
    addVal k x = HahnField.addVal k ℚ (x : HahnField k ℚ) :=
  rfl

/-- The natural valuation on Puiseux series in multiplicative convention. -/
def valuation : Valuation (Series k) (Multiplicative (WithTop ℚ)ᵒᵈ) :=
  AddValuation.toValuation (addVal k)

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem valuation_apply (x : Series k) :
    valuation k x = Multiplicative.ofAdd (OrderDual.toDual (addVal k x)) :=
  rfl

/-- The valuation subring of Puiseux series, obtained by comapping the ambient Hahn valuation
subring along the inclusion `Puiseux.Series k → HahnField k ℚ`. -/
def valuationSubringValuationSubring : ValuationSubring (Series k) :=
  (HahnField.valuationSubringValuationSubring k ℚ).comap (toHahnField k)

/-- The Puiseux valuation subring as a `Subring`. -/
abbrev valuationSubring : Subring (Series k) :=
  (valuationSubringValuationSubring k).toSubring

@[simp]
theorem mem_valuationSubring_iff (x : Series k) :
    x ∈ valuationSubring k ↔ (0 : WithTop ℚ) ≤ addVal k x := by
  change (toHahnField k x) ∈ HahnField.valuationSubringValuationSubring k ℚ ↔
    (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (x : HahnField k ℚ)
  rw [HahnField.mem_valuationSubringValuationSubring,
    HahnField.mem_valuationSubring_iff]
  rfl

@[simp]
theorem valuationSubringValuationSubring_toSubring :
    (valuationSubringValuationSubring k).toSubring = valuationSubring k :=
  rfl

theorem valuation_valuationSubring_eq :
    (valuation k).valuationSubring = valuationSubringValuationSubring k := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  change valuation k x ≤ 1 ↔
    (toHahnField k x) ∈ HahnField.valuationSubringValuationSubring k ℚ
  rw [HahnField.mem_valuationSubringValuationSubring, HahnField.mem_valuationSubring_iff]
  change Multiplicative.ofAdd (OrderDual.toDual (addVal k x)) ≤
      Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℚ)) ↔
    (0 : WithTop ℚ) ≤ addVal k x
  rw [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]

instance instIsLocalRingValuationSubring : IsLocalRing (valuationSubring k) :=
  inferInstanceAs (IsLocalRing (valuationSubringValuationSubring k))

/-- The inclusion of the Puiseux valuation subring into the ambient Hahn valuation subring. -/
def toHahnValuationSubring :
    valuationSubring k →+* HahnField.valuationSubring k ℚ where
  toFun x :=
    ⟨(x : Series k), by
      have hx : ((x : valuationSubring k) : Series k) ∈ valuationSubring k := x.property
      rw [mem_valuationSubring_iff] at hx
      exact (HahnField.mem_valuationSubring_iff k ℚ _).mpr (by simpa using hx)⟩
  map_one' := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl
  map_zero' := by
    ext
    rfl
  map_add' x y := by
    ext
    rfl

@[simp]
theorem toHahnValuationSubring_apply (x : valuationSubring k) :
    ((toHahnValuationSubring k x : HahnField.valuationSubring k ℚ) : HahnField k ℚ) =
      (x : Series k) :=
  rfl

/-- Constant coefficient on the Puiseux valuation subring. -/
def constantCoeffRingHom : valuationSubring k →+* k :=
  (HahnField.constantCoeffRingHom k ℚ).comp (toHahnValuationSubring k)

@[simp]
theorem constantCoeffRingHom_apply (x : valuationSubring k) :
    constantCoeffRingHom k x =
      HahnField.constantCoeffRingHom k ℚ (toHahnValuationSubring k x) :=
  rfl

theorem constantCoeffRingHom_surjective :
    Function.Surjective (constantCoeffRingHom k) := by
  intro c
  let xH : HahnField k ℚ := HahnField.singleOfNonneg k ℚ 0 c le_rfl
  have hxbd : HasBoundedDenominatorSupport k xH :=
    hasBoundedDenominatorSupport_singleOfNonneg k c le_rfl
  let x : Series k := ofHahnField k xH hxbd
  have hxmem : x ∈ valuationSubring k := by
    rw [mem_valuationSubring_iff]
    change (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ xH
    by_cases hc : c = 0
    · simp [xH, hc]
    · simp [xH, HahnField.addVal_apply, HahnField.singleOfNonneg_coe, hc]
  refine ⟨⟨x, hxmem⟩, ?_⟩
  change HahnField.constantCoeffRingHom k ℚ
      (toHahnValuationSubring k (⟨x, hxmem⟩ : valuationSubring k)) = c
  simp [x, xH]

theorem constantCoeffRingHom_eq_zero_iff_pos_addVal (x : valuationSubring k) :
    constantCoeffRingHom k x = 0 ↔
      (0 : WithTop ℚ) < addVal k (x : Series k) := by
  change HahnField.constantCoeffRingHom k ℚ (toHahnValuationSubring k x) = 0 ↔
    (0 : WithTop ℚ) < HahnField.addVal k ℚ ((x : Series k) : HahnField k ℚ)
  rw [HahnField.constantCoeffRingHom_eq_zero_iff_pos_addVal]
  rfl

/-- The maximal ideal of the Puiseux valuation subring is the kernel of the constant coefficient
map. -/
theorem constantCoeffRingHom_ker_eq_maximalIdeal :
    RingHom.ker (constantCoeffRingHom k) =
      IsLocalRing.maximalIdeal (valuationSubring k) :=
  IsLocalRing.ker_eq_maximalIdeal (constantCoeffRingHom k)
    (constantCoeffRingHom_surjective k)

theorem constantCoeffRingHom_ne_zero_of_isUnit {x : valuationSubring k} (hx : IsUnit x) :
    constantCoeffRingHom k x ≠ 0 := by
  intro hzero
  have hxmem : x ∈ IsLocalRing.maximalIdeal (valuationSubring k) := by
    rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k), RingHom.mem_ker]
    exact hzero
  exact (IsLocalRing.maximalIdeal.isMaximal (valuationSubring k)).ne_top
    ((IsLocalRing.maximalIdeal (valuationSubring k)).eq_top_of_isUnit_mem hxmem hx)

theorem isUnit_of_constantCoeffRingHom_ne_zero (x : valuationSubring k)
    (hx : constantCoeffRingHom k x ≠ 0) :
    IsUnit x := by
  by_contra hx_unit
  have hx_nonunit : x ∈ nonunits (valuationSubring k) := by
    rwa [mem_nonunits_iff]
  have hxmem : x ∈ IsLocalRing.maximalIdeal (valuationSubring k) := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hx_nonunit
  rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k), RingHom.mem_ker] at hxmem
  exact hx hxmem

theorem mem_maximalIdeal_iff_pos_addVal (x : valuationSubring k) :
    x ∈ IsLocalRing.maximalIdeal (valuationSubring k) ↔
      (0 : WithTop ℚ) < addVal k (x : Series k) := by
  rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k), RingHom.mem_ker,
    constantCoeffRingHom_eq_zero_iff_pos_addVal]

theorem mem_maximalIdeal_iff_toHahnValuationSubring
    (x : valuationSubring k) :
    x ∈ IsLocalRing.maximalIdeal (valuationSubring k) ↔
      toHahnValuationSubring k x ∈
        IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) := by
  rw [mem_maximalIdeal_iff_pos_addVal,
    HahnField.mem_maximalIdeal_iff_pos_addVal]
  rfl

def ofHahnValuationSubring
    (x : HahnField.valuationSubring k ℚ)
    (hx : HasBoundedDenominatorSupport k (x : HahnField k ℚ)) :
    valuationSubring k :=
  ⟨ofHahnField k (x : HahnField k ℚ) hx, by
    rw [mem_valuationSubring_iff]
    change (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (x : HahnField k ℚ)
    exact (HahnField.mem_valuationSubring_iff k ℚ (x : HahnField k ℚ)).mp x.property⟩

@[simp]
theorem toHahnValuationSubring_ofHahnValuationSubring
    (x : HahnField.valuationSubring k ℚ)
    (hx : HasBoundedDenominatorSupport k (x : HahnField k ℚ)) :
    toHahnValuationSubring k (ofHahnValuationSubring k x hx) = x := by
  ext
  rfl

/-- A polynomial over the Puiseux valuation subring obtained by lifting bounded-support
coefficients of a Hahn valuation-subring polynomial. -/
noncomputable def valuationSubringPolynomialOfHahn
    (F : Polynomial (HahnField.valuationSubring k ℚ))
    (hcoeff : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i : HahnField k ℚ)) :
    Polynomial (valuationSubring k) :=
  ∑ i ∈ F.support,
    Polynomial.C (ofHahnValuationSubring k (F.coeff i) (hcoeff i)) * Polynomial.X ^ i

theorem map_valuationSubringPolynomialOfHahn
    (F : Polynomial (HahnField.valuationSubring k ℚ))
    (hcoeff : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i : HahnField k ℚ)) :
    (valuationSubringPolynomialOfHahn k F hcoeff).map (toHahnValuationSubring k) = F := by
  dsimp [valuationSubringPolynomialOfHahn]
  simp_rw [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    toHahnValuationSubring_ofHahnValuationSubring]
  simpa using (Polynomial.as_sum_support_C_mul_X_pow F).symm

theorem coeff_map_valuationSubringPolynomialOfHahn
    (F : Polynomial (HahnField.valuationSubring k ℚ))
    (hcoeff : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i : HahnField k ℚ))
    (i : ℕ) :
    toHahnValuationSubring k ((valuationSubringPolynomialOfHahn k F hcoeff).coeff i) =
      F.coeff i := by
  have hmap := congrArg
    (fun P : Polynomial (HahnField.valuationSubring k ℚ) => P.coeff i)
    (map_valuationSubringPolynomialOfHahn (k := k) F hcoeff)
  simpa [Polynomial.coeff_map] using hmap

theorem coeff_mem_maximalIdeal_valuationSubringPolynomialOfHahn
    {F : Polynomial (HahnField.valuationSubring k ℚ)}
    (hcoeff : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i : HahnField k ℚ))
    {i : ℕ}
    (hi : F.coeff i ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ)) :
    (valuationSubringPolynomialOfHahn k F hcoeff).coeff i ∈
      IsLocalRing.maximalIdeal (valuationSubring k) := by
  rw [mem_maximalIdeal_iff_toHahnValuationSubring,
    coeff_map_valuationSubringPolynomialOfHahn]
  exact hi

theorem isUnit_coeff_valuationSubringPolynomialOfHahn
    {F : Polynomial (HahnField.valuationSubring k ℚ)}
    (hcoeff : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i : HahnField k ℚ))
    {i : ℕ}
    (hunit : IsUnit (F.coeff i)) :
    IsUnit ((valuationSubringPolynomialOfHahn k F hcoeff).coeff i) := by
  have hcc_ne :
      constantCoeffRingHom k ((valuationSubringPolynomialOfHahn k F hcoeff).coeff i) ≠ 0 := by
    intro hzero
    have hcc_hahn :
        HahnField.constantCoeffRingHom k ℚ (F.coeff i) = 0 := by
      have hmap_zero :
          HahnField.constantCoeffRingHom k ℚ
            (toHahnValuationSubring k
              ((valuationSubringPolynomialOfHahn k F hcoeff).coeff i)) = 0 := by
        simpa [constantCoeffRingHom] using hzero
      rwa [coeff_map_valuationSubringPolynomialOfHahn] at hmap_zero
    exact HahnField.constantCoeffRingHom_ne_zero_of_isUnit k ℚ hunit hcc_hahn
  exact isUnit_of_constantCoeffRingHom_ne_zero k
    ((valuationSubringPolynomialOfHahn k F hcoeff).coeff i) hcc_ne

/-- The quotient of the Puiseux valuation subring by the kernel of the constant coefficient map is
canonically isomorphic to the coefficient field. -/
def residueEquiv :
    (valuationSubring k ⧸ RingHom.ker (constantCoeffRingHom k)) ≃+* k :=
  RingHom.quotientKerEquivOfSurjective (constantCoeffRingHom_surjective k)

@[simp]
theorem residueEquiv_mk (x : valuationSubring k) :
    residueEquiv k (Ideal.Quotient.mk (RingHom.ker (constantCoeffRingHom k)) x) =
      constantCoeffRingHom k x :=
  RingHom.quotientKerEquivOfSurjective_apply_mk
    (constantCoeffRingHom_surjective k) x

/-- The mathlib residue field of the Puiseux valuation subring is the coefficient field. -/
def residueFieldEquiv :
    IsLocalRing.ResidueField (valuationSubring k) ≃+* k :=
  (Ideal.quotEquivOfEq
    (constantCoeffRingHom_ker_eq_maximalIdeal (k := k)).symm).trans
      (residueEquiv k)

@[simp]
theorem residueFieldEquiv_residue (x : valuationSubring k) :
    residueFieldEquiv k (IsLocalRing.residue (valuationSubring k) x) =
      constantCoeffRingHom k x := by
  change
    residueEquiv k
      (Ideal.quotEquivOfEq
        (constantCoeffRingHom_ker_eq_maximalIdeal (k := k)).symm
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (valuationSubring k)) x)) =
        constantCoeffRingHom k x
  rw [Ideal.quotEquivOfEq_mk, residueEquiv_mk]

end

end Puiseux

end HahnKaplanskyRealClosedness
