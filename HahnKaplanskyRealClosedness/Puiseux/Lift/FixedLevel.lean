/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Valuation.Core

/-!
# Fixed-denominator Puiseux valuation levels

This file contains the valuation subrings attached to fixed-denominator Puiseux levels and
their constant-coefficient maps.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- The valuation-subring part of a fixed-denominator Puiseux level. -/
def fixedDenominatorValuationSubring (n : ℕ+) : Subring (Series k) where
  carrier :=
    {x | x ∈ valuationSubring k ∧
      (x : HahnField k ℚ) ∈ fixedDenominatorSubfield k n}
  zero_mem' := by
    exact ⟨zero_mem (valuationSubring k), zero_mem (fixedDenominatorSubfield k n)⟩
  one_mem' := by
    exact ⟨one_mem (valuationSubring k), one_mem (fixedDenominatorSubfield k n)⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  neg_mem' := by
    intro x hx
    exact ⟨neg_mem hx.1, neg_mem hx.2⟩

/-- The valuation subring on the `n`-th fixed-denominator level, obtained by restricting the
ambient Hahn valuation subring. -/
def fixedDenominatorLevelValuationSubring (n : ℕ+) :
    ValuationSubring (FixedDenominatorSeries k n) :=
  (HahnField.valuationSubringValuationSubring k ℚ).comap
    (fixedDenominatorSubfield k n).subtype

/-- The fixed-denominator valuation level used in the Puiseux union is the same local ring as
the valuation subring of the corresponding fixed-denominator field. -/
def fixedDenominatorValuationSubringEquiv (n : ℕ+) :
    fixedDenominatorValuationSubring k n ≃+* fixedDenominatorLevelValuationSubring k n where
  toFun x :=
    ⟨⟨(x : Series k), x.property.2⟩, by
      have hx : ((x : fixedDenominatorValuationSubring k n) : Series k) ∈ valuationSubring k :=
        x.property.1
      change ((x : Series k) : HahnField k ℚ) ∈
        HahnField.valuationSubringValuationSubring k ℚ
      exact hx⟩
  invFun x :=
    ⟨fixedDenominatorToSeries k n x.1, by
      constructor
      · change ((fixedDenominatorToSeries k n x.1 : Series k) : HahnField k ℚ) ∈
          HahnField.valuationSubringValuationSubring k ℚ
        exact x.property
      · exact x.1.property⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl
  map_add' x y := by
    ext
    rfl

instance instIsLocalRingFixedDenominatorValuationSubring (n : ℕ+) :
    IsLocalRing (fixedDenominatorValuationSubring k n) :=
  (fixedDenominatorValuationSubringEquiv k n).symm.isLocalRing

theorem fixedDenominatorValuationSubringEquiv_symm_map_maximalIdeal (n : ℕ+) :
    (IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n)).map
      (fixedDenominatorValuationSubringEquiv k n).symm =
        IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) :=
  IsLocalRing.map_ringEquiv_maximalIdeal (fixedDenominatorValuationSubringEquiv k n).symm

theorem fixedDenominatorValuationSubring_le_valuationSubring (n : ℕ+) :
    fixedDenominatorValuationSubring k n ≤ valuationSubring k := by
  intro x hx
  exact hx.1

theorem fixedDenominatorValuationSubring_le_mul_right (n n' : ℕ+) :
    fixedDenominatorValuationSubring k n ≤
      fixedDenominatorValuationSubring k (n * n') := by
  intro x hx
  exact ⟨hx.1, fixedDenominatorSubfield_le_mul_right k n n' hx.2⟩

/-- Include a fixed-denominator valuation level into a right ramified level. -/
def fixedDenominatorValuationSubringMapMulRight (n q : ℕ+) :
    fixedDenominatorValuationSubring k n →+*
      fixedDenominatorValuationSubring k (n * q) :=
  Subring.inclusion (fixedDenominatorValuationSubring_le_mul_right k n q)

@[simp]
theorem fixedDenominatorValuationSubringMapMulRight_apply {n q : ℕ+}
    (x : fixedDenominatorValuationSubring k n) :
    ((fixedDenominatorValuationSubringMapMulRight k n q x :
      fixedDenominatorValuationSubring k (n * q)) : Series k) = (x : Series k) :=
  rfl

/-- Include a fixed-denominator valuation level into the full Puiseux valuation subring. -/
def fixedDenominatorValuationToValuationSubring (n : ℕ+) :
    fixedDenominatorValuationSubring k n →+* valuationSubring k :=
  Subring.inclusion (fixedDenominatorValuationSubring_le_valuationSubring k n)

@[simp]
theorem fixedDenominatorValuationToValuationSubring_apply {n : ℕ+}
    (x : fixedDenominatorValuationSubring k n) :
    ((fixedDenominatorValuationToValuationSubring k n x : valuationSubring k) :
      Series k) = (x : Series k) :=
  rfl

/-- Include a fixed-denominator valuation level into the ambient Hahn valuation subring. -/
def fixedDenominatorValuationToHahnValuationSubring (n : ℕ+) :
    fixedDenominatorValuationSubring k n →+* HahnField.valuationSubring k ℚ :=
  (toHahnValuationSubring k).comp (fixedDenominatorValuationToValuationSubring k n)

@[simp]
theorem fixedDenominatorValuationToHahnValuationSubring_apply {n : ℕ+}
    (x : fixedDenominatorValuationSubring k n) :
    ((fixedDenominatorValuationToHahnValuationSubring k n x :
      HahnField.valuationSubring k ℚ) : HahnField k ℚ) = (x : Series k) :=
  rfl

@[simp]
theorem fixedDenominatorValuationToHahnValuationSubring_comp_mapMulRight {n q : ℕ+} :
    (fixedDenominatorValuationToHahnValuationSubring k (n * q)).comp
        (fixedDenominatorValuationSubringMapMulRight k n q) =
      fixedDenominatorValuationToHahnValuationSubring k n := by
  ext x
  rfl

/-- Constant coefficient on a fixed-denominator valuation level. -/
def fixedDenominatorConstantCoeffRingHom (n : ℕ+) :
    fixedDenominatorValuationSubring k n →+* k :=
  (constantCoeffRingHom k).comp (fixedDenominatorValuationToValuationSubring k n)

@[simp]
theorem fixedDenominatorConstantCoeffRingHom_mapMulRight {n q : ℕ+}
    (x : fixedDenominatorValuationSubring k n) :
    fixedDenominatorConstantCoeffRingHom k (n * q)
        (fixedDenominatorValuationSubringMapMulRight k n q x) =
      fixedDenominatorConstantCoeffRingHom k n x :=
  rfl

theorem fixedDenominatorConstantCoeffRingHom_surjective (n : ℕ+) :
    Function.Surjective (fixedDenominatorConstantCoeffRingHom k n) := by
  intro c
  let xH : HahnField k ℚ := HahnField.singleOfNonneg k ℚ 0 c le_rfl
  have hxden : HasDenominatorSupport k n xH :=
    hasDenominatorSupport_singleOfNonneg k c (hasDenominator_zero n) le_rfl
  let x : Series k := ofHahnField k xH ⟨n, hxden⟩
  have hxmem : x ∈ fixedDenominatorValuationSubring k n := by
    constructor
    · rw [mem_valuationSubring_iff]
      change (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ xH
      by_cases hc : c = 0
      · simp [xH, hc]
      · simp [xH, HahnField.addVal_apply, HahnField.singleOfNonneg_coe, hc]
    · change HasDenominatorSupport k n (x : HahnField k ℚ)
      change HasDenominatorSupport k n xH
      exact hxden
  refine ⟨⟨x, hxmem⟩, ?_⟩
  change constantCoeffRingHom k
      (fixedDenominatorValuationToValuationSubring k n
        (⟨x, hxmem⟩ : fixedDenominatorValuationSubring k n)) = c
  simp [x, xH]

theorem fixedDenominatorConstantCoeffRingHom_eq_zero_iff_pos_addVal {n : ℕ+}
    (x : fixedDenominatorValuationSubring k n) :
    fixedDenominatorConstantCoeffRingHom k n x = 0 ↔
      (0 : WithTop ℚ) < addVal k (x : Series k) := by
  change constantCoeffRingHom k
      (fixedDenominatorValuationToValuationSubring k n x) = 0 ↔
    (0 : WithTop ℚ) < addVal k
      ((fixedDenominatorValuationToValuationSubring k n x : valuationSubring k) : Series k)
  rw [constantCoeffRingHom_eq_zero_iff_pos_addVal]

/-- The maximal ideal of a fixed-denominator valuation level is the kernel of the constant
coefficient map. -/
theorem fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (n : ℕ+) :
    RingHom.ker (fixedDenominatorConstantCoeffRingHom k n) =
      IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) :=
  IsLocalRing.ker_eq_maximalIdeal (fixedDenominatorConstantCoeffRingHom k n)
    (fixedDenominatorConstantCoeffRingHom_surjective k n)

theorem mem_fixedDenominator_maximalIdeal_iff_pos_addVal {n : ℕ+}
    (x : fixedDenominatorValuationSubring k n) :
    x ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) ↔
      (0 : WithTop ℚ) < addVal k (x : Series k) := by
  rw [← fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) n,
    RingHom.mem_ker, fixedDenominatorConstantCoeffRingHom_eq_zero_iff_pos_addVal]

theorem fixedDenominatorValuationSubringMapMulRight_mem_maximalIdeal {n q : ℕ+}
    {x : fixedDenominatorValuationSubring k n}
    (hx : x ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n)) :
    fixedDenominatorValuationSubringMapMulRight k n q x ∈
      IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k (n * q)) := by
  rw [mem_fixedDenominator_maximalIdeal_iff_pos_addVal] at hx ⊢
  simpa using hx

theorem fixedDenominatorConstantCoeffRingHom_ne_zero_of_isUnit {n : ℕ+}
    {x : fixedDenominatorValuationSubring k n} (hx : IsUnit x) :
    fixedDenominatorConstantCoeffRingHom k n x ≠ 0 := by
  intro hzero
  have hxmem : x ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) := by
    rw [← fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) n,
      RingHom.mem_ker]
    exact hzero
  exact (IsLocalRing.maximalIdeal.isMaximal (fixedDenominatorValuationSubring k n)).ne_top
    ((IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n)).eq_top_of_isUnit_mem
      hxmem hx)

theorem fixedDenominator_isUnit_of_constantCoeffRingHom_ne_zero {n : ℕ+}
    (x : fixedDenominatorValuationSubring k n)
    (hx : fixedDenominatorConstantCoeffRingHom k n x ≠ 0) :
    IsUnit x := by
  by_contra hx_unit
  have hx_nonunit : x ∈ nonunits (fixedDenominatorValuationSubring k n) := by
    rwa [mem_nonunits_iff]
  have hxmem : x ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hx_nonunit
  rw [← fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) n,
    RingHom.mem_ker] at hxmem
  exact hx hxmem

theorem fixedDenominatorValuationSubringMapMulRight_isUnit {n q : ℕ+}
    {x : fixedDenominatorValuationSubring k n} (hx : IsUnit x) :
    IsUnit (fixedDenominatorValuationSubringMapMulRight k n q x) := by
  exact hx.map (fixedDenominatorValuationSubringMapMulRight k n q)

theorem Polynomial.IsRoot.map_fixedDenominatorValuationSubringMapMulRight {n q : ℕ+}
    {P : Polynomial (fixedDenominatorValuationSubring k n)}
    {x : fixedDenominatorValuationSubring k n}
    (hx : P.IsRoot x) :
    (P.map (fixedDenominatorValuationSubringMapMulRight k n q)).IsRoot
      (fixedDenominatorValuationSubringMapMulRight k n q x) :=
  Polynomial.IsRoot.map hx

/-- A finite family of Puiseux valuation-subring elements is contained in one
fixed-denominator valuation level. -/
theorem exists_fixedDenominatorValuationSubring_finset {α : Type*} (s : Finset α)
    (f : α → valuationSubring k) :
    ∃ n : ℕ+, ∀ a ∈ s,
      (f a : Series k) ∈ fixedDenominatorValuationSubring k n := by
  rcases exists_fixedDenominatorSubfield_finset k s (fun a => (f a : Series k)) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro a ha
  exact ⟨(f a).property, hn a ha⟩

/-- The coefficients of a Puiseux valuation-subring polynomial are contained in one
fixed-denominator valuation level. -/
theorem exists_fixedDenominatorValuationSubring_polynomial_coeff
    (P : Polynomial (valuationSubring k)) :
    ∃ n : ℕ+, ∀ i : ℕ,
      (P.coeff i : Series k) ∈ fixedDenominatorValuationSubring k n := by
  classical
  rcases exists_fixedDenominatorValuationSubring_finset k P.support P.coeff with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro i
  by_cases hi : i ∈ P.support
  · exact hn i hi
  · have hcoeff : P.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
    rw [hcoeff]
    exact zero_mem (fixedDenominatorValuationSubring k n)

end

end Puiseux

end HahnKaplanskyRealClosedness
