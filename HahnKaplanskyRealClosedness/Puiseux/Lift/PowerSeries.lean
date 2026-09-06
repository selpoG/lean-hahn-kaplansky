/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import Mathlib.RingTheory.HahnSeries.PowerSeries
import HahnKaplanskyRealClosedness.Puiseux.Lift.Adic

/-!
# Power series maps into fixed Puiseux valuation levels

This file starts the explicit construction of the fixed-level equivalence between `k⟦X⟧` and
the valuation subring of the Puiseux level with denominator `n`.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

open scoped PowerSeries

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

def fixedDenominatorNatCastAddMonoidHom (n : ℕ+) : ℕ →+ ℚ where
  toFun i := (i : ℚ) / (n : ℚ)
  map_zero' := by simp
  map_add' i j := by
    field_simp
    exact Nat.cast_add i j

@[simp]
theorem fixedDenominatorNatCastAddMonoidHom_apply (n : ℕ+) (i : ℕ) :
    fixedDenominatorNatCastAddMonoidHom n i = (i : ℚ) / (n : ℚ) :=
  rfl

theorem fixedDenominatorNatCastAddMonoidHom_injective (n : ℕ+) :
    Function.Injective (fixedDenominatorNatCastAddMonoidHom n) := by
  intro i j hij
  change (i : ℚ) / (n : ℚ) = (j : ℚ) / (n : ℚ) at hij
  apply Nat.cast_injective (R := ℚ)
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast n.ne_zero
  field_simp [hn] at hij
  exact hij

theorem fixedDenominatorNatCastAddMonoidHom_le_iff (n : ℕ+) (i j : ℕ) :
    fixedDenominatorNatCastAddMonoidHom n i ≤ fixedDenominatorNatCastAddMonoidHom n j ↔
      i ≤ j := by
  have hnpos : (0 : ℚ) < n := by exact_mod_cast n.pos
  rw [fixedDenominatorNatCastAddMonoidHom_apply,
    fixedDenominatorNatCastAddMonoidHom_apply, div_le_div_iff_of_pos_right hnpos,
    Nat.cast_le]

theorem exists_nat_div_of_hasDenominator_nonneg {n : ℕ+} {q : ℚ}
    (hq : HasDenominator n q) (hq_nonneg : 0 ≤ q) :
    ∃ i : ℕ, q = (i : ℚ) / (n : ℚ) := by
  rcases hq with ⟨m, rfl⟩
  have hnpos : (0 : ℚ) < n := by exact_mod_cast n.pos
  have hm_nonneg_rat : (0 : ℚ) ≤ (m : ℚ) := by
    have hmul : 0 ≤ ((m : ℚ) / (n : ℚ)) * (n : ℚ) :=
      mul_nonneg hq_nonneg hnpos.le
    field_simp [hnpos.ne'] at hmul
    exact hmul
  have hm_nonneg : 0 ≤ m := by exact_mod_cast hm_nonneg_rat
  refine ⟨m.toNat, ?_⟩
  have hm_cast : ((m.toNat : ℕ) : ℚ) = (m : ℚ) := by
    exact_mod_cast (Int.toNat_of_nonneg hm_nonneg)
  rw [hm_cast]

theorem mem_range_fixedDenominatorNatCastAddMonoidHom_iff {n : ℕ+} {q : ℚ} :
    q ∈ Set.range (fixedDenominatorNatCastAddMonoidHom n) ↔
      HasDenominator n q ∧ 0 ≤ q := by
  constructor
  · rintro ⟨i, rfl⟩
    constructor
    · exact ⟨i, by simp [fixedDenominatorNatCastAddMonoidHom_apply]⟩
    · exact div_nonneg (by exact_mod_cast Nat.zero_le i) (by exact_mod_cast n.pos.le)
  · rintro ⟨hq, hq_nonneg⟩
    rcases exists_nat_div_of_hasDenominator_nonneg hq hq_nonneg with ⟨i, rfl⟩
    exact ⟨i, by simp [fixedDenominatorNatCastAddMonoidHom_apply]⟩

def fixedDenominatorNatOrderEmbedding (n : ℕ+) : ℕ ↪o ℚ where
  toFun := fixedDenominatorNatCastAddMonoidHom n
  inj' := fixedDenominatorNatCastAddMonoidHom_injective n
  map_rel_iff' := fun {i j} => fixedDenominatorNatCastAddMonoidHom_le_iff n i j

def powerSeriesToFixedDenominatorHahnSeries (n : ℕ+) :
    k⟦X⟧ →+* HahnSeries ℚ k :=
  (HahnSeries.embDomainRingHom
    (fixedDenominatorNatCastAddMonoidHom n)
    (fixedDenominatorNatCastAddMonoidHom_injective n)
    (fixedDenominatorNatCastAddMonoidHom_le_iff n)).comp
      (RingEquiv.toRingHom HahnSeries.toPowerSeries.symm)

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem powerSeriesToFixedDenominatorHahnSeries_coeff (n : ℕ+) (f : k⟦X⟧) (i : ℕ) :
    (powerSeriesToFixedDenominatorHahnSeries k n f).coeff ((i : ℚ) / (n : ℚ)) =
      PowerSeries.coeff i f := by
  change
    (HahnSeries.embDomain (fixedDenominatorNatOrderEmbedding n)
      (HahnSeries.toPowerSeries.symm f)).coeff
      (fixedDenominatorNatOrderEmbedding n i) =
      PowerSeries.coeff i f
  rw [HahnSeries.embDomain_coeff]
  rfl

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem powerSeriesToFixedDenominatorHahnSeries_coeff_of_not_mem_range
    (n : ℕ+) (f : k⟦X⟧) {q : ℚ}
    (hq : q ∉ Set.range (fixedDenominatorNatCastAddMonoidHom n)) :
    (powerSeriesToFixedDenominatorHahnSeries k n f).coeff q = 0 := by
  change
    (HahnSeries.embDomain (fixedDenominatorNatOrderEmbedding n)
      (HahnSeries.toPowerSeries.symm f)).coeff q = 0
  exact HahnSeries.embDomain_of_notMem_range hq

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem hasDenominatorSupport_powerSeriesToFixedDenominatorHahnSeries (n : ℕ+) (f : k⟦X⟧) :
    HasDenominatorSupport k n
      (toLex (powerSeriesToFixedDenominatorHahnSeries k n f) : HahnField k ℚ) := by
  intro q hq
  change q ∈ (powerSeriesToFixedDenominatorHahnSeries k n f).support at hq
  rcases HahnSeries.support_embDomain_subset hq with ⟨i, _hi, rfl⟩
  exact ⟨i, by simp [fixedDenominatorNatCastAddMonoidHom_apply]⟩

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem orderTop_powerSeriesToFixedDenominatorHahnSeries_nonneg (n : ℕ+) (f : k⟦X⟧) :
    (0 : WithTop ℚ) ≤ (powerSeriesToFixedDenominatorHahnSeries k n f).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro q hq
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨i, rfl⟩
  have hi_nonneg : (0 : ℚ) ≤ (fixedDenominatorNatCastAddMonoidHom n i) := by
    exact div_nonneg (by exact_mod_cast Nat.zero_le i) (by exact_mod_cast n.pos.le)
  exact not_lt_of_ge hi_nonneg (by simpa using hq)

def powerSeriesToFixedDenominatorLevelValuationSubring (n : ℕ+) :
    k⟦X⟧ →+* fixedDenominatorLevelValuationSubring k n where
  toFun f :=
    ⟨⟨toLex (powerSeriesToFixedDenominatorHahnSeries k n f),
        hasDenominatorSupport_powerSeriesToFixedDenominatorHahnSeries k n f⟩, by
      change (toLex (powerSeriesToFixedDenominatorHahnSeries k n f) : HahnField k ℚ) ∈
        HahnField.valuationSubringValuationSubring k ℚ
      rw [HahnField.mem_valuationSubringValuationSubring, HahnField.mem_valuationSubring_iff]
      change (0 : WithTop ℚ) ≤ (powerSeriesToFixedDenominatorHahnSeries k n f).orderTop
      exact orderTop_powerSeriesToFixedDenominatorHahnSeries_nonneg k n f⟩
  map_one' := by
    ext
    change toLex (powerSeriesToFixedDenominatorHahnSeries k n 1) =
      (1 : HahnField k ℚ)
    rw [map_one]
    rfl
  map_mul' f g := by
    ext
    change toLex (powerSeriesToFixedDenominatorHahnSeries k n (f * g)) =
      toLex (powerSeriesToFixedDenominatorHahnSeries k n f) *
        toLex (powerSeriesToFixedDenominatorHahnSeries k n g)
    rw [map_mul]
    rfl
  map_zero' := by
    ext
    change toLex (powerSeriesToFixedDenominatorHahnSeries k n 0) = (0 : HahnField k ℚ)
    rw [map_zero]
    rfl
  map_add' f g := by
    ext
    change toLex (powerSeriesToFixedDenominatorHahnSeries k n (f + g)) =
      toLex (powerSeriesToFixedDenominatorHahnSeries k n f) +
        toLex (powerSeriesToFixedDenominatorHahnSeries k n g)
    rw [map_add]
    rfl

def fixedDenominatorLevelValuationSubringToPowerSeries (n : ℕ+) :
    fixedDenominatorLevelValuationSubring k n → k⟦X⟧ :=
  fun x =>
    PowerSeries.mk fun i =>
      (ofLex (((x : FixedDenominatorSeries k n) : HahnField k ℚ))).coeff
        ((i : ℚ) / (n : ℚ))

theorem fixedDenominatorLevelValuationSubringToPowerSeries_coeff
    (n : ℕ+) (x : fixedDenominatorLevelValuationSubring k n) (i : ℕ) :
    PowerSeries.coeff i (fixedDenominatorLevelValuationSubringToPowerSeries k n x) =
      (ofLex (((x : FixedDenominatorSeries k n) : HahnField k ℚ))).coeff
        ((i : ℚ) / (n : ℚ)) :=
  PowerSeries.coeff_mk i _

theorem fixedDenominatorLevelValuationSubringToPowerSeries_left_inv
    (n : ℕ+) (f : k⟦X⟧) :
    fixedDenominatorLevelValuationSubringToPowerSeries k n
        (powerSeriesToFixedDenominatorLevelValuationSubring k n f) = f := by
  ext i
  rw [fixedDenominatorLevelValuationSubringToPowerSeries_coeff]
  change
    (powerSeriesToFixedDenominatorHahnSeries k n f).coeff ((i : ℚ) / (n : ℚ)) =
      PowerSeries.coeff i f
  exact powerSeriesToFixedDenominatorHahnSeries_coeff k n f i

theorem fixedDenominatorLevelValuationSubring_coeff_eq_zero_of_not_mem_range
    (n : ℕ+) (x : fixedDenominatorLevelValuationSubring k n) {q : ℚ}
    (hq : q ∉ Set.range (fixedDenominatorNatCastAddMonoidHom n)) :
    (ofLex (((x : FixedDenominatorSeries k n) : HahnField k ℚ))).coeff q = 0 := by
  by_contra hcoeff
  have hq_support :
      q ∈ (ofLex (((x : FixedDenominatorSeries k n) : HahnField k ℚ))).support :=
    (HahnSeries.mem_support _ _).2 hcoeff
  have hq_den : HasDenominator n q :=
    (x : FixedDenominatorSeries k n).property q hq_support
  have hx_order :
      (0 : WithTop ℚ) ≤
        (ofLex (((x : FixedDenominatorSeries k n) : HahnField k ℚ))).orderTop := by
    have hxmem := x.property
    change (((x : FixedDenominatorSeries k n) : HahnField k ℚ) ∈
      HahnField.valuationSubringValuationSubring k ℚ) at hxmem
    rw [HahnField.mem_valuationSubringValuationSubring, HahnField.mem_valuationSubring_iff]
      at hxmem
    exact hxmem
  have hq_nonneg : 0 ≤ q := by
    have hq_order :
        (ofLex (((x : FixedDenominatorSeries k n) : HahnField k ℚ))).orderTop ≤
          (q : WithTop ℚ) :=
      HahnSeries.orderTop_le_of_coeff_ne_zero hcoeff
    exact WithTop.coe_le_coe.mp (le_trans hx_order hq_order)
  exact hq (mem_range_fixedDenominatorNatCastAddMonoidHom_iff.mpr ⟨hq_den, hq_nonneg⟩)

theorem powerSeriesToFixedDenominatorLevelValuationSubring_right_inv
    (n : ℕ+) (x : fixedDenominatorLevelValuationSubring k n) :
    powerSeriesToFixedDenominatorLevelValuationSubring k n
      (fixedDenominatorLevelValuationSubringToPowerSeries k n x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply ofLex.injective
  ext q
  change
    (powerSeriesToFixedDenominatorHahnSeries k n
      (fixedDenominatorLevelValuationSubringToPowerSeries k n x)).coeff q =
        (ofLex (((x : FixedDenominatorSeries k n) : HahnField k ℚ))).coeff q
  by_cases hq : q ∈ Set.range (fixedDenominatorNatCastAddMonoidHom n)
  · rcases hq with ⟨i, rfl⟩
    change
      (powerSeriesToFixedDenominatorHahnSeries k n
        (fixedDenominatorLevelValuationSubringToPowerSeries k n x)).coeff
          ((i : ℚ) / (n : ℚ)) =
        (ofLex (((x : FixedDenominatorSeries k n) : HahnField k ℚ))).coeff
          ((i : ℚ) / (n : ℚ))
    rw [powerSeriesToFixedDenominatorHahnSeries_coeff,
      fixedDenominatorLevelValuationSubringToPowerSeries_coeff]
  · rw [powerSeriesToFixedDenominatorHahnSeries_coeff_of_not_mem_range k n
      (fixedDenominatorLevelValuationSubringToPowerSeries k n x) hq,
      fixedDenominatorLevelValuationSubring_coeff_eq_zero_of_not_mem_range k n x hq]

def powerSeriesFixedDenominatorLevelValuationSubringEquiv (n : ℕ+) :
    k⟦X⟧ ≃+* fixedDenominatorLevelValuationSubring k n where
  toFun := powerSeriesToFixedDenominatorLevelValuationSubring k n
  invFun := fixedDenominatorLevelValuationSubringToPowerSeries k n
  left_inv := fixedDenominatorLevelValuationSubringToPowerSeries_left_inv k n
  right_inv := powerSeriesToFixedDenominatorLevelValuationSubring_right_inv k n
  map_mul' := (powerSeriesToFixedDenominatorLevelValuationSubring k n).map_mul
  map_add' := (powerSeriesToFixedDenominatorLevelValuationSubring k n).map_add

/-- Reindexing by `i ↦ i / n` identifies power series directly with the fixed-denominator
valuation subring used in the Puiseux union. -/
def powerSeriesFixedDenominatorValuationSubringEquiv (n : ℕ+) :
    k⟦X⟧ ≃+* fixedDenominatorValuationSubring k n :=
  (powerSeriesFixedDenominatorLevelValuationSubringEquiv k n).trans
    (fixedDenominatorValuationSubringEquiv k n).symm

theorem powerSeriesFixedDenominatorValuationSubringEquiv_map_maximalIdeal
    (n : ℕ+) :
    (IsLocalRing.maximalIdeal k⟦X⟧).map
      (powerSeriesFixedDenominatorValuationSubringEquiv k n :
        k⟦X⟧ →+* fixedDenominatorValuationSubring k n) =
        IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) :=
  IsLocalRing.map_ringEquiv_maximalIdeal
    (powerSeriesFixedDenominatorValuationSubringEquiv k n)

theorem powerSeriesFixedDenominatorLevelValuationSubringEquiv_map_maximalIdeal
    (n : ℕ+) :
    (IsLocalRing.maximalIdeal k⟦X⟧).map
      (powerSeriesFixedDenominatorLevelValuationSubringEquiv k n :
        k⟦X⟧ →+* fixedDenominatorLevelValuationSubring k n) =
        IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n) :=
  IsLocalRing.map_ringEquiv_maximalIdeal
    (powerSeriesFixedDenominatorLevelValuationSubringEquiv k n)

theorem fixedLevelPowerSeriesEquivHypothesis :
    FixedLevelPowerSeriesEquivHypothesis k := by
  intro n
  exact ⟨powerSeriesFixedDenominatorLevelValuationSubringEquiv k n,
    powerSeriesFixedDenominatorLevelValuationSubringEquiv_map_maximalIdeal k n⟩

/-- Every fixed-denominator valuation level is complete for its maximal-ideal topology. -/
theorem fixedDenominatorLevelValuationSubring_isAdicComplete :
    ∀ n : ℕ+, IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n))
      (fixedDenominatorLevelValuationSubring k n) := by
  let _ : IsAdicComplete (IsLocalRing.maximalIdeal k⟦X⟧) k⟦X⟧ :=
    powerSeries_isAdicComplete_maximalIdeal k
  exact levelValuationSubringAdicComplete_of_fixedLevelPowerSeriesEquiv k
    (fixedLevelPowerSeriesEquivHypothesis k)

/-- The fixed-denominator valuation subring used in the Puiseux union is complete for its
maximal-ideal topology. -/
theorem fixedDenominatorValuationSubring_isAdicComplete :
    ∀ n : ℕ+, IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n) := by
  let _ : IsAdicComplete (IsLocalRing.maximalIdeal k⟦X⟧) k⟦X⟧ :=
    powerSeries_isAdicComplete_maximalIdeal k
  intro n
  let e := powerSeriesFixedDenominatorValuationSubringEquiv k n
  have hcomplete : IsAdicComplete
      ((IsLocalRing.maximalIdeal k⟦X⟧).map
        (e : k⟦X⟧ →+* fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n) :=
    isAdicComplete_map_ringEquiv e (IsLocalRing.maximalIdeal k⟦X⟧)
  rw [show
      (IsLocalRing.maximalIdeal k⟦X⟧).map
        (e : k⟦X⟧ →+* fixedDenominatorValuationSubring k n) =
          IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) by
        dsimp [e]
        exact powerSeriesFixedDenominatorValuationSubringEquiv_map_maximalIdeal k n]
    at hcomplete
  exact hcomplete

end

end Puiseux

end HahnKaplanskyRealClosedness
