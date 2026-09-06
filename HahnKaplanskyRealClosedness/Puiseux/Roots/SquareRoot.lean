/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Support.Base

/-!
# Puiseux bounded square roots

This file contains the bounded-denominator square-root construction for Puiseux series.
-/

namespace HahnKaplanskyRealClosedness
namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

/-- Square-root existence in the ambient Hahn field, strengthened with the bounded-denominator
support condition needed to descend back to Puiseux series. -/
def BoundedSquareRootHypothesis [LinearOrder k] [IsStrictOrderedRing k] : Prop :=
  ∀ {x : Series k}, 0 ≤ x →
    ∃ y : HahnField k ℚ, HasBoundedDenominatorSupport k y ∧
      (x : HahnField k ℚ) = y * y

/-- The local square-root input needed for Puiseux: a normalized valuation-subring unit with
positive residue and bounded-denominator support has a bounded-denominator square root. -/
def BoundedNormalizedUnitSquareRootHypothesis [LinearOrder k] [IsStrictOrderedRing k] : Prop :=
  ∀ u : HahnField.valuationSubring k ℚ,
    IsUnit u → 0 < HahnField.constantCoeff k ℚ u →
      HasBoundedDenominatorSupport k (u : HahnField k ℚ) →
        ∃ z : HahnField k ℚ,
          HasBoundedDenominatorSupport k z ∧ (u : HahnField k ℚ) = z * z

/-- The remaining square-root input after removing the positive constant coefficient. -/
def BoundedConstantCoeffOneSquareRootHypothesis [LinearOrder k] [IsStrictOrderedRing k] : Prop :=
  ∀ u : HahnField.valuationSubring k ℚ,
    IsUnit u → HahnField.constantCoeff k ℚ u = 1 →
      HasBoundedDenominatorSupport k (u : HahnField k ℚ) →
        ∃ z : HahnField k ℚ,
          HasBoundedDenominatorSupport k z ∧ (u : HahnField k ℚ) = z * z

theorem hasDenominatorSupport_binomialFamily [BinomialRing k] {n : ℕ+} {x : HahnField k ℚ}
    (hxpos : 0 < (ofLex x - 1).orderTop) (hx : HasDenominatorSupport k n x)
    (r : k) (m : ℕ) :
    HasDenominatorSupport k n
      (toLex (HahnSeries.SummableFamily.binomialFamily (ofLex x) r m) : HahnField k ℚ) := by
  rw [HahnSeries.SummableFamily.binomialFamily_apply hxpos]
  apply hasDenominatorSupport_smul k
  exact hasDenominatorSupport_pow k
    (by
      convert hasDenominatorSupport_sub k hx (hasDenominatorSupport_one k n) using 1
      rfl) m

theorem hasDenominatorSupport_hsum_binomialFamily [BinomialRing k] {n : ℕ+} {x : HahnField k ℚ}
    (hxpos : 0 < (ofLex x - 1).orderTop) (hx : HasDenominatorSupport k n x)
    (r : k) :
    HasDenominatorSupport k n
      (toLex (HahnSeries.SummableFamily.binomialFamily (ofLex x) r).hsum : HahnField k ℚ) :=
  hasDenominatorSupport_hsum k (HahnSeries.SummableFamily.binomialFamily (ofLex x) r)
    fun m => hasDenominatorSupport_binomialFamily k hxpos hx r m

/-- The explicit binomial square root of a Hahn-field element close to `1`. -/
noncomputable def binomialHalfRoot [BinomialRing k] (x : HahnField k ℚ) : HahnField k ℚ :=
  toLex (HahnSeries.SummableFamily.binomialFamily (ofLex x) ((1 : k) / 2)).hsum

@[simp]
theorem ofLex_binomialHalfRoot [BinomialRing k] (x : HahnField k ℚ) :
    ofLex (binomialHalfRoot k x) =
      (HahnSeries.SummableFamily.binomialFamily (ofLex x) ((1 : k) / 2)).hsum :=
  rfl

theorem orderTopSubOnePos_pow_val_eq_hsum [LinearOrder k] [IsStrictOrderedRing k]
    {x : HahnField k ℚ} (hxpos : 0 < (ofLex x - 1).orderTop) (r : k) :
    (((HahnSeries.toOrderTopSubOnePos hxpos : HahnSeries.orderTopSubOnePos ℚ k) ^ r).val.val :
        HahnSeries ℚ k) =
      (HahnSeries.SummableFamily.binomialFamily (ofLex x) r).hsum := by
  rw [HahnSeries.binomial_power]
  rfl

theorem hasBoundedDenominatorSupport_binomialHalfRoot [BinomialRing k]
    {x : HahnField k ℚ} (hxpos : 0 < (ofLex x - 1).orderTop)
    (hxbd : HasBoundedDenominatorSupport k x) :
    HasBoundedDenominatorSupport k (binomialHalfRoot k x) := by
  rcases hxbd with ⟨n, hxden⟩
  refine ⟨n, ?_⟩
  change HasDenominatorSupport k n
    (toLex (HahnSeries.SummableFamily.binomialFamily (ofLex x) ((1 : k) / 2)).hsum :
      HahnField k ℚ)
  exact hasDenominatorSupport_hsum_binomialFamily k hxpos hxden ((1 : k) / 2)

theorem binomialHalfRoot_sq_series [LinearOrder k] [IsStrictOrderedRing k]
    {x : HahnField k ℚ} (hxpos : 0 < (ofLex x - 1).orderTop) :
    let zS : HahnSeries ℚ k :=
      (HahnSeries.SummableFamily.binomialFamily (ofLex x) ((1 : k) / 2)).hsum
    zS * zS = ofLex x := by
  let u : HahnSeries.orderTopSubOnePos ℚ k := HahnSeries.toOrderTopSubOnePos hxpos
  let zS : HahnSeries ℚ k :=
    (HahnSeries.SummableFamily.binomialFamily (ofLex x) ((1 : k) / 2)).hsum
  have hpow : (((u ^ ((1 : k) / 2)).val.val : HahnSeries ℚ k) = zS) := by
    dsimp only [u, zS]
    exact orderTopSubOnePos_pow_val_eq_hsum k hxpos ((1 : k) / 2)
  have hu : ((u.val.val : HahnSeries ℚ k) = ofLex x) := by
    dsimp only [u]
    rfl
  have hs0 : (u ^ ((1 : k) / 2)) * (u ^ ((1 : k) / 2)) = u :=
    HahnField.orderTopSubOnePos_sq_pow_half k ℚ u
  have hs1 :
      ((u ^ ((1 : k) / 2)).val.val : HahnSeries ℚ k) *
          ((u ^ ((1 : k) / 2)).val.val : HahnSeries ℚ k) =
        (u.val.val : HahnSeries ℚ k) := by
    have hs2 :=
      congrArg (fun v : HahnSeries.orderTopSubOnePos ℚ k =>
        (v.val.val : HahnSeries ℚ k)) hs0
    simpa using hs2
  rw [hpow, hu] at hs1
  exact hs1

theorem binomialHalfRoot_sq_of_orderTop_sub_one_pos
    [LinearOrder k] [IsStrictOrderedRing k]
    {x : HahnField k ℚ} (hxpos : 0 < (ofLex x - 1).orderTop) :
    binomialHalfRoot k x * binomialHalfRoot k x = x := by
  let zS : HahnSeries ℚ k :=
    (HahnSeries.SummableFamily.binomialFamily (ofLex x) ((1 : k) / 2)).hsum
  have hS : zS * zS = ofLex x := by
    simpa [zS] using binomialHalfRoot_sq_series k hxpos
  apply toLex.injective
  change ofLex (binomialHalfRoot k x) * ofLex (binomialHalfRoot k x) = ofLex x
  simpa [ofLex_binomialHalfRoot, zS] using hS

theorem exists_square_root_of_orderTop_sub_one_pos_with_bounded_support
    [LinearOrder k] [IsStrictOrderedRing k]
    {x : HahnField k ℚ} (hxpos : 0 < (ofLex x - 1).orderTop)
    (hxbd : HasBoundedDenominatorSupport k x) :
    ∃ z : HahnField k ℚ, HasBoundedDenominatorSupport k z ∧ x = z * z := by
  refine ⟨binomialHalfRoot k x, hasBoundedDenominatorSupport_binomialHalfRoot k hxpos hxbd, ?_⟩
  exact (binomialHalfRoot_sq_of_orderTop_sub_one_pos k hxpos).symm

theorem orderTop_sub_one_pos_of_constantCoeff_eq_one
    [LinearOrder k] [IsStrictOrderedRing k]
    {u : HahnField.valuationSubring k ℚ}
    (hcc : HahnField.constantCoeff k ℚ u = 1) :
    0 < (ofLex ((u : HahnField k ℚ) - 1)).orderTop := by
  have hzero : HahnField.constantCoeffRingHom k ℚ (u - 1) = 0 := by
    rw [map_sub]
    change HahnField.constantCoeff k ℚ u -
        HahnField.constantCoeff k ℚ (1 : HahnField.valuationSubring k ℚ) = 0
    simp [hcc]
  have hpos := (HahnField.constantCoeffRingHom_eq_zero_iff_pos_addVal k ℚ (u - 1)).mp hzero
  simpa [HahnField.addVal_apply] using hpos

theorem boundedConstantCoeffOneSquareRootHypothesis
    [LinearOrder k] [IsStrictOrderedRing k] :
    BoundedConstantCoeffOneSquareRootHypothesis k := by
  intro u _hu hcc hxbd
  have hxpos : 0 < (ofLex ((u : HahnField k ℚ) - 1)).orderTop :=
    orderTop_sub_one_pos_of_constantCoeff_eq_one k hcc
  exact exists_square_root_of_orderTop_sub_one_pos_with_bounded_support k hxpos hxbd

theorem isSquare_of_hahn_square_root_of_bounded_support
    {x : Series k} {y : HahnField k ℚ}
    (hy : HasBoundedDenominatorSupport k y)
    (hxy : (x : HahnField k ℚ) = y * y) :
    IsSquare x := by
  refine ⟨ofHahnField k y hy, ?_⟩
  ext
  exact hxy

theorem isSquare_of_bounded_square_root_hypothesis
    [LinearOrder k] [IsStrictOrderedRing k]
    (hSquare : BoundedSquareRootHypothesis k) {x : Series k} (hx : 0 ≤ x) :
    IsSquare x := by
  rcases hSquare hx with ⟨y, hy, hxy⟩
  exact isSquare_of_hahn_square_root_of_bounded_support k hy hxy

/-- Remove the positive constant coefficient from a normalized unit when nonnegative
coefficients have square roots.  It is enough to solve the bounded square-root problem for units
with constant coefficient `1`. -/
theorem boundedNormalizedUnitSquareRootHypothesis_of_constantCoeff_one_of_nonneg_squares
    [LinearOrder k] [IsStrictOrderedRing k]
    (hsq : ∀ {x : k}, 0 ≤ x → IsSquare x)
    (hone : BoundedConstantCoeffOneSquareRootHypothesis k) :
    BoundedNormalizedUnitSquareRootHypothesis k := by
  intro u huunit hupos hubd
  rcases hsq hupos.le with ⟨c, hc⟩
  have hcnz : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hc
    linarith
  let ci : HahnField.valuationSubring k ℚ := ⟨toLex (HahnSeries.single 0 c⁻¹), by
    change (0 : WithTop ℚ) ≤
      HahnField.addVal k ℚ (toLex (HahnSeries.single 0 c⁻¹))
    rw [HahnField.addVal_single_of_ne (k := k) (Γ := ℚ) (inv_ne_zero hcnz)]
    simp⟩
  let w : HahnField.valuationSubring k ℚ := ci * ci * u
  have hci : HahnField.constantCoeffRingHom k ℚ ci = c⁻¹ := by
    rw [HahnField.constantCoeffRingHom_apply]
    change (ofLex (toLex (HahnSeries.single 0 c⁻¹))).coeff 0 = c⁻¹
    simp
  have hciunit : IsUnit ci := by
    apply HahnField.isUnit_of_constantCoeffRingHom_ne_zero k ℚ
    rw [hci]
    exact inv_ne_zero hcnz
  have hwunit : IsUnit w := by
    simpa [w, mul_assoc] using (hciunit.mul hciunit).mul huunit
  have hucc : HahnField.constantCoeffRingHom k ℚ u = c ^ 2 := by
    rw [HahnField.constantCoeffRingHom_apply, ← HahnField.constantCoeff_apply]
    simpa [pow_two] using hc
  have hwmap : HahnField.constantCoeffRingHom k ℚ w =
      HahnField.constantCoeffRingHom k ℚ ci * HahnField.constantCoeffRingHom k ℚ ci *
        HahnField.constantCoeffRingHom k ℚ u := by
    rw [show w = (ci * ci) * u by rfl, map_mul, map_mul]
  have hwcc : HahnField.constantCoeff k ℚ w = 1 := by
    change HahnField.constantCoeffRingHom k ℚ w = 1
    rw [hwmap, hci, hucc]
    field_simp [hcnz]
  have hci_bd : HasBoundedDenominatorSupport k (ci : HahnField k ℚ) := by
    simpa [ci] using
      hasBoundedDenominatorSupport_single k (c⁻¹) (hasDenominator_zero (1 : ℕ+))
  have hwbd : HasBoundedDenominatorSupport k (w : HahnField k ℚ) := by
    simpa [w, mul_assoc] using
      hasBoundedDenominatorSupport_mul k
        (hasBoundedDenominatorSupport_mul k hci_bd hci_bd) hubd
  rcases hone w hwunit hwcc hwbd with ⟨z, hzbd, hzw⟩
  let c0 : HahnField k ℚ := toLex (HahnSeries.single 0 c)
  have hc0bd : HasBoundedDenominatorSupport k c0 := by
    simpa [c0] using
      hasBoundedDenominatorSupport_single k c (hasDenominator_zero (1 : ℕ+))
  refine ⟨c0 * z, hasBoundedDenominatorSupport_mul k hc0bd hzbd, ?_⟩
  have hc0ci : c0 * (ci : HahnField k ℚ) = 1 := by
    dsimp [c0, ci]
    change toLex (HahnSeries.single 0 c * HahnSeries.single 0 c⁻¹) = (1 : HahnField k ℚ)
    rw [HahnSeries.single_mul_single]
    simp [hcnz]
  have hdenorm : (u : HahnField k ℚ) = c0 * c0 * (w : HahnField k ℚ) := by
    change (u : HahnField k ℚ) =
      c0 * c0 * ((ci : HahnField k ℚ) * (ci : HahnField k ℚ) * (u : HahnField k ℚ))
    rw [show c0 * c0 * ((ci : HahnField k ℚ) * (ci : HahnField k ℚ) *
          (u : HahnField k ℚ)) =
        (c0 * (ci : HahnField k ℚ)) * (c0 * (ci : HahnField k ℚ)) *
          (u : HahnField k ℚ) by ring]
    rw [hc0ci]
    simp
  calc
    (u : HahnField k ℚ) = c0 * c0 * (w : HahnField k ℚ) := hdenorm
    _ = c0 * c0 * (z * z) := by rw [hzw]
    _ = (c0 * z) * (c0 * z) := by ring

/-- Reduce bounded square roots of arbitrary nonnegative Puiseux elements to the normalized
valuation-subring unit case by factoring out the leading monomial. -/
theorem boundedSquareRootHypothesis_of_normalized_units
    [LinearOrder k] [IsStrictOrderedRing k]
    (hunit : BoundedNormalizedUnitSquareRootHypothesis k) :
    BoundedSquareRootHypothesis k := by
  intro x hx
  rcases lt_or_eq_of_le hx with hxpos | hzero
  · have hxne : (x : HahnField k ℚ) ≠ 0 := by
      exact_mod_cast ne_of_gt hxpos
    let γ : ℚ := (HahnField.addVal k ℚ (x : HahnField k ℚ)).untop
      (by simpa [AddValuation.ne_top_iff] using hxne)
    have hxγ : HahnField.addVal k ℚ (x : HahnField k ℚ) = (γ : WithTop ℚ) :=
      (WithTop.coe_untop _ _).symm
    rcases hasBoundedDenominatorSupport_coe k x with ⟨nx, hnx⟩
    have hγden : HasDenominator nx γ := by
      have horder := hasDenominatorSupport_order k hnx hxne
      have hsne : ofLex (x : HahnField k ℚ) ≠ 0 := by
        intro hs
        exact hxne (by simpa using congrArg toLex hs)
      have hγeq : γ = (ofLex (x : HahnField k ℚ)).order := by
        have htop :
            (ofLex (x : HahnField k ℚ)).orderTop = (γ : WithTop ℚ) := by
          simpa [HahnField.addVal_apply] using hxγ
        have horderTop :
            ((ofLex (x : HahnField k ℚ)).order : WithTop ℚ) =
              (ofLex (x : HahnField k ℚ)).orderTop := by
          simpa using HahnSeries.order_eq_orderTop_of_ne_zero hsne
        have hcoe : ((ofLex (x : HahnField k ℚ)).order : WithTop ℚ) = (γ : WithTop ℚ) := by
          rw [horderTop, htop]
        exact (WithTop.coe_eq_coe.mp hcoe).symm
      rwa [hγeq]
    let y : HahnField.valuationSubring k ℚ :=
      ⟨HahnField.hahnMonomial k ℚ (-γ) * (x : HahnField k ℚ), by
        change (0 : WithTop ℚ) ≤
          HahnField.addVal k ℚ (toLex (HahnSeries.single (-γ) (1 : k)) *
            (x : HahnField k ℚ))
        rw [HahnField.addVal_single_neg_mul_of_addVal_eq k ℚ hxγ]⟩
    have hyunit : IsUnit y := HahnField.isUnit_normalized_monomial k ℚ hxγ
    have hypos : 0 < HahnField.constantCoeff k ℚ y :=
      (HahnField.pos_iff_constantCoeff_pos_of_normalized_monomial k ℚ hxγ).mp hxpos
    have hybd : HasBoundedDenominatorSupport k (y : HahnField k ℚ) := by
      exact hasBoundedDenominatorSupport_mul k
        (hasBoundedDenominatorSupport_hahnMonomial k (hasDenominator_neg hγden))
        (hasBoundedDenominatorSupport_coe k x)
    rcases hunit y hyunit hypos hybd with ⟨z, hzbd, hyz⟩
    let halfγ : ℚ := γ / 2
    have hhalfγ : HasDenominator ⟨(halfγ).den, (halfγ).den_pos⟩ halfγ :=
      hasDenominator_self halfγ
    let m : HahnField k ℚ := HahnField.hahnMonomial k ℚ halfγ
    refine ⟨m * z, hasBoundedDenominatorSupport_mul k
      (hasBoundedDenominatorSupport_hahnMonomial k hhalfγ) hzbd, ?_⟩
    have hm : m ^ 2 = HahnField.hahnMonomial k ℚ γ := by
      dsimp [m, halfγ, HahnField.hahnMonomial]
      change toLex (HahnSeries.single (γ / 2) (1 : k) ^ 2) =
        toLex (HahnSeries.single γ (1 : k))
      rw [HahnSeries.single_pow]
      have htwo : 2 * (γ / 2) = γ := by ring
      simp [htwo]
    have hdenorm :
        HahnField.hahnMonomial k ℚ γ * (y : HahnField k ℚ) = (x : HahnField k ℚ) := by
      change HahnField.hahnMonomial k ℚ γ *
        (HahnField.hahnMonomial k ℚ (-γ) * (x : HahnField k ℚ)) = (x : HahnField k ℚ)
      rw [← mul_assoc]
      change toLex (HahnSeries.single γ (1 : k) * HahnSeries.single (-γ) (1 : k)) *
        (x : HahnField k ℚ) = (x : HahnField k ℚ)
      rw [HahnSeries.single_mul_single]
      simp
    calc
      (x : HahnField k ℚ) = HahnField.hahnMonomial k ℚ γ * (y : HahnField k ℚ) :=
        hdenorm.symm
      _ = HahnField.hahnMonomial k ℚ γ * (z * z) := by rw [hyz]
      _ = (m * z) * (m * z) := by
        rw [← hm, pow_two]
        ring
  · refine ⟨0, hasBoundedDenominatorSupport_zero k, ?_⟩
    rw [← hzero]
    simp

theorem boundedSquareRootHypothesis_of_constantCoeff_one_of_nonneg_squares
    [LinearOrder k] [IsStrictOrderedRing k]
    (hsq : ∀ {x : k}, 0 ≤ x → IsSquare x)
    (hone : BoundedConstantCoeffOneSquareRootHypothesis k) :
    BoundedSquareRootHypothesis k :=
  boundedSquareRootHypothesis_of_normalized_units k
    (boundedNormalizedUnitSquareRootHypothesis_of_constantCoeff_one_of_nonneg_squares k hsq hone)

theorem boundedSquareRootHypothesis
    [LinearOrder k] [IsStrictOrderedRing k] [IsRealClosed k] :
    BoundedSquareRootHypothesis k :=
  boundedSquareRootHypothesis_of_constantCoeff_one_of_nonneg_squares k
    (fun hx => IsSquare.of_nonneg hx) (boundedConstantCoeffOneSquareRootHypothesis k)

end

end Puiseux
end HahnKaplanskyRealClosedness
