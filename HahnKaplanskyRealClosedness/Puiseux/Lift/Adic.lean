/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Inverse
import HahnKaplanskyRealClosedness.Puiseux.Lift.FixedLevel

/-!
# Adic-completeness API for Puiseux valuation levels

This file contains generic adic-completeness transport lemmas and the fixed-denominator
Puiseux-level bridges built from the valuation-level equivalences in
`Puiseux.ValuationFixedLevel`.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

open scoped PowerSeries Ring

section PowerSeries

variable (k : Type*) [Field k]

theorem powerSeries_maximalIdeal_pow_eq_span_X_pow (n : ℕ) :
    (IsLocalRing.maximalIdeal k⟦X⟧) ^ n =
      Ideal.span {(PowerSeries.X : k⟦X⟧) ^ n} := by
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow]

theorem mem_powerSeries_maximalIdeal_pow_iff_coeff_lt_eq_zero
    (n : ℕ) (f : k⟦X⟧) :
    f ∈ (IsLocalRing.maximalIdeal k⟦X⟧) ^ n ↔
      ∀ i, i < n → PowerSeries.coeff i f = 0 := by
  rw [powerSeries_maximalIdeal_pow_eq_span_X_pow k n, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]

instance powerSeries_isAdicComplete_maximalIdeal :
    IsAdicComplete (IsLocalRing.maximalIdeal k⟦X⟧) k⟦X⟧ where
  haus' := by
    intro f hf
    ext i
    have hfi := hf (i + 1)
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero,
      mem_powerSeries_maximalIdeal_pow_iff_coeff_lt_eq_zero] at hfi
    exact hfi i (Nat.lt_succ_self i)
  prec' := by
    intro f hf
    refine ⟨PowerSeries.mk fun i => PowerSeries.coeff i (f (i + 1)), ?_⟩
    intro n
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      mem_powerSeries_maximalIdeal_pow_iff_coeff_lt_eq_zero]
    intro i hi
    have hstep := hf (Nat.succ_le_iff.mpr hi)
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem,
      mem_powerSeries_maximalIdeal_pow_iff_coeff_lt_eq_zero] at hstep
    have hcoeff := hstep i (Nat.lt_succ_self i)
    have hcoeff_eq :
        PowerSeries.coeff i (f (i + 1)) = PowerSeries.coeff i (f n) :=
      sub_eq_zero.mp hcoeff
    simpa [PowerSeries.coeff_mk, sub_eq_zero] using hcoeff_eq.symm

end PowerSeries

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

theorem smodEq_map_ringEquiv_adic_iff {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (n : ℕ) (x y : S) :
    x ≡ y [SMOD ((I.map (e : R →+* S)) ^ n • ⊤ : Submodule S S)] ↔
      e.symm x ≡ e.symm y [SMOD (I ^ n • ⊤ : Submodule R R)] := by
  rw [SModEq.sub_mem, SModEq.sub_mem]
  simp only [smul_eq_mul, Ideal.mul_top]
  constructor
  · intro h
    have hmap :
        e.symm (x - y) ∈ Ideal.comap (e : R →+* S) ((I.map (e : R →+* S)) ^ n) := by
      change e (e.symm (x - y)) ∈ ((I.map (e : R →+* S)) ^ n)
      simpa using h
    rw [← Ideal.map_pow,
      Ideal.comap_map_of_bijective (f := (e : R →+* S)) e.bijective] at hmap
    simpa using hmap
  · intro h
    have hmap : e (e.symm x - e.symm y) ∈ (I ^ n).map (e : R →+* S) :=
      Ideal.mem_map_of_mem (e : R →+* S) h
    rw [Ideal.map_pow] at hmap
    simpa using hmap

theorem isAdicComplete_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete (I.map (e : R →+* S)) S where
  toIsHausdorff := by
    refine ⟨fun x hx => ?_⟩
    apply e.symm.injective
    have hx0 : e.symm x = 0 := by
      exact IsHausdorff.haus (show IsHausdorff I R from inferInstance) (e.symm x) (by
        intro n
        simpa using (smodEq_map_ringEquiv_adic_iff e I n x 0).mp (hx n))
    simpa using hx0
  toIsPrecomplete := by
    refine ⟨fun f hf => ?_⟩
    have hg :
        ∀ {m n}, m ≤ n →
          e.symm (f m) ≡ e.symm (f n) [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      exact (smodEq_map_ringEquiv_adic_iff e I m (f m) (f n)).mp (hf hmn)
    rcases IsPrecomplete.prec (show IsPrecomplete I R from inferInstance) hg with ⟨L, hL⟩
    refine ⟨e L, ?_⟩
    intro n
    exact (smodEq_map_ringEquiv_adic_iff e I n (f n) (e L)).mpr (by simpa using hL n)

theorem henselianLocalRing_of_isAdicComplete_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    HenselianLocalRing R := by
  constructor
  intro f hf a₀ hroot hder
  have : HenselianRing R (IsLocalRing.maximalIdeal R) := inferInstance
  exact HenselianRing.is_henselian f hf a₀ hroot
    (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))

/-- A non-monic simple-root lift from adic completeness.

This is the Newton-iteration core of `IsAdicComplete.henselianRing`, isolated because the
iteration itself does not use monicity. -/
theorem exists_root_of_isAdicComplete_simpleRoot
    (R : Type*) [CommRing R] (I : Ideal R)
    [IsAdicComplete I R]
    {f : Polynomial R} {a₀ : R}
    (hroot : f.eval a₀ ∈ I)
    (hder : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := f.derivative
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => ?_
    rw [hc, sub_eq_add_neg, ← add_zero a₀]
    refine ih.add ?_
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine I.mul_mem_right _ ?_
    rw [← SModEq.zero] at hroot ⊢
    exact (ih.eval f).trans hroot
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert hder using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa [c, pow_one] using hroot
    | succ n ih => ?_
    rw [← Polynomial.taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
      add_neg_cancel_comm]
    rw [Polynomial.eval_eq_sum,
      Polynomial.sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
    swap
    · intro i
      rw [zero_mul]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, Polynomial.taylor_coeff_zero, Polynomial.taylor_coeff_one,
        pow_zero, pow_one, mul_one, mul_neg, mul_left_comm,
        Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
      exact Ideal.zero_mem _
    · refine Submodule.sum_mem _ ?_
      simp only [Finset.mem_Ico]
      rintro i ⟨h2i, _⟩
      have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih => ?_
    rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
    refine ih.add ?_
    symm
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
    rw [add_assoc]
    exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by
      exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ hroot

theorem fixedLevelHenselianLocalRing_of_isAdicComplete
    [∀ n : ℕ+, IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n)] :
    ∀ n : ℕ+, HenselianLocalRing (fixedDenominatorValuationSubring k n) := by
  intro n
  have : IsLocalRing (fixedDenominatorValuationSubring k n) := inferInstance
  have : IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n) := inferInstance
  exact henselianLocalRing_of_isAdicComplete_maximalIdeal
    (fixedDenominatorValuationSubring k n)

theorem fixedLevelAdicComplete_of_levelValuationSubringAdicComplete
    [∀ n : ℕ+, IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n))
      (fixedDenominatorLevelValuationSubring k n)] :
    ∀ n : ℕ+, IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n) := by
  intro n
  have : IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n))
      (fixedDenominatorLevelValuationSubring k n) := inferInstance
  let e := fixedDenominatorValuationSubringEquiv k n
  have hcomplete : IsAdicComplete
      ((IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n)).map
        (e.symm : fixedDenominatorLevelValuationSubring k n →+*
          fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n) :=
    isAdicComplete_map_ringEquiv e.symm
      (IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n))
  rw [show
      (IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n)).map
        (e.symm : fixedDenominatorLevelValuationSubring k n →+*
          fixedDenominatorValuationSubring k n) =
        IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) by
      dsimp [e]
      exact fixedDenominatorValuationSubringEquiv_symm_map_maximalIdeal k n] at hcomplete
  exact hcomplete

/-- An intermediate target for identifying each fixed-denominator valuation level with a power
series valuation ring.  Supplying this equivalence and the compatibility of maximal ideals lets
the route reuse `k⟦X⟧`-adic completeness. -/
def FixedLevelPowerSeriesEquivHypothesis : Prop :=
  ∀ n : ℕ+, ∃ e : k⟦X⟧ ≃+* fixedDenominatorLevelValuationSubring k n,
    (IsLocalRing.maximalIdeal k⟦X⟧).map
      (e : k⟦X⟧ →+* fixedDenominatorLevelValuationSubring k n) =
        IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n)

theorem levelValuationSubringAdicComplete_of_powerSeriesEquiv {n : ℕ+}
    [IsAdicComplete (IsLocalRing.maximalIdeal k⟦X⟧) k⟦X⟧]
    (e : k⟦X⟧ ≃+* fixedDenominatorLevelValuationSubring k n)
    (he : (IsLocalRing.maximalIdeal k⟦X⟧).map
      (e : k⟦X⟧ →+* fixedDenominatorLevelValuationSubring k n) =
        IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n)) :
    IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n))
      (fixedDenominatorLevelValuationSubring k n) := by
  have hcomplete : IsAdicComplete
      ((IsLocalRing.maximalIdeal k⟦X⟧).map
        (e : k⟦X⟧ →+* fixedDenominatorLevelValuationSubring k n))
      (fixedDenominatorLevelValuationSubring k n) :=
    isAdicComplete_map_ringEquiv e (IsLocalRing.maximalIdeal k⟦X⟧)
  simpa [he] using hcomplete

theorem levelValuationSubringAdicComplete_of_fixedLevelPowerSeriesEquiv
    [IsAdicComplete (IsLocalRing.maximalIdeal k⟦X⟧) k⟦X⟧]
    (hEquiv : FixedLevelPowerSeriesEquivHypothesis k) :
    ∀ n : ℕ+, IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorLevelValuationSubring k n))
      (fixedDenominatorLevelValuationSubring k n) := by
  intro n
  rcases hEquiv n with ⟨e, he⟩
  exact levelValuationSubringAdicComplete_of_powerSeriesEquiv k e he

end

end Puiseux

end HahnKaplanskyRealClosedness
