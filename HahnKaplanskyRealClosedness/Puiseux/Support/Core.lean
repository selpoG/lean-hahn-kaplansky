/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import Mathlib.Algebra.Order.Field.Subfield
import HahnKaplanskyRealClosedness.Basic.ClusterProperty
import HahnKaplanskyRealClosedness.Basic.ValuationClusterProperty
import HahnKaplanskyRealClosedness.SimpleCluster.Core

/-!
# Puiseux series inside the rational Hahn field

This file starts the refactoring from the former full-Hahn-field target to the Puiseux target.
Puiseux series are modeled as the elements of `HahnField k ℚ` whose support has a common
denominator.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

instance instRatDivisibleByNat : DivisibleBy ℚ ℕ where
  div q n := q / (n : ℚ)
  div_zero q := by simp
  div_cancel := by
    intro n q hn
    rw [nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr hn]

/-- A rational exponent belongs to the lattice `(1 / n) • ℤ`. -/
def HasDenominator (n : ℕ+) (q : ℚ) : Prop :=
  ∃ m : ℤ, q = (m : ℚ) / (n : ℚ)

variable (k : Type*) [Field k]

/-- The support of a Hahn series is contained in the lattice `(1 / n) • ℤ`. -/
def HasDenominatorSupport (n : ℕ+) (x : HahnField k ℚ) : Prop :=
  ∀ q ∈ (ofLex x).support, HasDenominator n q

/-- The support of a Hahn series has a common denominator. -/
def HasBoundedDenominatorSupport (x : HahnField k ℚ) : Prop :=
  ∃ n : ℕ+, HasDenominatorSupport k n x

theorem hasDenominatorSupport_mono_den
    {x : HahnField k ℚ} {n n' : ℕ+}
    (hn : ∀ q, HasDenominator n q → HasDenominator n' q)
    (hx : HasDenominatorSupport k n x) :
    HasDenominatorSupport k n' x :=
  fun q hq => hn q (hx q hq)

theorem hasBoundedDenominatorSupport_zero :
    HasBoundedDenominatorSupport k (0 : HahnField k ℚ) := by
  refine ⟨1, ?_⟩
  intro q hq
  simp at hq

theorem hasDenominator_zero (n : ℕ+) : HasDenominator n 0 := by
  exact ⟨0, by simp⟩

theorem hasDenominator_self (q : ℚ) : HasDenominator ⟨q.den, q.den_pos⟩ q := by
  refine ⟨q.num, ?_⟩
  exact (Rat.num_div_den q).symm

theorem exists_hasDenominator (q : ℚ) : ∃ n : ℕ+, HasDenominator n q :=
  ⟨⟨q.den, q.den_pos⟩, hasDenominator_self q⟩

theorem hasDenominator_neg {n : ℕ+} {q : ℚ}
    (hq : HasDenominator n q) : HasDenominator n (-q) := by
  rcases hq with ⟨m, rfl⟩
  exact ⟨-m, by
    rw [Int.cast_neg]
    ring⟩

theorem hasDenominator_add_same {n : ℕ+} {q r : ℚ}
    (hq : HasDenominator n q) (hr : HasDenominator n r) :
    HasDenominator n (q + r) := by
  rcases hq with ⟨m, rfl⟩
  rcases hr with ⟨m', rfl⟩
  exact ⟨m + m', by
    rw [Int.cast_add]
    ring⟩

theorem hasDenominator_mul_right {n n' : ℕ+} {q : ℚ}
    (hq : HasDenominator n q) : HasDenominator (n * n') q := by
  rcases hq with ⟨m, rfl⟩
  refine ⟨m * (n' : ℤ), ?_⟩
  field_simp
  rw [Int.cast_mul]
  norm_num
  ring

theorem hasDenominator_of_nsmul_eq {n : ℕ+} {m : ℕ+} {δ γ : ℚ}
    (hγ : HasDenominator n γ) (hscale : (m : ℕ) • δ = γ) :
    HasDenominator (n * m) δ := by
  rcases hγ with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hm0 : (m : ℚ) ≠ 0 := by
    exact_mod_cast m.ne_zero
  rw [nsmul_eq_mul] at hscale
  apply (mul_left_cancel₀ hm0)
  rw [hscale, hz]
  push_cast
  field_simp

theorem hasDenominator_add {n n' : ℕ+} {q r : ℚ}
    (hq : HasDenominator n q) (hr : HasDenominator n' r) :
    HasDenominator (n * n') (q + r) :=
  hasDenominator_add_same (hasDenominator_mul_right (n' := n') hq)
    (by simpa [mul_comm] using (hasDenominator_mul_right (n' := n) hr))

theorem hasDenominatorSupport_zero (n : ℕ+) :
    HasDenominatorSupport k n (0 : HahnField k ℚ) := by
  intro q hq
  simp at hq

theorem hasDenominatorSupport_one (n : ℕ+) :
    HasDenominatorSupport k n (1 : HahnField k ℚ) := by
  intro q hq
  change q ∈ (1 : HahnSeries ℚ k).support at hq
  have hq0 : q = 0 := by
    simpa [HahnSeries.support_one] using hq
  rw [hq0]
  exact hasDenominator_zero n

theorem hasDenominatorSupport_single {n : ℕ+} {γ : ℚ} (c : k)
    (hγ : HasDenominator n γ) :
    HasDenominatorSupport k n (toLex (HahnSeries.single γ c) : HahnField k ℚ) := by
  intro q hq
  change q ∈ (HahnSeries.single γ c).support at hq
  rw [HahnSeries.mem_support] at hq
  have hqγ : q = γ := by
    have hq' : q = γ ∧ c ≠ 0 := by
      simpa [HahnSeries.coeff_single] using hq
    exact hq'.1
  rwa [hqγ]

theorem hasBoundedDenominatorSupport_single {n : ℕ+} {γ : ℚ} (c : k)
    (hγ : HasDenominator n γ) :
    HasBoundedDenominatorSupport k (toLex (HahnSeries.single γ c) : HahnField k ℚ) :=
  ⟨n, hasDenominatorSupport_single k c hγ⟩

theorem hasDenominatorSupport_singleOfNonneg [LinearOrder k] [IsStrictOrderedRing k]
    {n : ℕ+} {γ : ℚ} (c : k)
    (hγ : HasDenominator n γ) (hγnonneg : 0 ≤ γ) :
    HasDenominatorSupport k n
      (HahnField.singleOfNonneg k ℚ γ c hγnonneg : HahnField k ℚ) := by
  rw [HahnField.singleOfNonneg_coe]
  exact hasDenominatorSupport_single k c hγ

theorem hasBoundedDenominatorSupport_singleOfNonneg_of_denominator
    [LinearOrder k] [IsStrictOrderedRing k] {n : ℕ+} {γ : ℚ} (c : k)
    (hγ : HasDenominator n γ) (hγnonneg : 0 ≤ γ) :
    HasBoundedDenominatorSupport k
      (HahnField.singleOfNonneg k ℚ γ c hγnonneg : HahnField k ℚ) :=
  ⟨n, hasDenominatorSupport_singleOfNonneg k c hγ hγnonneg⟩

theorem hasBoundedDenominatorSupport_singleOfNonneg [LinearOrder k] [IsStrictOrderedRing k]
    {γ : ℚ} (c : k)
    (hγnonneg : 0 ≤ γ) :
    HasBoundedDenominatorSupport k
      (HahnField.singleOfNonneg k ℚ γ c hγnonneg : HahnField k ℚ) := by
  rcases exists_hasDenominator γ with ⟨n, hγ⟩
  exact hasBoundedDenominatorSupport_singleOfNonneg_of_denominator k c hγ hγnonneg

theorem hasDenominatorSupport_order {n : ℕ+} {x : HahnField k ℚ}
    (hx : HasDenominatorSupport k n x) (hxn : x ≠ 0) :
    HasDenominator n (ofLex x).order := by
  apply hx
  rw [HahnSeries.mem_support]
  apply HahnSeries.coeff_order_eq_zero.not.mpr
  exact fun hs => hxn (by simpa using congrArg toLex hs)

theorem hasDenominatorSupport_neg {n : ℕ+} {x : HahnField k ℚ}
    (hx : HasDenominatorSupport k n x) :
    HasDenominatorSupport k n (-x) := by
  intro q hq
  change q ∈ (-(ofLex x)).support at hq
  rw [HahnSeries.support_neg] at hq
  exact hx q hq

theorem hasDenominatorSupport_add {n : ℕ+} {x y : HahnField k ℚ}
    (hx : HasDenominatorSupport k n x)
    (hy : HasDenominatorSupport k n y) :
    HasDenominatorSupport k n (x + y) := by
  intro q hq
  change q ∈ (ofLex x + ofLex y).support at hq
  rcases HahnSeries.support_add_subset (ofLex x) (ofLex y) hq with hqx | hqy
  · exact hx q hqx
  · exact hy q hqy

theorem hasDenominatorSupport_mul {n : ℕ+} {x y : HahnField k ℚ}
    (hx : HasDenominatorSupport k n x)
    (hy : HasDenominatorSupport k n y) :
    HasDenominatorSupport k n (x * y) := by
  intro q hq
  change q ∈ (ofLex x * ofLex y).support at hq
  rcases HahnSeries.support_mul_subset hq with ⟨a, ha, b, hb, hqeq⟩
  rw [← hqeq]
  exact hasDenominator_add_same (hx a ha) (hy b hb)

theorem hasDenominatorSupport_sub {n : ℕ+} {x y : HahnField k ℚ}
    (hx : HasDenominatorSupport k n x)
    (hy : HasDenominatorSupport k n y) :
    HasDenominatorSupport k n (x - y) := by
  simpa [sub_eq_add_neg] using hasDenominatorSupport_add k hx (hasDenominatorSupport_neg k hy)

theorem hasDenominatorSupport_pow {n : ℕ+} {x : HahnField k ℚ}
    (hx : HasDenominatorSupport k n x) :
    ∀ m : ℕ, HasDenominatorSupport k n (x ^ m)
  | 0 => by simpa using hasDenominatorSupport_one k n
  | m + 1 => by
      rw [pow_succ]
      exact hasDenominatorSupport_mul k (hasDenominatorSupport_pow hx m) hx

theorem hasDenominatorSupport_smul {n : ℕ+} {x : HahnField k ℚ}
    (c : k) (hx : HasDenominatorSupport k n x) :
    HasDenominatorSupport k n (toLex (c • ofLex x) : HahnField k ℚ) := by
  intro q hq
  change q ∈ (c • ofLex x).support at hq
  exact hx q (HahnSeries.support_smul_subset c (ofLex x) hq)

theorem hasDenominatorSupport_hsum {α : Type*} {n : ℕ+}
    (s : HahnSeries.SummableFamily ℚ k α)
    (hs : ∀ a, HasDenominatorSupport k n (toLex (s a) : HahnField k ℚ)) :
    HasDenominatorSupport k n (toLex s.hsum : HahnField k ℚ) := by
  intro q hq
  change q ∈ s.hsum.support at hq
  exact HahnField.hsum_support_property k ℚ s
    (fun a q hqa => hs a q (by simpa using hqa)) q hq

theorem hasDenominatorSupport_finset_sum {α : Type*} {n : ℕ+}
    (s : Finset α) (f : α → HahnField k ℚ)
    (hf : ∀ a ∈ s, HasDenominatorSupport k n (f a)) :
    HasDenominatorSupport k n (∑ a ∈ s, f a) := by
  classical
  revert hf
  refine Finset.induction_on s ?empty ?insert
  · intro hf
    simpa using hasDenominatorSupport_zero k n
  · intro a s has ih hf
    rw [Finset.sum_insert has]
    exact hasDenominatorSupport_add k (hf a (by simp)) (ih (by
      intro b hb
      exact hf b (by simp [hb])))

theorem hasDenominatorSupport_eval {n : ℕ+}
    (P : Polynomial (HahnField k ℚ)) {x : HahnField k ℚ}
    (hcoeff : ∀ i : ℕ, HasDenominatorSupport k n (P.coeff i))
    (hx : HasDenominatorSupport k n x) :
    HasDenominatorSupport k n (P.eval x) := by
  rw [Polynomial.eval_eq_sum_range]
  apply hasDenominatorSupport_finset_sum k
  intro i hi
  exact hasDenominatorSupport_mul k (hcoeff i) (hasDenominatorSupport_pow k hx i)

theorem hasDenominatorSupport_oddClusterStep_target
    [LinearOrder k] [IsStrictOrderedRing k]
    {F : Polynomial (HahnField.valuationSubring k ℚ)} {m : ℕ}
    {y y' : HahnField.valuationSubring k ℚ} {n : ℕ+}
    (hm : 0 < m)
    (hcoeff : ∀ i : ℕ,
      HasDenominatorSupport k n (F.coeff i : HahnField k ℚ))
    (hy : HasDenominatorSupport k n (y : HahnField k ℚ))
    (hstep : HahnField.OddClusterStep k ℚ F m y y') :
    HasDenominatorSupport k (n * ⟨m, hm⟩) (y' : HahnField k ℚ) := by
  let m' : ℕ+ := ⟨m, hm⟩
  rcases hstep.2 with
    ⟨γ, δ, c, hδpos, hγpos, hcne, hscale, hy'eq, hval, hstepVal, himprove⟩
  have hEval :
      HasDenominatorSupport k n
        ((F.map (algebraMap (HahnField.valuationSubring k ℚ)
          (HahnField k ℚ))).eval (y : HahnField k ℚ)) := by
    exact hasDenominatorSupport_eval k
      (F.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)))
      (by
        intro i
        rw [Polynomial.coeff_map]
        exact hcoeff i)
      hy
  have hEvalVal :
      HahnField.addVal k ℚ
          ((F.map (algebraMap (HahnField.valuationSubring k ℚ)
            (HahnField k ℚ))).eval (y : HahnField k ℚ)) =
        (γ : WithTop ℚ) := by
    rw [HahnField.eval_map_algebraMap_eq_coe_eval]
    exact hval
  have hEval_ne :
      ((F.map (algebraMap (HahnField.valuationSubring k ℚ)
        (HahnField k ℚ))).eval (y : HahnField k ℚ)) ≠ 0 := by
    intro hzero
    rw [hzero] at hEvalVal
    simp at hEvalVal
  have hseries_ne :
      ofLex
          ((F.map (algebraMap (HahnField.valuationSubring k ℚ)
            (HahnField k ℚ))).eval (y : HahnField k ℚ)) ≠ 0 := by
    intro hzero
    apply hEval_ne
    simpa using congrArg toLex hzero
  have horderEqTop :
      ((ofLex
          ((F.map (algebraMap (HahnField.valuationSubring k ℚ)
            (HahnField k ℚ))).eval (y : HahnField k ℚ))).order : WithTop ℚ) =
        (γ : WithTop ℚ) := by
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hseries_ne]
    simpa [HahnField.addVal_apply] using hEvalVal
  have horderEq :
      (ofLex
          ((F.map (algebraMap (HahnField.valuationSubring k ℚ)
            (HahnField k ℚ))).eval (y : HahnField k ℚ))).order = γ :=
    WithTop.coe_injective horderEqTop
  have hγden : HasDenominator n γ :=
    horderEq ▸ hasDenominatorSupport_order k hEval hEval_ne
  have hδden : HasDenominator (n * m') δ :=
    hasDenominator_of_nsmul_eq hγden (by simpa [m'] using hscale)
  have hyden : HasDenominatorSupport k (n * m') (y : HahnField k ℚ) :=
    hasDenominatorSupport_mono_den k
      (fun q hq => hasDenominator_mul_right (n' := m') hq) hy
  have hsingle :
      HasDenominatorSupport k (n * m')
        (HahnField.singleOfNonneg k ℚ δ c (le_of_lt hδpos) : HahnField k ℚ) :=
    hasDenominatorSupport_singleOfNonneg k c hδden (le_of_lt hδpos)
  have hadd :
      HasDenominatorSupport k (n * m')
        ((HahnField.singleOfNonneg k ℚ δ c (le_of_lt hδpos) : HahnField k ℚ) +
          (y : HahnField k ℚ)) :=
    hasDenominatorSupport_add k hsingle hyden
  have hy'eqH :
      (y' : HahnField k ℚ) =
        (HahnField.singleOfNonneg k ℚ δ c (le_of_lt hδpos) : HahnField k ℚ) +
          (y : HahnField k ℚ) := by
    exact congrArg (fun z : HahnField.valuationSubring k ℚ =>
      (z : HahnField k ℚ)) hy'eq
  rw [hy'eqH]
  simpa [m'] using hadd

theorem hasDenominatorSupport_inv {n : ℕ+} {x : HahnField k ℚ}
    (hx : HasDenominatorSupport k n x) :
    HasDenominatorSupport k n x⁻¹ := by
  by_cases hzero : x = 0
  · simpa [hzero] using hasDenominatorSupport_zero k n
  · let s : HahnSeries ℚ k := ofLex x
    have hs_ne : s ≠ 0 := by
      intro hs
      exact hzero (by simpa [s] using congrArg toLex hs)
    have horder : HasDenominator n s.order := by
      simpa [s] using hasDenominatorSupport_order k hx hzero
    let y : HahnSeries ℚ k := 1 - HahnSeries.single (-s.order) s.leadingCoeff⁻¹ * s
    have hsingle :
        HasDenominatorSupport k n
          (toLex (HahnSeries.single (-s.order) s.leadingCoeff⁻¹) : HahnField k ℚ) :=
      hasDenominatorSupport_single k s.leadingCoeff⁻¹ (hasDenominator_neg horder)
    have hy : HasDenominatorSupport k n (toLex y : HahnField k ℚ) := by
      simpa [y, s] using
        hasDenominatorSupport_sub k (hasDenominatorSupport_one k n)
          (hasDenominatorSupport_mul k hsingle hx)
    have hypos : 0 < y.orderTop := by
      have hlead : s.leadingCoeff⁻¹ * s.leadingCoeff = 1 :=
        inv_mul_cancel₀ (HahnSeries.leadingCoeff_ne_zero.mpr hs_ne)
      simpa [y] using HahnSeries.unit_aux s hlead (-s.order) (neg_add_cancel s.order)
    intro q hq
    change q ∈ (s⁻¹).support at hq
    rw [HahnSeries.inv_def] at hq
    rcases HahnSeries.support_mul_subset hq with ⟨a, ha, b, hb, hqeq⟩
    have ha_den : HasDenominator n a := by
      exact hsingle a (by
        change a ∈ (HahnSeries.single (-s.order) s.leadingCoeff⁻¹).support
        exact ha)
    have hb_den : HasDenominator n b := by
      have hb_union := HahnSeries.SummableFamily.support_hsum_subset hb
      rcases Set.mem_iUnion.mp hb_union with ⟨m, hbm⟩
      have hpow := hasDenominatorSupport_pow k hy m
      exact hpow b (by
        change b ∈ (y ^ m).support
        simpa [HahnSeries.SummableFamily.powers, hypos, y] using hbm)
    rw [← hqeq]
    exact hasDenominator_add_same ha_den hb_den

theorem hasBoundedDenominatorSupport_one :
    HasBoundedDenominatorSupport k (1 : HahnField k ℚ) := by
  refine ⟨1, ?_⟩
  intro q hq
  change q ∈ (1 : HahnSeries ℚ k).support at hq
  have hq0 : q = 0 := by
    simpa [HahnSeries.support_one] using hq
  rw [hq0]
  exact hasDenominator_zero 1

theorem hasBoundedDenominatorSupport_hahnMonomial {n : ℕ+} {γ : ℚ}
    (hγ : HasDenominator n γ) :
    HasBoundedDenominatorSupport k (HahnField.hahnMonomial k ℚ γ) := by
  refine ⟨n, ?_⟩
  intro q hq
  change q ∈ (HahnSeries.single γ (1 : k)).support at hq
  have hqγ : q = γ := by
    simpa [HahnSeries.support_single_of_ne (one_ne_zero : (1 : k) ≠ 0)] using hq
  rwa [hqγ]

theorem hasBoundedDenominatorSupport_neg {x : HahnField k ℚ}
    (hx : HasBoundedDenominatorSupport k x) :
    HasBoundedDenominatorSupport k (-x) := by
  rcases hx with ⟨n, hx⟩
  refine ⟨n, ?_⟩
  intro q hq
  change q ∈ (-(ofLex x)).support at hq
  rw [HahnSeries.support_neg] at hq
  exact hx q hq

theorem hasBoundedDenominatorSupport_add {x y : HahnField k ℚ}
    (hx : HasBoundedDenominatorSupport k x)
    (hy : HasBoundedDenominatorSupport k y) :
    HasBoundedDenominatorSupport k (x + y) := by
  rcases hx with ⟨n, hx⟩
  rcases hy with ⟨n', hy⟩
  refine ⟨n * n', ?_⟩
  intro q hq
  change q ∈ (ofLex x + ofLex y).support at hq
  rcases HahnSeries.support_add_subset (ofLex x) (ofLex y) hq with hqx | hqy
  · exact hasDenominator_mul_right (n' := n') (hx q hqx)
  · simpa [mul_comm] using (hasDenominator_mul_right (n' := n) (hy q hqy))

theorem hasBoundedDenominatorSupport_finset_sum_of_boundedSupport {α : Type*}
    (s : Finset α) (f : α → HahnField k ℚ)
    (hf : ∀ a ∈ s, HasBoundedDenominatorSupport k (f a)) :
    HasBoundedDenominatorSupport k (∑ a ∈ s, f a) := by
  classical
  revert hf
  refine Finset.induction_on s ?empty ?insert
  · intro hf
    simpa using hasBoundedDenominatorSupport_zero k
  · intro a s has ih hf
    rw [Finset.sum_insert has]
    exact hasBoundedDenominatorSupport_add k (hf a (by simp)) (ih (by
      intro b hb
      exact hf b (by simp [hb])))

theorem hasBoundedDenominatorSupport_mul {x y : HahnField k ℚ}
    (hx : HasBoundedDenominatorSupport k x)
    (hy : HasBoundedDenominatorSupport k y) :
    HasBoundedDenominatorSupport k (x * y) := by
  rcases hx with ⟨n, hx⟩
  rcases hy with ⟨n', hy⟩
  refine ⟨n * n', ?_⟩
  intro q hq
  change q ∈ (ofLex x * ofLex y).support at hq
  rcases HahnSeries.support_mul_subset hq with ⟨a, ha, b, hb, hqeq⟩
  rw [← hqeq]
  exact hasDenominator_add (hx a ha) (hy b hb)

theorem hasBoundedDenominatorSupport_pow {x : HahnField k ℚ}
    (hx : HasBoundedDenominatorSupport k x) :
    ∀ m : ℕ, HasBoundedDenominatorSupport k (x ^ m)
  | 0 => by simpa using hasBoundedDenominatorSupport_one k
  | m + 1 => by
      rw [pow_succ]
      exact hasBoundedDenominatorSupport_mul k (hasBoundedDenominatorSupport_pow hx m) hx

theorem hasBoundedDenominatorSupport_inv {x : HahnField k ℚ}
    (hx : HasBoundedDenominatorSupport k x) :
    HasBoundedDenominatorSupport k x⁻¹ := by
  rcases hx with ⟨n, hx⟩
  exact ⟨n, hasDenominatorSupport_inv k hx⟩

end

end Puiseux

end HahnKaplanskyRealClosedness
