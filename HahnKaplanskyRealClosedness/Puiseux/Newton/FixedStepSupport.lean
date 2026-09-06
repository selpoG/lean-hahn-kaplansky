/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Support.FiniteLevel
import HahnKaplanskyRealClosedness.Puiseux.Support.Core
import HahnKaplanskyRealClosedness.Puiseux.Valuation.RootPredicates
import HahnKaplanskyRealClosedness.SimpleCluster.Fixed.Chain.Terminal

/-!
# Bounded support along fixed-lift odd-cluster chains

The Hahn fixed-step engine is independent of the Puiseux denominator lattice.  This file records
the support bridge for the infinite correction: bounded support of the candidate gives a common
denominator for all step values, because each step exponent occurs in the correction with its
nonzero step coefficient.  Finite-source support remains available as a separate estimate, but
its denominator may grow with the number of steps.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

omit [LinearOrder k] [IsStrictOrderedRing k] in
private theorem hasDenominatorSupportPolynomial_mul_of_common_denominator
    {F G : Polynomial (HahnField k ℚ)} {n : ℕ+}
    (hF : ∀ i : ℕ, HasDenominatorSupport k n (F.coeff i))
    (hG : ∀ i : ℕ, HasDenominatorSupport k n (G.coeff i)) :
    ∀ i : ℕ, HasDenominatorSupport k n ((F * G).coeff i) := by
  intro i
  rw [Polynomial.coeff_mul]
  apply hasDenominatorSupport_finset_sum k
  intro p _hp
  exact hasDenominatorSupport_mul k (hF p.1) (hG p.2)

omit [LinearOrder k] [IsStrictOrderedRing k] in
private theorem hasDenominatorSupportPolynomial_pow_of_common_denominator
    {F : Polynomial (HahnField k ℚ)} {n : ℕ+}
    (hF : ∀ i : ℕ, HasDenominatorSupport k n (F.coeff i)) :
    ∀ m : ℕ, ∀ i : ℕ, HasDenominatorSupport k n ((F ^ m).coeff i)
  | 0, i => by
      simp only [pow_zero, Polynomial.coeff_one]
      by_cases hi : i = 0
      · subst i
        exact hasDenominatorSupport_one k n
      · simp [hi, hasDenominatorSupport_zero]
  | m + 1, i => by
      rw [pow_succ]
      exact hasDenominatorSupportPolynomial_mul_of_common_denominator k
        (hasDenominatorSupportPolynomial_pow_of_common_denominator hF m)
        hF i

omit [LinearOrder k] [IsStrictOrderedRing k] in
private theorem hasDenominatorSupportPolynomial_X_add_C_of_common_denominator
    {n : ℕ+} {y : HahnField k ℚ}
    (hy : HasDenominatorSupport k n y) :
    ∀ i : ℕ, HasDenominatorSupport k n
      ((Polynomial.X + Polynomial.C y).coeff i) := by
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C] using hy
  · by_cases hi1 : i = 1
    · subst i
      simpa [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C] using
        hasDenominatorSupport_one k n
    · rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
      have hne : 1 ≠ i := Ne.symm hi1
      simp [hi0, hne, hasDenominatorSupport_zero]

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem hasDenominatorSupportPolynomial_comp_X_add_C_of_common_denominator
    {F : Polynomial (HahnField k ℚ)} {n : ℕ+}
    (hF : ∀ i : ℕ, HasDenominatorSupport k n (F.coeff i))
    {y : HahnField k ℚ} (hy : HasDenominatorSupport k n y) :
    ∀ i : ℕ, HasDenominatorSupport k n
      ((F.comp (Polynomial.X + Polynomial.C y)).coeff i) := by
  have hXaddC := hasDenominatorSupportPolynomial_X_add_C_of_common_denominator k hy
  rw [Polynomial.comp_eq_sum_left]
  intro i
  rw [Polynomial.coeff_sum]
  apply hasDenominatorSupport_finset_sum k
  intro j _hj
  change HasDenominatorSupport k n
    ((Polynomial.C (F.coeff j) * (Polynomial.X + Polynomial.C y) ^ j).coeff i)
  rw [Polynomial.coeff_mul]
  apply hasDenominatorSupport_finset_sum k
  intro p _hp
  rw [Polynomial.coeff_C]
  by_cases hp0 : p.1 = 0
  · rw [if_pos hp0]
    exact hasDenominatorSupport_mul k (hF j)
      (hasDenominatorSupportPolynomial_pow_of_common_denominator k hXaddC j p.2)
  · rw [if_neg hp0]
    simpa using hasDenominatorSupport_zero k n

private theorem coeff_pred_ne_zero_of_rootMultiplicity_eq_natDegree
    [IsRealClosed k]
    {p : Polynomial k} {c : k} {m : ℕ}
    (hp : p ≠ 0) (hdeg : p.natDegree = m)
    (hmul : p.rootMultiplicity c = m) (hc : c ≠ 0) (hmpos : 0 < m) :
    p.coeff (m - 1) ≠ 0 := by
  have hfac : ∃ u : k, u ≠ 0 ∧
      p = Polynomial.C u * (Polynomial.X - Polynomial.C c) ^ m := by
    have hdvd : (Polynomial.X - Polynomial.C c) ^ m ∣ p := by
      rw [← hmul]
      exact Polynomial.pow_rootMultiplicity_dvd p c
    rcases hdvd with ⟨q, hq⟩
    have hq0 : q ≠ 0 := by
      intro hzero
      apply hp
      simpa [hzero] using hq
    have hpow0 : (Polynomial.X - Polynomial.C c) ^ m ≠ 0 :=
      pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c)
    have hqdeg : q.natDegree = 0 := by
      have hsum : m + q.natDegree = p.natDegree := by
        rw [hq, Polynomial.natDegree_mul hpow0 hq0,
          Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
        simp
      omega
    let u := q.coeff 0
    have hqC : q = Polynomial.C u := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
    have hu : u ≠ 0 := by
      intro hu0
      apply hq0
      rw [hqC, hu0, Polynomial.C_0]
    exact ⟨u, hu, by rw [hq, hqC, mul_comm]⟩
  rcases hfac with ⟨u, hu, hfac⟩
  rw [hfac]
  have hcoeffpow :
      ((Polynomial.X - Polynomial.C c) ^ m).coeff (m - 1) =
        (m : k) * (-c) := by
    rw [show Polynomial.X - Polynomial.C c =
        Polynomial.X + Polynomial.C (-c) by simp [sub_eq_add_neg]]
    rw [Polynomial.coeff_X_add_C_pow]
    have hchoose : m.choose (m - 1) = m := by
      rw [show m = (m - 1) + 1 by omega]
      simp
    rw [hchoose]
    have hpow : m - (m - 1) = 1 := by omega
    rw [hpow]
    simp [mul_comm]
  rw [Polynomial.coeff_C_mul, hcoeffpow]
  have hmcast : (m : k) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  exact mul_ne_zero hu (mul_ne_zero hmcast (neg_ne_zero.mpr hc))

theorem hasDenominator_newtonStep_of_full_initial_rootMultiplicity
    [IsRealClosed k]
    {F : Polynomial (HahnField.valuationSubring k ℚ)} {m : ℕ}
    {N : ℕ+} {y : HahnField.valuationSubring k ℚ} {γ δ : ℚ}
    (hmpos : 0 < m)
    (hcoeff : ∀ i : ℕ,
      HasDenominatorSupport k N (F.coeff i : HahnField k ℚ))
    (hy : HasDenominatorSupport k N (y : HahnField k ℚ))
    (hδpos : 0 < δ) (hscale : m • δ = γ)
    (hunit : IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m))
    {c : k} (hc : c ≠ 0)
    (hmul : (HahnField.newtonInitialPolynomial k ℚ
      ((F.comp (Polynomial.X + Polynomial.C y)).map
        (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)))
      δ γ).rootMultiplicity c = m) :
    HasDenominator N δ := by
  let G : Polynomial (HahnField k ℚ) :=
    (F.comp (Polynomial.X + Polynomial.C y)).map
      (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))
  have hGcoeff : ∀ i : ℕ, HasDenominatorSupport k N (G.coeff i) := by
    intro i
    have hFmap : ∀ j : ℕ,
        HasDenominatorSupport k N
          ((F.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).coeff j) := by
      intro j
      rw [Polynomial.coeff_map]
      exact hcoeff j
    have hcomp := hasDenominatorSupportPolynomial_comp_X_add_C_of_common_denominator
      (k := k) hFmap (y := (y : HahnField k ℚ)) hy i
    simpa [G, Polynomial.map_comp, Algebra.algebraMap_ofSubsemiring_apply] using hcomp
  have hmem : m ∈ HahnField.newtonInitialSupport k ℚ G δ γ := by
    dsimp [G]
    exact HahnField.main_mem_newtonInitialSupport_map_comp_X_add_C_of_unit_scale
      k ℚ hunit hscale
  have hpne : HahnField.newtonInitialPolynomial k ℚ G δ γ ≠ 0 :=
    HahnField.newtonInitialPolynomial_ne_zero_of_initialSupport_nonempty k ℚ G δ γ ⟨m, hmem⟩
  have hdeg : (HahnField.newtonInitialPolynomial k ℚ G δ γ).natDegree = m := by
    dsimp [G]
    exact HahnField.natDegree_newtonInitialPolynomial_map_comp_X_add_C_eq_of_unit_scale
      k ℚ hδpos hunit hscale
  have hpred :
      (HahnField.newtonInitialPolynomial k ℚ G δ γ).coeff (m - 1) ≠ 0 :=
    coeff_pred_ne_zero_of_rootMultiplicity_eq_natDegree (k := k) hpne hdeg hmul hc hmpos
  have hpred_mem : m - 1 ∈ HahnField.newtonInitialSupport k ℚ G δ γ := by
    by_contra hnot
    apply hpred
    rw [HahnField.coeff_newtonInitialPolynomial,
      HahnField.newtonInitialCoeff_of_notMem k ℚ G δ γ hnot]
  have hpred_eq :
      (HahnField.newtonInitialPolynomial k ℚ G δ γ).coeff (m - 1) =
        (ofLex (G.coeff (m - 1))).coeff (γ - (m - 1) • δ) := by
    rw [HahnField.coeff_newtonInitialPolynomial,
      HahnField.newtonInitialCoeff_of_mem k ℚ G δ γ hpred_mem]
  have hcoeff_ne :
      (ofLex (G.coeff (m - 1))).coeff (γ - (m - 1) • δ) ≠ 0 := by
    intro hzero
    apply hpred
    rw [hpred_eq, hzero]
  have hden : HasDenominator N (γ - (m - 1) • δ) :=
    hGcoeff (m - 1) (γ - (m - 1) • δ) (by
      rw [HahnSeries.mem_support]
      exact hcoeff_ne)
  have heq : γ - (m - 1) • δ = δ := by
    rw [nsmul_eq_mul] at hscale ⊢
    rw [← hscale]
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  rw [heq] at hden
  exact hden

def FixedStepFullInitialRootMultiplicity
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start) : Prop :=
  ∀ n : ℕ,
    ∃ c : k, c ≠ 0 ∧
      (HahnField.newtonInitialPolynomial k ℚ
        ((C.liftData.lift.comp
          (Polynomial.X + Polynomial.C (C.source n).1)).map
          (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)))
        (C.stepValue k ℚ n) (m • C.stepValue k ℚ n)).rootMultiplicity c = m

/- A fixed-level chain stays in one denominator lattice once every selected Newton initial root
   has the full multiplicity of the fixed cluster.  This is the induction step that turns the
   local Newton denominator calculation above into a uniform source bound. -/
theorem hasDenominatorSupport_fixedStepChainFromData_source_of_full_initial_rootMultiplicity
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    {N : ℕ+}
    (hcoeff : ∀ i : ℕ,
      HasDenominatorSupport k N (C.liftData.lift.coeff i : HahnField k ℚ))
    (hstart : HasDenominatorSupport k N (start : HahnField k ℚ))
    (hfull : FixedStepFullInitialRootMultiplicity (k := k) C) :
    ∀ n : ℕ, HasDenominatorSupport k N ((C.source n).1 : HahnField k ℚ) := by
  intro n
  induction n with
  | zero =>
      simpa [C.start_source] using hstart
  | succ n ih =>
      rcases hfull n with ⟨c, hc, hmul⟩
      have hunit : IsUnit ((C.liftData.lift.comp
          (Polynomial.X + Polynomial.C (C.source n).1)).coeff m) :=
        HahnField.isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal
          k ℚ C.liftData.unit (C.source n).property
      have hstep : HasDenominator N (C.stepValue k ℚ n) :=
        hasDenominator_newtonStep_of_full_initial_rootMultiplicity
          (k := k) (F := C.liftData.lift) (m := m) (N := N)
          (y := C.source n) (γ := m • C.stepValue k ℚ n)
          (δ := C.stepValue k ℚ n)
          (Nat.zero_lt_one.trans C.one_lt) hcoeff ih
          (C.stepValue_pos k ℚ n) rfl hunit
          (c := c) hc hmul
      have hsingle : HasDenominatorSupport k N
          (HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
            (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) : HahnField k ℚ) :=
        hasDenominatorSupport_singleOfNonneg k (C.stepCoeff k ℚ n)
          hstep (le_of_lt (C.stepValue_pos k ℚ n))
      have hsource :
          ((C.source (n + 1)).1 : HahnField k ℚ) =
            ((C.source n).1 : HahnField k ℚ) +
              (HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
                (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) : HahnField k ℚ) := by
        have hdiff := C.stepDiff_eq_singleOfNonneg k ℚ n
        have hdiff' :
            (C.source (n + 1)).1 =
              (C.source n).1 +
                HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
                  (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) :=
          eq_add_of_sub_eq' hdiff
        exact congrArg (fun z : HahnField.valuationSubring k ℚ =>
          (z : HahnField k ℚ)) hdiff'
      rw [hsource]
      exact hasDenominatorSupport_add k ih hsingle

/- The denominator of one Newton correction is forced by the current source level.  This is the
   local denominator calculation used by the finite-prefix propagation below. -/
theorem hasDenominator_fixedStepChainFromData_stepValue_of_source_at
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    {N : ℕ+}
    (hcoeff : ∀ i : ℕ,
      HasDenominatorSupport k N (C.liftData.lift.coeff i : HahnField k ℚ))
    (n : ℕ)
    (hsource : HasDenominatorSupport k N ((C.source n).1 : HahnField k ℚ)) :
    HasDenominator (N * ⟨m, Nat.zero_lt_one.trans C.one_lt⟩)
      (C.stepValue k ℚ n) := by
  let m' : ℕ+ := ⟨m, Nat.zero_lt_one.trans C.one_lt⟩
  have hnext : HasDenominatorSupport k (N * m')
      ((C.source (n + 1)).1 : HahnField k ℚ) := by
    exact hasDenominatorSupport_oddClusterStep_target k
      (Nat.zero_lt_one.trans C.one_lt) hcoeff hsource (C.step n)
  have hcurrent : HasDenominatorSupport k (N * m')
      ((C.source n).1 : HahnField k ℚ) := by
    exact hasDenominatorSupport_mono_den k
      (fun q hq => hasDenominator_mul_right (n' := m') hq) hsource
  let z : HahnField k ℚ :=
    ((C.source (n + 1)).1 : HahnField k ℚ) - ((C.source n).1 : HahnField k ℚ)
  have hz : HasDenominatorSupport k (N * m') z := by
    exact hasDenominatorSupport_sub k hnext hcurrent
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hval :
        HahnField.addVal k ℚ z = (C.stepValue k ℚ n : WithTop ℚ) := by
      simpa [z] using C.addVal_stepDiff_eq_stepValue k ℚ n
    rw [hz0, AddValuation.map_zero] at hval
    simp at hval
  have hz_series_ne : ofLex z ≠ 0 := by
    intro hz0
    apply hz_ne
    simpa [z] using congrArg toLex hz0
  have horder : HasDenominator (N * m') (ofLex z).order :=
    hasDenominatorSupport_order k hz hz_ne
  have horderTop :
      ((ofLex z).order : WithTop ℚ) = (C.stepValue k ℚ n : WithTop ℚ) := by
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hz_series_ne]
    simpa [z, HahnField.addVal_apply] using C.addVal_stepDiff_eq_stepValue k ℚ n
  have horderEq : (ofLex z).order = C.stepValue k ℚ n :=
    WithTop.coe_eq_coe.mp horderTop
  rw [horderEq] at horder
  simpa [m'] using horder

/- A finite prefix has an explicit denominator level. The level grows by the multiplicity at
   each step; the full-multiplicity fixed-level route in `LowerEdgeFixedLevel` supplies the
   uniform-level argument for the infinite continuation. -/
theorem hasDenominatorSupport_fixedStepChainFromData_source_prefix
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    {N M : ℕ+}
    (hM : (M : ℕ) = m)
    (hcoeff : ∀ i : ℕ,
      HasDenominatorSupport k N (C.liftData.lift.coeff i : HahnField k ℚ))
    (hstart : HasDenominatorSupport k N (start : HahnField k ℚ)) :
    ∀ n : ℕ,
      HasDenominatorSupport k
        (N * M ^ n)
        ((C.source n).1 : HahnField k ℚ) := by
  have hstepFactor : (⟨m, Nat.zero_lt_one.trans C.one_lt⟩ : ℕ+) = M := by
    apply Subtype.ext
    exact hM.symm
  intro n
  induction n with
  | zero =>
      simpa [C.start_source] using hstart
  | succ n ih =>
      have hcoeff' : ∀ i : ℕ,
          HasDenominatorSupport k (N * M ^ n)
            (C.liftData.lift.coeff i : HahnField k ℚ) := by
        intro i
        exact hasDenominatorSupport_mono_den k
          (fun q hq => hasDenominator_mul_right (n' := M ^ n) hq) (hcoeff i)
      have hstep : HasDenominator (N * M ^ (n + 1))
          (C.stepValue k ℚ n) := by
        have hstep' := hasDenominator_fixedStepChainFromData_stepValue_of_source_at
          (k := k) C hcoeff' n ih
        simpa [hstepFactor, pow_succ, mul_assoc] using hstep'
      have hsingle : HasDenominatorSupport k (N * M ^ (n + 1))
          (HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
            (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) : HahnField k ℚ) :=
        hasDenominatorSupport_singleOfNonneg k (C.stepCoeff k ℚ n)
          hstep (le_of_lt (C.stepValue_pos k ℚ n))
      have hsource :
          ((C.source (n + 1)).1 : HahnField k ℚ) =
            ((C.source n).1 : HahnField k ℚ) +
              (HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
                (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) : HahnField k ℚ) := by
        have hdiff := C.stepDiff_eq_singleOfNonneg k ℚ n
        have hdiff' :
            (C.source (n + 1)).1 =
              (C.source n).1 +
                HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
                  (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) :=
          eq_add_of_sub_eq' hdiff
        exact congrArg (fun z : HahnField.valuationSubring k ℚ =>
          (z : HahnField k ℚ)) hdiff'
      rw [hsource]
      have hih' : HasDenominatorSupport k (N * M ^ (n + 1))
          ((C.source n).1 : HahnField k ℚ) := by
        exact hasDenominatorSupport_mono_den k
          (fun q hq => by
            rw [pow_succ]
            simpa [mul_assoc] using (hasDenominator_mul_right (n' := M) hq)) ih
      exact hasDenominatorSupport_add k hih' hsingle

/- A fixed denominator for every source also controls every Newton step.  The
   valuation of a step is the order of the corresponding source difference. -/
theorem hasCommonDenominator_fixedStepChainFromData_stepValue_of_source
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    {N : ℕ+}
    (hsource : ∀ n : ℕ,
      HasDenominatorSupport k N ((C.source n).1 : HahnField k ℚ)) :
    ∀ n : ℕ, HasDenominator N (C.stepValue k ℚ n) := by
  intro n
  let z : HahnField k ℚ :=
    ((C.source (n + 1)).1 : HahnField k ℚ) - ((C.source n).1 : HahnField k ℚ)
  have hz : HasDenominatorSupport k N z := by
    exact hasDenominatorSupport_sub k (hsource (n + 1)) (hsource n)
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hval :
        HahnField.addVal k ℚ z = (C.stepValue k ℚ n : WithTop ℚ) := by
      simpa [z] using C.addVal_stepDiff_eq_stepValue k ℚ n
    rw [hz0, AddValuation.map_zero] at hval
    simp at hval
  have hz_series_ne : ofLex z ≠ 0 := by
    intro hz0
    apply hz_ne
    simpa [z] using congrArg toLex hz0
  have horder : HasDenominator N (ofLex z).order :=
    hasDenominatorSupport_order k hz hz_ne
  have horderTop :
      ((ofLex z).order : WithTop ℚ) = (C.stepValue k ℚ n : WithTop ℚ) := by
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hz_series_ne]
    simpa [z, HahnField.addVal_apply] using C.addVal_stepDiff_eq_stepValue k ℚ n
  have horderEq : (ofLex z).order = C.stepValue k ℚ n :=
    WithTop.coe_eq_coe.mp horderTop
  rw [horderEq] at horder
  exact horder

/- A common denominator for the correction exponents also controls every finite source.  This is
   the direction used by the Puiseux continuation contract: the Newton step supplies the
   exponent, while the source is reconstructed by a finite sum of singleton corrections. -/
theorem hasBoundedDenominatorSupport_fixedStepChainFromData_source_of_stepValue
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    {N : ℕ+}
    (hstart : HasDenominatorSupport k N (start : HahnField k ℚ))
    (hstep : ∀ n : ℕ, HasDenominator N (C.stepValue k ℚ n)) :
    ∀ n : ℕ, HasDenominatorSupport k N ((C.source n).1 : HahnField k ℚ) := by
  intro n
  induction n with
  | zero =>
      simpa [C.start_source] using hstart
  | succ n ih =>
      have hsingle : HasDenominatorSupport k N
          (HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
            (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) :
            HahnField k ℚ) :=
        hasDenominatorSupport_singleOfNonneg k (C.stepCoeff k ℚ n)
          (hstep n) (le_of_lt (C.stepValue_pos k ℚ n))
      have hsource :
          ((C.source (n + 1)).1 : HahnField k ℚ) =
            ((C.source n).1 : HahnField k ℚ) +
              (HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
                (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) :
                HahnField k ℚ) := by
        have hdiff := C.stepDiff_eq_singleOfNonneg k ℚ n
        have hdiff' :
            (C.source (n + 1)).1 =
              (C.source n).1 +
                HahnField.singleOfNonneg k ℚ (C.stepValue k ℚ n)
                  (C.stepCoeff k ℚ n) (le_of_lt (C.stepValue_pos k ℚ n)) :=
          eq_add_of_sub_eq' hdiff
        exact congrArg (fun z : HahnField.valuationSubring k ℚ =>
          (z : HahnField k ℚ)) hdiff'
      rw [hsource]
      exact hasDenominatorSupport_add k ih hsingle

/- The source-level denominator condition is the primitive support obligation for a
   fixed-step candidate.  It is deliberately stated separately from the chain
   construction: the remaining Newton--Puiseux work is to produce this uniform
   source level. -/
theorem hasBoundedDenominatorSupport_fixedStepChainFromData_candidate_of_source
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    (hsource : ∃ N : ℕ+, ∀ n : ℕ,
      HasDenominatorSupport k N ((C.source n).1 : HahnField k ℚ)) :
    HasBoundedDenominatorSupport k (C.candidate k ℚ : HahnField k ℚ) := by
  rcases hsource with ⟨N, hsource⟩
  have hstep : ∀ n : ℕ, HasDenominator N (C.stepValue k ℚ n) :=
    hasCommonDenominator_fixedStepChainFromData_stepValue_of_source
      (k := k) C hsource
  have hcorrection : HasDenominatorSupport k N
      (toLex (C.correctionHahnSeries k ℚ) : HahnField k ℚ) := by
    change HasDenominatorSupport k N
      (toLex ((C.correctionFamily k ℚ).hsum) : HahnField k ℚ)
    exact hasDenominatorSupport_hsum k (C.correctionFamily k ℚ) (fun n => by
      rw [C.correctionFamily_apply k ℚ n]
      exact hasDenominatorSupport_single k (C.stepCoeff k ℚ n) (hstep n))
  have hstart : HasDenominatorSupport k N (start : HahnField k ℚ) := by
    simpa [C.start_source] using hsource 0
  refine ⟨N, ?_⟩
  change HasDenominatorSupport k N
    ((start : HahnField k ℚ) + toLex (C.correctionHahnSeries k ℚ))
  exact hasDenominatorSupport_add k hstart hcorrection

theorem
    candidate_bounded_of_full_initial_rootMultiplicity
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    {N : ℕ+}
    (hcoeff : ∀ i : ℕ,
      HasDenominatorSupport k N (C.liftData.lift.coeff i : HahnField k ℚ))
    (hstart : HasDenominatorSupport k N (start : HahnField k ℚ))
    (hfull : FixedStepFullInitialRootMultiplicity (k := k) C) :
    HasBoundedDenominatorSupport k (C.candidate k ℚ : HahnField k ℚ) := by
  apply hasBoundedDenominatorSupport_fixedStepChainFromData_candidate_of_source
    (k := k) C
  exact ⟨N, hasDenominatorSupport_fixedStepChainFromData_source_of_full_initial_rootMultiplicity
    (k := k) C hcoeff hstart hfull⟩

theorem boundedRootInMaximalIdeal_of_fixedStepChainFromData_candidate_isRoot_of_bounded
    [IsRealClosed k]
    {F : Polynomial (HahnField k ℚ)} {m : ℕ} {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    (hcandidate : HasBoundedDenominatorSupport k (C.candidate k ℚ : HahnField k ℚ))
    (hroot :
      (C.liftData.lift.map
        (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).IsRoot
        (C.candidate k ℚ : HahnField k ℚ)) :
    BoundedRootInMaximalIdeal k C.liftData.lift := by
  refine ⟨C.candidate k ℚ, C.candidate_mem_maximalIdeal k ℚ, hcandidate, ?_⟩
  rw [Polynomial.IsRoot] at hroot ⊢
  rw [HahnField.eval_map_algebraMap_eq_coe_eval] at hroot
  exact Subtype.ext hroot

end

end Puiseux

end HahnKaplanskyRealClosedness
