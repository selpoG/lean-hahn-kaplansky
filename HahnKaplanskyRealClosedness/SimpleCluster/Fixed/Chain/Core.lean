/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.SimpleCluster.Fixed.Foundation

/-!
# Fixed chain construction and terminal-from algebra
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

theorem exists_KOddClusterFixedStepChainFromData_of_fixedLiftWithRootBelow_no_positiveRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hstep : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (hno : ¬ PositiveHahnRoot k Γ F)
    (hbranch : KTranslatedSameMultiplicityZeroBranch k Γ F m)
    (D : KOddClusterLiftData k Γ F m)
    (start : valuationSubring k Γ)
    (hstart : start ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    ∃ C : KOddClusterFixedStepChainFromData k Γ F m start, C.liftData = D := by
  let hD := hstep hbelow hbranch D
  let U : ℕ →
      {A : valuationSubring k Γ // A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)} :=
    Nat.rec
      ⟨start, hstart⟩
      (fun _ S =>
        let hnext : ∃ A' : valuationSubring k Γ, OddClusterStep k Γ D.lift m S.1 A' := by
          rcases hD S.1 S.2 with hroot | hnext
          · exact False.elim (hno hroot)
          · exact hnext
        ⟨Classical.choose hnext, (Classical.choose_spec hnext).mem_maximalIdeal⟩)
  refine ⟨
    { one_lt := hbranch.one_lt
      liftData := D
      source := U
      start_source := rfl
      step := ?_ }, rfl⟩
  intro n
  dsimp [U]
  exact Classical.choose_spec _

theorem KOddClusterFixedStepChainFromData.exists_stepDiff_eq_singleOfNonneg
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    ∃ δ : Γ, ∃ c : k, ∃ hδpos : 0 < δ,
      c ≠ 0 ∧
        (C.source (n + 1)).1 - (C.source n).1 =
          singleOfNonneg k Γ δ c (le_of_lt hδpos) ∧
          addVal k Γ (((C.source (n + 1)).1 - (C.source n).1 : valuationSubring k Γ) :
            HahnField k Γ) =
            (δ : WithTop Γ) :=
  (C.step n).exists_stepDiff_eq_singleOfNonneg k Γ

noncomputable def KOddClusterFixedStepChainFromData.stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) : Γ :=
  Classical.choose (C.exists_stepDiff_eq_singleOfNonneg k Γ n)

noncomputable def KOddClusterFixedStepChainFromData.stepCoeff
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) : k :=
  Classical.choose (Classical.choose_spec (C.exists_stepDiff_eq_singleOfNonneg k Γ n))

theorem KOddClusterFixedStepChainFromData.stepValue_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    0 < C.stepValue k Γ n := by
  let hdiff := C.exists_stepDiff_eq_singleOfNonneg k Γ n
  exact (Classical.choose_spec (Classical.choose_spec hdiff)).1

theorem KOddClusterFixedStepChainFromData.stepCoeff_ne_zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    C.stepCoeff k Γ n ≠ 0 := by
  let hdiff := C.exists_stepDiff_eq_singleOfNonneg k Γ n
  exact (Classical.choose_spec (Classical.choose_spec hdiff)).2.1

theorem KOddClusterFixedStepChainFromData.stepDiff_eq_singleOfNonneg
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.source (n + 1)).1 - (C.source n).1 =
      singleOfNonneg k Γ (C.stepValue k Γ n) (C.stepCoeff k Γ n)
        (le_of_lt (C.stepValue_pos k Γ n)) := by
  let hdiff := C.exists_stepDiff_eq_singleOfNonneg k Γ n
  exact (Classical.choose_spec (Classical.choose_spec hdiff)).2.2.1

theorem KOddClusterFixedStepChainFromData.addVal_stepDiff_eq_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    addVal k Γ (((C.source (n + 1)).1 - (C.source n).1 : valuationSubring k Γ) :
      HahnField k Γ) =
      (C.stepValue k Γ n : WithTop Γ) := by
  let hdiff := C.exists_stepDiff_eq_singleOfNonneg k Γ n
  exact (Classical.choose_spec (Classical.choose_spec hdiff)).2.2.2

noncomputable def KOddClusterFixedStepChainFromData.tailFrom
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    KOddClusterFixedStepChainFromData k Γ F m (C.source n).1 where
  one_lt := C.one_lt
  liftData := C.liftData
  source j := C.source (n + j)
  start_source := by simp
  step j := by simpa [Nat.add_assoc] using C.step (n + j)

theorem KOddClusterFixedStepChainFromData.tailFrom_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n j : ℕ) :
    (C.tailFrom k Γ n).stepValue k Γ j = C.stepValue k Γ (n + j) := by
  have htail := (C.tailFrom k Γ n).addVal_stepDiff_eq_stepValue k Γ j
  have horig := C.addVal_stepDiff_eq_stepValue k Γ (n + j)
  have htail' :
      addVal k Γ
          (((C.source (n + j + 1)).1 - (C.source (n + j)).1 :
              valuationSubring k Γ) : HahnField k Γ) =
        ((C.tailFrom k Γ n).stepValue k Γ j : WithTop Γ) := by
    simpa [KOddClusterFixedStepChainFromData.tailFrom, Nat.add_assoc] using htail
  rw [horig] at htail'
  exact WithTop.coe_injective htail'.symm

theorem KOddClusterFixedStepChainFromData.evalValue_eq_nsmul_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    addVal k Γ ((C.liftData.lift.eval (C.source n).1 : valuationSubring k Γ) :
      HahnField k Γ) =
      (m • C.stepValue k Γ n : WithTop Γ) := by
  rcases (C.step n).exists_step_value_scales_to_eval_value k Γ with
    ⟨γ, δ, hval, hstepVal, hscale⟩
  have hstepVal' := C.addVal_stepDiff_eq_stepValue k Γ n
  rw [hstepVal'] at hstepVal
  have hδ : δ = C.stepValue k Γ n :=
    WithTop.coe_injective hstepVal.symm
  rw [← hscale, hδ] at hval
  simpa using hval

theorem KOddClusterFixedStepChainFromData.source_eval_addVal_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.stepValue k Γ n : WithTop Γ) ≤
      addVal k Γ
        ((C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          ((C.source n).1 : HahnField k Γ)) := by
  rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) C.liftData.lift
    (C.source n).1]
  rw [C.evalValue_eq_nsmul_stepValue k Γ n]
  have hle : C.stepValue k Γ n ≤ m • C.stepValue k Γ n :=
    le_self_nsmul (le_of_lt (C.stepValue_pos k Γ n))
      (Nat.ne_of_gt (zero_lt_one.trans C.one_lt))
  simpa [WithTop.coe_nsmul] using (show
    (C.stepValue k Γ n : WithTop Γ) ≤
      ((m • C.stepValue k Γ n : Γ) : WithTop Γ) from by
        exact_mod_cast hle)

theorem KOddClusterFixedStepChainFromData.source_eval_addVal_eq_nsmul_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    addVal k Γ
        ((C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          ((C.source n).1 : HahnField k Γ)) =
      (m • C.stepValue k Γ n : WithTop Γ) := by
  rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) C.liftData.lift
    (C.source n).1]
  exact C.evalValue_eq_nsmul_stepValue k Γ n

theorem KOddClusterFixedStepChainFromData.evalValue_lt_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    addVal k Γ ((C.liftData.lift.eval (C.source n).1 : valuationSubring k Γ) :
      HahnField k Γ) <
      addVal k Γ ((C.liftData.lift.eval (C.source (n + 1)).1 : valuationSubring k Γ) :
        HahnField k Γ) := by
  rcases (C.step n).exists_eval_value_lt_next k Γ with ⟨γ, hγ, hlt⟩
  rw [hγ]
  exact hlt

theorem KOddClusterFixedStepChainFromData.stepValue_lt_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    C.stepValue k Γ n < C.stepValue k Γ (n + 1) := by
  have hcur := C.evalValue_eq_nsmul_stepValue k Γ n
  have hnext := C.evalValue_eq_nsmul_stepValue k Γ (n + 1)
  have hlt := C.evalValue_lt_succ k Γ n
  rw [hcur, hnext] at hlt
  have hlt' : m • C.stepValue k Γ n < m • C.stepValue k Γ (n + 1) :=
    WithTop.coe_lt_coe.mp hlt
  exact (nsmul_right_strictMono (M := Γ) (Nat.ne_of_gt (zero_lt_one.trans C.one_lt))).lt_iff_lt.mp
    hlt'

theorem KOddClusterFixedStepChainFromData.stepValue_strictMono
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    StrictMono (C.stepValue k Γ) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  exact C.stepValue_lt_succ k Γ n

def KOddClusterFixedStepChainFromData.correctionFamily
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    HahnSeries.SummableFamily Γ k ℕ :=
  singleStrictMonoSummableFamily k Γ
    (C.stepValue k Γ) (C.stepCoeff k Γ) (C.stepValue_strictMono k Γ)

@[simp]
theorem KOddClusterFixedStepChainFromData.correctionFamily_apply
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.correctionFamily k Γ : ℕ → HahnSeries Γ k) n =
      HahnSeries.single (C.stepValue k Γ n) (C.stepCoeff k Γ n) :=
  rfl

def KOddClusterFixedStepChainFromData.correctionHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    HahnSeries Γ k :=
  (C.correctionFamily k Γ).hsum

theorem KOddClusterFixedStepChainFromData.correctionHahnSeries_support_subset_range
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    (C.correctionHahnSeries k Γ).support ⊆ Set.range (C.stepValue k Γ) :=
  singleStrictMonoSummableFamily_support_subset_range k Γ
    (C.stepValue k Γ) (C.stepCoeff k Γ) (C.stepValue_strictMono k Γ)

theorem KOddClusterFixedStepChainFromData.correctionHahnSeries_support_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) {γ : Γ}
    (hγ : γ ∈ (C.correctionHahnSeries k Γ).support) :
    0 < γ := by
  exact support_property_of_subset_range k Γ
    (C.correctionHahnSeries_support_subset_range k Γ) (C.stepValue_pos k Γ) γ hγ

theorem KOddClusterFixedStepChainFromData.correctionHahnSeries_orderTop_nonneg
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    (0 : WithTop Γ) ≤ (C.correctionHahnSeries k Γ).orderTop := by
  rw [HahnSeries.zero_le_orderTop_iff]
  by_cases hzero : C.correctionHahnSeries k Γ = 0
  · simp [hzero]
  · have hcoeff :
        (C.correctionHahnSeries k Γ).coeff (C.correctionHahnSeries k Γ).order ≠ 0 := by
      simpa using (HahnSeries.coeff_order_eq_zero.not.2 hzero)
    have hmem : (C.correctionHahnSeries k Γ).order ∈
        (C.correctionHahnSeries k Γ).support := by
      simpa [Function.mem_support] using hcoeff
    exact le_of_lt (C.correctionHahnSeries_support_pos k Γ hmem)

def KOddClusterFixedStepChainFromData.correctionHahnField
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    HahnField k Γ :=
  toLex (C.correctionHahnSeries k Γ)

def KOddClusterFixedStepChainFromData.correctionValuationSubring
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    valuationSubring k Γ :=
  ⟨C.correctionHahnField k Γ, by
    rw [mem_valuationSubring_iff, addVal_apply]
    simpa [KOddClusterFixedStepChainFromData.correctionHahnField] using
      C.correctionHahnSeries_orderTop_nonneg k Γ⟩

theorem KOddClusterFixedStepChainFromData.correctionHahnSeries_orderTop_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    (0 : WithTop Γ) < (C.correctionHahnSeries k Γ).orderTop := by
  by_cases hzero : C.correctionHahnSeries k Γ = 0
  · simp [hzero]
  · rw [HahnSeries.zero_lt_orderTop_iff hzero]
    have hcoeff :
        (C.correctionHahnSeries k Γ).coeff (C.correctionHahnSeries k Γ).order ≠ 0 := by
      simpa using (HahnSeries.coeff_order_eq_zero.not.2 hzero)
    have hmem :
        (C.correctionHahnSeries k Γ).order ∈ (C.correctionHahnSeries k Γ).support := by
      simpa [Function.mem_support] using hcoeff
    exact C.correctionHahnSeries_support_pos k Γ hmem

theorem KOddClusterFixedStepChainFromData.correctionValuationSubring_mem_maximalIdeal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    C.correctionValuationSubring k Γ ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [mem_maximalIdeal_iff_pos_addVal]
  rw [addVal_apply]
  simpa [KOddClusterFixedStepChainFromData.correctionValuationSubring,
    KOddClusterFixedStepChainFromData.correctionHahnField] using
    C.correctionHahnSeries_orderTop_pos k Γ

def KOddClusterFixedStepChainFromData.correctionPartialHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    HahnSeries Γ k :=
  (Finset.range n).sum
    (fun i => HahnSeries.single (C.stepValue k Γ i) (C.stepCoeff k Γ i))

def KOddClusterFixedStepChainFromData.correctionPartialHahnField
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    HahnField k Γ :=
  toLex (C.correctionPartialHahnSeries k Γ n)

theorem KOddClusterFixedStepChainFromData.sum_stepDiff_range_add_start_eq_source
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (Finset.range n).sum (fun i => (C.source (i + 1)).1 - (C.source i).1) +
      start =
        (C.source n).1 := by
  have hsum := SimpleClusterChain.sum_stepDiff_range_add_zero k Γ
    (fun n => (C.source n).1) n
  simpa [SimpleClusterChain.stepDiff, C.start_source] using hsum

theorem KOddClusterFixedStepChainFromData.correctionPartialHahnField_add_start_eq_source
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    C.correctionPartialHahnField k Γ n + (start : HahnField k Γ) =
      ((C.source n).1 : HahnField k Γ) := by
  have hsum :
      (Finset.range n).sum
          (fun i => (((C.source (i + 1)).1 - (C.source i).1 : valuationSubring k Γ) :
            HahnField k Γ)) +
        (start : HahnField k Γ) =
          ((C.source n).1 : HahnField k Γ) := by
    calc
      (Finset.range n).sum
          (fun i => (((C.source (i + 1)).1 - (C.source i).1 : valuationSubring k Γ) :
            HahnField k Γ)) +
        (start : HahnField k Γ)
          =
            (((Finset.range n).sum
              (fun i => (C.source (i + 1)).1 - (C.source i).1) : valuationSubring k Γ) :
              HahnField k Γ) +
            (start : HahnField k Γ) := by
            have hmap :=
              (map_sum (algebraMap (valuationSubring k Γ) (HahnField k Γ))
                (fun i => (C.source (i + 1)).1 - (C.source i).1) (Finset.range n)).symm
            exact congrArg (fun x : HahnField k Γ => x + (start : HahnField k Γ)) hmap
      _ = ((((Finset.range n).sum
              (fun i => (C.source (i + 1)).1 - (C.source i).1) + start :
              valuationSubring k Γ) : valuationSubring k Γ) :
              HahnField k Γ) := by
            exact
              (map_add (algebraMap (valuationSubring k Γ) (HahnField k Γ))
                ((Finset.range n).sum
                  (fun i => (C.source (i + 1)).1 - (C.source i).1)) start).symm
      _ = ((C.source n).1 : HahnField k Γ) := by
            rw [C.sum_stepDiff_range_add_start_eq_source k Γ n]
  calc
    C.correctionPartialHahnField k Γ n + (start : HahnField k Γ)
        = (Finset.range n).sum
            (fun i => toLex (HahnSeries.single (C.stepValue k Γ i) (C.stepCoeff k Γ i))) +
          (start : HahnField k Γ) := by
            simp only [KOddClusterFixedStepChainFromData.correctionPartialHahnField,
              KOddClusterFixedStepChainFromData.correctionPartialHahnSeries]
            exact congrArg (fun x : HahnField k Γ => x + (start : HahnField k Γ))
              (map_sum (ofLexRingHom k Γ)
                (fun i => HahnSeries.single (C.stepValue k Γ i) (C.stepCoeff k Γ i))
                (Finset.range n))
    _ = (Finset.range n).sum
          (fun i => (((C.source (i + 1)).1 - (C.source i).1 : valuationSubring k Γ) :
            HahnField k Γ)) +
          (start : HahnField k Γ) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i _
            have hdiff := congrArg
              (fun x : valuationSubring k Γ => (x : HahnField k Γ))
              (C.stepDiff_eq_singleOfNonneg k Γ i)
            simpa [singleOfNonneg_coe] using hdiff.symm
    _ = ((C.source n).1 : HahnField k Γ) := hsum

theorem KOddClusterFixedStepChainFromData.correctionHahnSeries_coeff_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.correctionHahnSeries k Γ).coeff (C.stepValue k Γ n) = C.stepCoeff k Γ n := by
  rw [KOddClusterFixedStepChainFromData.correctionHahnSeries,
    KOddClusterFixedStepChainFromData.correctionFamily, HahnSeries.SummableFamily.coeff_hsum]
  rw [finsum_eq_single
    (fun i =>
      (singleStrictMonoSummableFamily k Γ (C.stepValue k Γ) (C.stepCoeff k Γ)
        (C.stepValue_strictMono k Γ) i).coeff (C.stepValue k Γ n))
    n]
  · simp [singleStrictMonoSummableFamily_apply]
  · intro i hin
    rw [singleStrictMonoSummableFamily_apply, HahnSeries.coeff_single_of_ne]
    intro hval
    exact hin ((C.stepValue_strictMono k Γ).injective hval.symm)

theorem KOddClusterFixedStepChainFromData.correctionPartialHahnSeries_coeff_stepValue_of_lt
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) {i n : ℕ} (hi : i < n) :
    (C.correctionPartialHahnSeries k Γ n).coeff (C.stepValue k Γ i) =
      C.stepCoeff k Γ i := by
  rw [KOddClusterFixedStepChainFromData.correctionPartialHahnSeries, HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [HahnSeries.coeff_single_of_ne]
    intro hval
    exact hji ((C.stepValue_strictMono k Γ).injective hval.symm)
  · intro hi_not
    exact False.elim (hi_not (Finset.mem_range.mpr hi))

theorem KOddClusterFixedStepChainFromData.correctionTail_coeff_stepValue_eq_zero_of_lt
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) {i n : ℕ} (hi : i < n) :
    (C.correctionHahnSeries k Γ - C.correctionPartialHahnSeries k Γ n).coeff
        (C.stepValue k Γ i) = 0 := by
  rw [HahnSeries.coeff_sub, C.correctionHahnSeries_coeff_stepValue k Γ,
    C.correctionPartialHahnSeries_coeff_stepValue_of_lt k Γ hi, sub_self]

theorem KOddClusterFixedStepChainFromData.correctionTail_coeff_eq_zero_of_lt_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) {γ : Γ} {n : ℕ}
    (hγ : γ < C.stepValue k Γ n) :
    (C.correctionHahnSeries k Γ - C.correctionPartialHahnSeries k Γ n).coeff γ = 0 := by
  by_cases hmem : ∃ i : ℕ, γ = C.stepValue k Γ i
  · rcases hmem with ⟨i, rfl⟩
    have hi : i < n := (C.stepValue_strictMono k Γ).lt_iff_lt.mp hγ
    exact C.correctionTail_coeff_stepValue_eq_zero_of_lt k Γ hi
  · have hhsum : (C.correctionHahnSeries k Γ).coeff γ = 0 := by
      by_contra hcoeff
      have hsupport : γ ∈ (C.correctionHahnSeries k Γ).support := by
        simpa [Function.mem_support] using hcoeff
      rcases C.correctionHahnSeries_support_subset_range k Γ hsupport with ⟨i, hi⟩
      exact hmem ⟨i, hi.symm⟩
    have hsum : (C.correctionPartialHahnSeries k Γ n).coeff γ = 0 := by
      rw [KOddClusterFixedStepChainFromData.correctionPartialHahnSeries, HahnSeries.coeff_sum]
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [HahnSeries.coeff_single_of_ne]
      intro hγj
      exact hmem ⟨j, hγj⟩
    rw [HahnSeries.coeff_sub, hhsum, hsum, sub_zero]

theorem KOddClusterFixedStepChainFromData.correctionTail_orderTop_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.stepValue k Γ n : WithTop Γ) ≤
      (C.correctionHahnSeries k Γ - C.correctionPartialHahnSeries k Γ n).orderTop := by
  let T : HahnSeries Γ k := C.correctionHahnSeries k Γ - C.correctionPartialHahnSeries k Γ n
  change (C.stepValue k Γ n : WithTop Γ) ≤ T.orderTop
  by_cases hT : T = 0
  · simp [hT]
  · by_contra hle
    have hlt : T.orderTop < (C.stepValue k Γ n : WithTop Γ) :=
      lt_of_not_ge hle
    have htop : T.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.mpr hT
    let γ : Γ := WithTop.untop T.orderTop htop
    have horder : T.orderTop = (γ : WithTop Γ) :=
      (WithTop.coe_untop T.orderTop htop).symm
    have hγlt : γ < C.stepValue k Γ n :=
      WithTop.coe_lt_coe.mp (by simpa [horder] using hlt)
    have hcoeff_ne : T.coeff γ ≠ 0 :=
      HahnSeries.coeff_orderTop_ne horder
    have hcoeff_zero : T.coeff γ = 0 := by
      simpa [T] using C.correctionTail_coeff_eq_zero_of_lt_stepValue k Γ hγlt
    exact hcoeff_ne hcoeff_zero

def KOddClusterFixedStepChainFromData.candidate
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    valuationSubring k Γ :=
  start + C.correctionValuationSubring k Γ

theorem KOddClusterFixedStepChainFromData.start_mem
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    start ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  have hmem := (C.source 0).2
  rwa [C.start_source] at hmem

noncomputable def KOddClusterFixedStepChainFromData.toShiftedChainData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    KOddClusterFixedStepChainFromData k Γ
      (F.comp (Polynomial.X +
        Polynomial.C (algebraMap (valuationSubring k Γ) (HahnField k Γ) start))) m 0 :=
  { one_lt := C.one_lt
    liftData := C.liftData.comp_X_add_C k Γ start (C.start_mem k Γ)
    source := fun n =>
      ⟨(C.source n).1 - start,
        (IsLocalRing.maximalIdeal (valuationSubring k Γ)).sub_mem (C.source n).2
          (C.start_mem k Γ)⟩
    start_source := by
      simp [C.start_source]
    step := by
      intro n
      have hstep := C.step n
      have hstep' :
          OddClusterStep k Γ C.liftData.lift m
            ((C.source n).1 - start + start) ((C.source (n + 1)).1 - start + start) := by
        convert hstep using 1 <;> abel
      exact
        OddClusterStep.to_comp_X_add_C (k := k) (Γ := Γ)
          (F := C.liftData.lift) (m := m) (A := start)
          (z := (C.source n).1 - start) (z' := (C.source (n + 1)).1 - start)
          (C.start_mem k Γ) hstep' }

theorem KOddClusterFixedStepChainFromData.toShiftedChainData_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.toShiftedChainData k Γ).stepValue k Γ n = C.stepValue k Γ n := by
  have hshift := (C.toShiftedChainData k Γ).addVal_stepDiff_eq_stepValue k Γ n
  have horig := C.addVal_stepDiff_eq_stepValue k Γ n
  have hdiff :
      (C.source (n + 1)).1 - start - ((C.source n).1 - start) =
        (C.source (n + 1)).1 - (C.source n).1 := by
    abel
  have hshift' :
      addVal k Γ
          (((C.source (n + 1)).1 - start - ((C.source n).1 - start) :
            valuationSubring k Γ) : HahnField k Γ) =
        ((C.toShiftedChainData k Γ).stepValue k Γ n : WithTop Γ) := by
    simpa [KOddClusterFixedStepChainFromData.toShiftedChainData] using hshift
  rw [hdiff, horig] at hshift'
  exact WithTop.coe_injective hshift'.symm

theorem KOddClusterFixedStepChainFromData.candidate_mem_maximalIdeal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    C.candidate k Γ ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem (C.start_mem k Γ)
    (C.correctionValuationSubring_mem_maximalIdeal k Γ)

theorem KOddClusterFixedStepChainFromData.candidate_sub_source_eq_tail
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.candidate k Γ : HahnField k Γ) - ((C.source n).1 : HahnField k Γ) =
      C.correctionHahnField k Γ - C.correctionPartialHahnField k Γ n := by
  have hsource := C.correctionPartialHahnField_add_start_eq_source k Γ n
  rw [← hsource]
  simp [KOddClusterFixedStepChainFromData.candidate,
    KOddClusterFixedStepChainFromData.correctionValuationSubring]
  abel

theorem KOddClusterFixedStepChainFromData.candidate_sub_source_addVal_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.stepValue k Γ n : WithTop Γ) ≤
      addVal k Γ (((C.candidate k Γ - (C.source n).1 : valuationSubring k Γ) :
        HahnField k Γ)) := by
  rw [addVal_apply]
  change (C.stepValue k Γ n : WithTop Γ) ≤
    (ofLexRingHom k Γ
      ((C.candidate k Γ : HahnField k Γ) - ((C.source n).1 : HahnField k Γ))).orderTop
  rw [C.candidate_sub_source_eq_tail k Γ n]
  rw [map_sub]
  simp only [ofLexRingHom_apply]
  simpa [KOddClusterFixedStepChainFromData.correctionHahnField,
    KOddClusterFixedStepChainFromData.correctionPartialHahnField] using
    C.correctionTail_orderTop_ge_stepValue k Γ n

theorem KOddClusterFixedStepChainFromData.candidate_eval_sub_source_eval_addVal_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.stepValue k Γ n : WithTop Γ) ≤
      addVal k Γ
        ((C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            (C.candidate k Γ : HahnField k Γ) -
          (C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            ((C.source n).1 : HahnField k Γ)) := by
  exact addVal_eval_map_sub_eval_map_ge_of_ge k Γ C.liftData.lift
    (x := (C.candidate k Γ : HahnField k Γ))
    (y := ((C.source n).1 : HahnField k Γ))
    (δ := C.stepValue k Γ n)
    (by
      exact (C.candidate k Γ).property)
    (by
      exact ((C.source n).1).property)
    (C.candidate_sub_source_addVal_ge_stepValue k Γ n)

theorem KOddClusterFixedStepChainFromData.candidate_eval_ge_stepValue_of_source_eval_ge
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ)
    (hsource :
      (C.stepValue k Γ n : WithTop Γ) ≤
        addVal k Γ
          ((C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            ((C.source n).1 : HahnField k Γ))) :
    (C.stepValue k Γ n : WithTop Γ) ≤
      addVal k Γ
        ((C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (C.candidate k Γ : HahnField k Γ)) := by
  let z : HahnField k Γ :=
    (C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      (C.candidate k Γ : HahnField k Γ)
  let zn : HahnField k Γ :=
    (C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      ((C.source n).1 : HahnField k Γ)
  have hdiff :
      (C.stepValue k Γ n : WithTop Γ) ≤ addVal k Γ (z - zn) := by
    exact C.candidate_eval_sub_source_eval_addVal_ge_stepValue k Γ n
  have hdecomp : z = (z - zn) + zn := by
    abel
  change (C.stepValue k Γ n : WithTop Γ) ≤ addVal k Γ z
  rw [hdecomp]
  exact (addVal k Γ).map_le_add hdiff hsource

theorem KOddClusterFixedStepChainFromData.candidate_eval_addVal_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) (n : ℕ) :
    (C.stepValue k Γ n : WithTop Γ) ≤
      addVal k Γ
        ((C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (C.candidate k Γ : HahnField k Γ)) :=
  C.candidate_eval_ge_stepValue_of_source_eval_ge k Γ n
    (C.source_eval_addVal_ge_stepValue k Γ n)

theorem KOddClusterFixedStepChainFromData.candidate_isRoot_map_of_unboundedStepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start)
    (hnot_bdd : ¬ BddAbove (Set.range (C.stepValue k Γ))) :
    (C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).IsRoot
      (C.candidate k Γ : HahnField k Γ) := by
  rw [Polynomial.IsRoot]
  let z : HahnField k Γ :=
    (C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      (C.candidate k Γ : HahnField k Γ)
  change z = 0
  by_contra hz
  have htop : addVal k Γ z ≠ ⊤ := by
    rw [addVal_apply]
    exact HahnSeries.orderTop_ne_top.mpr (fun hz_ofLex => hz (ofLex.injective hz_ofLex))
  let γ : Γ := WithTop.untop (addVal k Γ z) htop
  have hadd : addVal k Γ z = (γ : WithTop Γ) :=
    (WithTop.coe_untop (addVal k Γ z) htop).symm
  have hbdd : BddAbove (Set.range (C.stepValue k Γ)) := by
    refine ⟨γ, ?_⟩
    intro δ hδ
    rcases hδ with ⟨n, rfl⟩
    apply WithTop.coe_le_coe.mp
    rw [← hadd]
    exact C.candidate_eval_addVal_ge_stepValue k Γ n
  exact hnot_bdd hbdd

theorem KOddClusterFixedStepChainFromData.candidate_isRoot_map_or_bddAbove_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start) :
    (C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).IsRoot
        (C.candidate k Γ : HahnField k Γ) ∨
      BddAbove (Set.range (C.stepValue k Γ)) := by
  by_cases hbdd : BddAbove (Set.range (C.stepValue k Γ))
  · exact Or.inr hbdd
  · exact Or.inl (C.candidate_isRoot_map_of_unboundedStepValue k Γ hbdd)

theorem KOddClusterFixedStepChainFromData.positiveHahnRoot_of_candidate_isRoot_map
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (C : KOddClusterFixedStepChainFromData k Γ F m start)
    (hroot :
      (C.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).IsRoot
        (C.candidate k Γ : HahnField k Γ)) :
    PositiveHahnRoot k Γ F := by
  have hrootMax : RootInMaximalIdeal k Γ C.liftData.lift := by
    refine ⟨C.candidate k Γ, ?_, ?_⟩
    · exact C.candidate_mem_maximalIdeal k Γ
    · rw [Polynomial.IsRoot] at hroot ⊢
      rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) C.liftData.lift
        (C.candidate k Γ)] at hroot
      exact Subtype.ext hroot
  have hpos := RootInMaximalIdeal.positiveHahnRootInMap k Γ hrootMax
  simpa [PositiveHahnRootInMap, C.liftData.map_eq] using hpos

/-- The bounded fixed-step obstruction for a fixed-lift chain whose first source is an
arbitrary maximal-ideal element.  This is the terminal branch left after an improved
lower-edge source has been iterated without producing an unbounded correction. -/
structure KOddClusterFixedStepTerminalFromData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (F : Polynomial (HahnField k Γ)) (m : ℕ) (start : valuationSubring k Γ) where
  chain : KOddClusterFixedStepChainFromData k Γ F m start
  bddAbove_stepValue : BddAbove (Set.range (chain.stepValue k Γ))

theorem exists_KOddClusterFixedStepTerminalFromData_of_fixedLiftWithRootBelow_no_positiveRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hstep : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (hno : ¬ PositiveHahnRoot k Γ F)
    (hbranch : KTranslatedSameMultiplicityZeroBranch k Γ F m)
    (D : KOddClusterLiftData k Γ F m)
    (start : valuationSubring k Γ)
    (hstart : start ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    ∃ T : KOddClusterFixedStepTerminalFromData k Γ F m start, T.chain.liftData = D := by
  rcases exists_KOddClusterFixedStepChainFromData_of_fixedLiftWithRootBelow_no_positiveRoot
      k Γ hstep hbelow hno hbranch D start hstart with ⟨C, hC⟩
  rcases C.candidate_isRoot_map_or_bddAbove_stepValue k Γ with hroot | hbdd
  · exact False.elim (hno (C.positiveHahnRoot_of_candidate_isRoot_map k Γ hroot))
  · exact ⟨{
      chain := C
      bddAbove_stepValue := hbdd }, hC⟩

end HahnField

end

end HahnKaplanskyRealClosedness
