/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.SimpleCluster.Fixed.OrdinalSupport

/-!
# Fixed-lift ordinal-prefix closure

This module owns the resolver-free ordinal-prefix construction for the fixed-lift terminal
branch: successor singleton increments, polynomial coefficient continuity, and the Hartogs
contradiction. Auxiliary Nat-recovery and plateau routes are kept outside the canonical source.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

open OrdinalSupport

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

namespace KSameMultiplicityFixedStepTerminalObstructionData

namespace KSameMultiplicityFixedStepTerminalShiftState

private structure KSameMultiplicityOrdinalJetChain
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (I : Type*) [LinearOrder I]
    (F : Polynomial (HahnField k Γ)) (m : ℕ) where
  state : I → KSameMultiplicityFixedStepTerminalShiftState k Γ F m
  rank_strictMono : StrictMono fun i =>
    (state i).terminal.terminal.chain.stepValue k Γ 0
  shift_coeff_stable : ∀ {i j : I}, i ≤ j → ∀ {γ : Γ},
    γ < (state i).terminal.terminal.chain.stepValue k Γ 0 →
      (ofLex ((state j).shift : HahnField k Γ)).coeff γ =
        (ofLex ((state i).shift : HahnField k Γ)).coeff γ

private def KSameMultiplicityOrdinalJetChain.rank
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) (i : I) : Γ :=
  (C.state i).terminal.terminal.chain.stepValue k Γ 0

private noncomputable def KSameMultiplicityOrdinalJetChain.stableCoeff
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) (γ : Γ) : k := by
  classical
  exact if hcut : ∃ i : I, γ < C.rank k Γ i then
    (ofLex ((C.state (Classical.choose hcut)).shift : HahnField k Γ)).coeff γ
  else 0

private theorem KSameMultiplicityOrdinalJetChain.stableCoeff_eq_state_of_lt_rank
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m)
    {i : I} {γ : Γ} (hγ : γ < C.rank k Γ i) :
    C.stableCoeff k Γ γ =
      (ofLex ((C.state i).shift : HahnField k Γ)).coeff γ := by
  classical
  rw [KSameMultiplicityOrdinalJetChain.stableCoeff]
  split
  next hcut =>
    let j := Classical.choose hcut
    have hj : γ < C.rank k Γ j := Classical.choose_spec hcut
    change
      (ofLex ((C.state j).shift : HahnField k Γ)).coeff γ =
        (ofLex ((C.state i).shift : HahnField k Γ)).coeff γ
    rcases le_total i j with hij | hji
    · exact C.shift_coeff_stable hij hγ
    · exact (C.shift_coeff_stable hji hj).symm
  next hnot => exact False.elim (hnot ⟨i, hγ⟩)

private noncomputable def KSameMultiplicityOrdinalJetChain.firstCrossing
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m)
    (γ : Γ) (hcut : ∃ i : I, γ < C.rank k Γ i) : I :=
  let cut : Set I := {i | γ < C.rank k Γ i}
  (Set.IsWF.of_wellFoundedLT cut).min hcut

private theorem KSameMultiplicityOrdinalJetChain.firstCrossing_spec
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m)
    (γ : Γ) (hcut : ∃ i : I, γ < C.rank k Γ i) :
    γ < C.rank k Γ (C.firstCrossing k Γ γ hcut) :=
  (Set.IsWF.of_wellFoundedLT {i : I | γ < C.rank k Γ i}).min_mem hcut

private theorem KSameMultiplicityOrdinalJetChain.firstCrossing_le
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m)
    (γ : Γ) (hcut : ∃ i : I, γ < C.rank k Γ i) {i : I}
    (hi : γ < C.rank k Γ i) : C.firstCrossing k Γ γ hcut ≤ i := by
  by_contra hnot
  exact (Set.IsWF.of_wellFoundedLT {j : I | γ < C.rank k Γ j}).not_lt_min
    hcut hi (lt_of_not_ge hnot)

private noncomputable def KSameMultiplicityOrdinalJetChain.firstCrossingBlock
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) (i : I) :
    HahnSeries Γ k := by
  classical
  let coeff : Γ → k := fun γ => if hcut : ∃ j : I, γ < C.rank k Γ j then
    if C.firstCrossing k Γ γ hcut = i then C.stableCoeff k Γ γ else 0 else 0
  refine ⟨coeff, ?_⟩
  refine (ofLex ((C.state i).shift : HahnField k Γ)).isPWO_support.mono ?_
  intro γ hγ
  have hcut : ∃ j : I, γ < C.rank k Γ j := by
    by_contra hnot
    apply hγ
    simp [coeff, hnot]
  have hfirst : C.firstCrossing k Γ γ hcut = i := by
    by_contra hne
    apply hγ
    simp [coeff, hcut, hne]
  have hcoeff : C.stableCoeff k Γ γ ≠ 0 := by
    simpa [coeff, hcut, hfirst] using hγ
  have hlt := C.firstCrossing_spec k Γ γ hcut
  rw [hfirst] at hlt
  have heq := C.stableCoeff_eq_state_of_lt_rank k Γ hlt
  simpa [Function.mem_support, heq] using hcoeff

private theorem
    KSameMultiplicityOrdinalJetChain.mem_firstCrossingBlock_imp_firstCrossing_eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) {i : I} {γ : Γ}
    (hγ : γ ∈ (C.firstCrossingBlock k Γ i).support) :
    ∃ hcut : ∃ j : I, γ < C.rank k Γ j,
      C.firstCrossing k Γ γ hcut = i := by
  have hcut : ∃ j : I, γ < C.rank k Γ j := by
    by_contra hnot
    apply hγ
    simp [KSameMultiplicityOrdinalJetChain.firstCrossingBlock, hnot]
  refine ⟨hcut, ?_⟩
  by_contra hne
  apply hγ
  simp [KSameMultiplicityOrdinalJetChain.firstCrossingBlock, hcut, hne]

private theorem KSameMultiplicityOrdinalJetChain.firstCrossingBlocks_ordered
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m)
    {i j : I} (hij : i < j) {γ δ : Γ}
    (hγ : γ ∈ (C.firstCrossingBlock k Γ i).support)
    (hδ : δ ∈ (C.firstCrossingBlock k Γ j).support) : γ < δ := by
  rcases C.mem_firstCrossingBlock_imp_firstCrossing_eq k Γ hγ with ⟨hcutγ, hfirstγ⟩
  rcases C.mem_firstCrossingBlock_imp_firstCrossing_eq k Γ hδ with ⟨hcutδ, hfirstδ⟩
  have hγlt := C.firstCrossing_spec k Γ γ hcutγ
  rw [hfirstγ] at hγlt
  have hnot : ¬ δ < C.rank k Γ i := by
    intro hδlt
    have hle := C.firstCrossing_le k Γ δ hcutδ hδlt
    rw [hfirstδ] at hle
    exact (not_le_of_gt hij) hle
  exact hγlt.trans_le (le_of_not_gt hnot)

private theorem
    KSameMultiplicityOrdinalJetChain.firstCrossingBlock_iUnion_support_isPWO
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) :
    (⋃ i : I, (C.firstCrossingBlock k Γ i).support).IsPWO :=
  iUnion_hahnSeries_support_isPWO_of_pairwise_ordered k Γ
    (C.firstCrossingBlock k Γ) (C.firstCrossingBlocks_ordered k Γ)

private theorem KSameMultiplicityOrdinalJetChain.mem_support_stableCoeff_imp_cut
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) {γ : Γ}
    (hγ : γ ∈ Function.support (C.stableCoeff k Γ)) :
    ∃ i : I, γ < C.rank k Γ i := by
  by_contra hnot
  apply hγ
  rw [KSameMultiplicityOrdinalJetChain.stableCoeff, dif_neg hnot]

private noncomputable def KSameMultiplicityOrdinalJetChain.stableHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) : HahnSeries Γ k := by
  classical
  refine ⟨C.stableCoeff k Γ, ?_⟩
  refine Set.IsPWO.mono (C.firstCrossingBlock_iUnion_support_isPWO k Γ) ?_
  intro γ hγ
  have hcut := C.mem_support_stableCoeff_imp_cut k Γ hγ
  let i := C.firstCrossing k Γ γ hcut
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  change (if h : ∃ j : I, γ < C.rank k Γ j then
    if C.firstCrossing k Γ γ h = i then C.stableCoeff k Γ γ else 0 else 0) ≠ 0
  simpa [hcut, i, Function.mem_support] using hγ

private theorem KSameMultiplicityOrdinalJetChain.stableHahnSeries_support_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) {γ : Γ}
    (hγ : γ ∈ (C.stableHahnSeries k Γ).support) : 0 < γ := by
  have hcoeff : C.stableCoeff k Γ γ ≠ 0 := by
    simpa [KSameMultiplicityOrdinalJetChain.stableHahnSeries,
      Function.mem_support] using hγ
  have hcut := C.mem_support_stableCoeff_imp_cut k Γ (by
    simpa [Function.mem_support] using hcoeff)
  rcases hcut with ⟨i, hi⟩
  have heq := C.stableCoeff_eq_state_of_lt_rank k Γ hi
  have hstateCoeff : (ofLex ((C.state i).shift : HahnField k Γ)).coeff γ ≠ 0 := by
    simpa [heq] using hcoeff
  have hpos :
      (0 : WithTop Γ) < (ofLex ((C.state i).shift : HahnField k Γ)).orderTop := by
    have := (mem_maximalIdeal_iff_pos_addVal k Γ _).mp (C.state i).shift_mem
    simpa [addVal_apply] using this
  exact WithTop.coe_lt_coe.mp
    (hpos.trans_le (HahnSeries.orderTop_le_of_coeff_ne_zero hstateCoeff))

private theorem KSameMultiplicityOrdinalJetChain.stableHahnSeries_orderTop_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) :
    (0 : WithTop Γ) < (C.stableHahnSeries k Γ).orderTop := by
  by_cases hzero : C.stableHahnSeries k Γ = 0
  · simp [hzero]
  · rw [HahnSeries.zero_lt_orderTop_iff hzero]
    apply C.stableHahnSeries_support_pos k Γ
    simpa [Function.mem_support] using
      (HahnSeries.coeff_order_eq_zero.not.2 hzero)

private noncomputable def KSameMultiplicityOrdinalJetChain.stableValuationSubring
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) :
    valuationSubring k Γ :=
  ⟨toLex (C.stableHahnSeries k Γ), by
    rw [mem_valuationSubring_iff, addVal_apply]
    exact le_of_lt (C.stableHahnSeries_orderTop_pos k Γ)⟩

private theorem
    KSameMultiplicityOrdinalJetChain.stableValuationSubring_mem_maximalIdeal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) :
    C.stableValuationSubring k Γ ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [mem_maximalIdeal_iff_pos_addVal, addVal_apply]
  simpa [KSameMultiplicityOrdinalJetChain.stableValuationSubring] using
    C.stableHahnSeries_orderTop_pos k Γ

private theorem
    KSameMultiplicityOrdinalJetChain.rank_le_stable_sub_state_orderTop
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) (i : I) :
    (C.rank k Γ i : WithTop Γ) ≤
      (C.stableHahnSeries k Γ - ofLex ((C.state i).shift : HahnField k Γ)).orderTop := by
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro γ hγ
  change C.stableCoeff k Γ γ -
    (ofLex ((C.state i).shift : HahnField k Γ)).coeff γ = 0
  rw [C.stableCoeff_eq_state_of_lt_rank k Γ (WithTop.coe_lt_coe.mp hγ), sub_self]

private theorem KSameMultiplicityOrdinalJetChain.rank_le_stable_sub_state_addVal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) (i : I) :
    (C.rank k Γ i : WithTop Γ) ≤
      addVal k Γ ((C.stableValuationSubring k Γ : HahnField k Γ) -
        ((C.state i).shift : HahnField k Γ)) := by
  simpa [addVal_apply,
    KSameMultiplicityOrdinalJetChain.stableValuationSubring, map_sub] using
      C.rank_le_stable_sub_state_orderTop k Γ i

private structure RankCoherentLowerEdge
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m) where
  obstruction : KSameMultiplicityLowerEdgeObstruction k Γ S.current m
  source_eq_zero : obstruction.source = 0
  delta_eq_firstStep :
    obstruction.delta = S.terminal.terminal.chain.stepValue k Γ 0
  branch_eq : obstruction.branch = S.terminal.branch
  liftData_eq : obstruction.liftData = S.terminal.terminal.chain.liftData

private theorem
    firstSourceNonbelow_or_rankCoherentLowerEdge
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m) :
    (∀ j, 0 < j → j < m →
      (((m - j) • S.terminal.terminal.chain.stepValue k Γ 0 : Γ) : WithTop Γ) ≤
        addVal k Γ
          ((S.terminal.terminal.chain.liftData.lift.comp
            (Polynomial.X + Polynomial.C
              (S.terminal.terminal.chain.source 0).1)).coeff j : HahnField k Γ)) ∨
      Nonempty (RankCoherentLowerEdge k Γ S) := by
  let D := S.terminal.terminal.chain
  by_cases hnotBelow : ∀ j, 0 < j → j < m →
      (((m - j) • D.stepValue k Γ 0 : Γ) : WithTop Γ) ≤
        addVal k Γ
          ((D.liftData.lift.comp
            (Polynomial.X + Polynomial.C (D.source 0).1)).coeff j : HahnField k Γ)
  · exact Or.inl hnotBelow
  · right
    push Not at hnotBelow
    rcases hnotBelow with ⟨j, hjpos, hjlt, hbelowCoeff⟩
    exact ⟨{
      obstruction := {
        branch := S.terminal.branch
        liftData := D.liftData
        source := (D.source 0).1
        source_mem := (D.source 0).2
        gamma := m • D.stepValue k Γ 0
        delta := D.stepValue k Γ 0
        eval_eq := D.evalValue_eq_nsmul_stepValue k Γ 0
        delta_pos := D.stepValue_pos k Γ 0
        scale := rfl
        index := j
        index_pos := hjpos
        index_lt := hjlt
        below := hbelowCoeff }
      source_eq_zero := D.start_source
      delta_eq_firstStep := rfl
      branch_eq := rfl
      liftData_eq := rfl }⟩

private theorem
    KSameMultiplicityOrdinalJetChain.nsmul_rank_le_stable_sub_eval_or_lowerEdge
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) (i : I) :
    ((m • C.rank k Γ i : WithTop Γ) ≤
        addVal k Γ
          (F.eval (C.stableValuationSubring k Γ : HahnField k Γ) -
            F.eval ((C.state i).shift : HahnField k Γ))) ∨
      Nonempty (RankCoherentLowerEdge k Γ (C.state i)) := by
  let S := C.state i
  let D := S.terminal.terminal.chain
  let x : valuationSubring k Γ := C.stableValuationSubring k Γ - S.shift
  let z : HahnField k Γ := (x : HahnField k Γ)
  rcases S.firstSourceNonbelow_or_rankCoherentLowerEdge k Γ with hnotBelow | hedge
  · left
    have hz : (D.stepValue k Γ 0 : WithTop Γ) ≤ addVal k Γ z := by
      simpa [S, D, x, z, KSameMultiplicityOrdinalJetChain.rank] using
        C.rank_le_stable_sub_state_addVal k Γ i
    have hraw :=
      addVal_eval_map_sub_eval_map_ge_of_comp_nonbelow k Γ D.liftData.lift
        (D.source 0).1 (m := m) (δ := D.stepValue k Γ 0)
        (γ := m • D.stepValue k Γ 0) (z := z)
        (D.stepValue_pos k Γ 0) rfl hz hnotBelow
    have harg :
        ((D.source 0).1 : HahnField k Γ) + z = (x : HahnField k Γ) := by
      simp [D.start_source, z]
    have hright :
        (D.liftData.lift.map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            (((D.source 0).1 : HahnField k Γ) + z) =
          F.eval (C.stableValuationSubring k Γ : HahnField k Γ) := by
      calc
        (D.liftData.lift.map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            (((D.source 0).1 : HahnField k Γ) + z) =
            (D.liftData.lift.map
              (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
              (x : HahnField k Γ) := by rw [harg]
        _ = ((D.liftData.lift.eval x : valuationSubring k Γ) : HahnField k Γ) := by
          rw [eval_map_algebraMap_eq_coe_eval]
        _ = F.eval ((x : HahnField k Γ) +
            algebraMap (valuationSubring k Γ) (HahnField k Γ) S.shift) :=
          S.lift_eval_eq_original_shift_eval k Γ x
        _ = F.eval (C.stableValuationSubring k Γ : HahnField k Γ) := by
          congr 2
          rw [show (x : HahnField k Γ) =
              (C.stableValuationSubring k Γ : HahnField k Γ) -
                (S.shift : HahnField k Γ) by simp [x]]
          rw [← Algebra.algebraMap_ofSubsemiring_apply
            (valuationSubring k Γ) S.shift]
          exact sub_add_cancel _ _
    have hleft :
        (D.liftData.lift.map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            ((D.source 0).1 : HahnField k Γ) =
          F.eval (S.shift : HahnField k Γ) := by
      rw [eval_map_algebraMap_eq_coe_eval]
      simpa [D, S, D.start_source, Algebra.algebraMap_ofSubsemiring_apply] using
        S.lift_eval_eq_original_shift_eval k Γ (D.source 0).1
    rw [hright, hleft] at hraw
    simpa [S, D, KSameMultiplicityOrdinalJetChain.rank] using hraw
  · exact Or.inr hedge

private theorem
    KSameMultiplicityOrdinalJetChain.nsmul_rank_le_stable_eval_or_lowerEdge
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) (i : I) :
    ((m • C.rank k Γ i : WithTop Γ) ≤
      addVal k Γ (F.eval (C.stableValuationSubring k Γ : HahnField k Γ))) ∨
      Nonempty (RankCoherentLowerEdge k Γ (C.state i)) := by
  rcases C.nsmul_rank_le_stable_sub_eval_or_lowerEdge k Γ i with
    heval | hedge
  · left
    have hstateEq :
        addVal k Γ (F.eval ((C.state i).shift : HahnField k Γ)) =
          (m • C.rank k Γ i : WithTop Γ) := by
      simpa [KSameMultiplicityOrdinalJetChain.rank] using
        (C.state i).shift_eval_addVal_eq_nsmul_firstStep k Γ
    have hstate :
        (m • C.rank k Γ i : WithTop Γ) ≤
          addVal k Γ (F.eval ((C.state i).shift : HahnField k Γ)) :=
      hstateEq.ge
    have hsum := (addVal k Γ).map_le_add heval hstate
    have hdecomp :
        F.eval (C.stableValuationSubring k Γ : HahnField k Γ) =
          (F.eval (C.stableValuationSubring k Γ : HahnField k Γ) -
            F.eval ((C.state i).shift : HahnField k Γ)) +
            F.eval ((C.state i).shift : HahnField k Γ) := by
      abel
    rw [← hdecomp] at hsum
    exact hsum
  · exact Or.inr hedge

private noncomputable def
    KSameMultiplicityOrdinalJetChain.stableLimitShiftState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F)
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ F m := by
  let Tlimit := Classical.choose
    (exists_KOddClusterFixedStepTerminalFromData_of_fixedLiftWithRootBelow_no_positiveRoot
      k Γ hfixed hbelow hno T.branch T.terminal.chain.liftData
        (C.stableValuationSubring k Γ) (C.stableValuationSubring_mem_maximalIdeal k Γ))
  exact {
    current := F.comp (Polynomial.X + Polynomial.C
      (algebraMap (valuationSubring k Γ) (HahnField k Γ) (C.stableValuationSubring k Γ)))
    shift := C.stableValuationSubring k Γ
    shift_mem := C.stableValuationSubring_mem_maximalIdeal k Γ
    current_eq := rfl
    terminal := Tlimit.toShiftedSameTerminalObstructionData k Γ T.branch
    root_transport := PositiveHahnRoot.of_comp_X_add_C k Γ
      (C.stableValuationSubring_mem_maximalIdeal k Γ) }

private theorem
    KSameMultiplicityOrdinalJetChain.rank_lt_stableLimit_firstStep_or_lowerEdge
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F)
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m)
    {i j : I} (hij : i < j) :
    (C.rank k Γ i <
        (C.stableLimitShiftState k Γ hfixed hbelow T hno).terminal.terminal.chain.stepValue
          k Γ 0) ∨
      Nonempty (RankCoherentLowerEdge k Γ (C.state j)) := by
  let L := C.stableLimitShiftState k Γ hfixed hbelow T hno
  rcases C.nsmul_rank_le_stable_eval_or_lowerEdge k Γ j with
    heval | hlowerEdge
  · left
    have hscale :
        m • C.rank k Γ j ≤ m • L.terminal.terminal.chain.stepValue k Γ 0 := by
      apply WithTop.coe_le_coe.mp
      calc
        ((m • C.rank k Γ j : Γ) : WithTop Γ) ≤
            addVal k Γ (F.eval (C.stableValuationSubring k Γ : HahnField k Γ)) := by
              simpa using heval
        _ = ((m • L.terminal.terminal.chain.stepValue k Γ 0 : Γ) : WithTop Γ) := by
              simpa [L,
                KSameMultiplicityOrdinalJetChain.stableLimitShiftState] using
                L.shift_eval_addVal_eq_nsmul_firstStep k Γ
    have hle : C.rank k Γ j ≤ L.terminal.terminal.chain.stepValue k Γ 0 :=
      (nsmul_right_strictMono (M := Γ)
        (Nat.ne_of_gt (zero_lt_one.trans T.terminal.chain.one_lt))).le_iff_le.mp hscale
    exact (C.rank_strictMono hij).trans_le hle
  · exact Or.inr hlowerEdge

private theorem KSameMultiplicityOrdinalJetChain.rank_lt_stableLimit_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    (hlower : KSameMultiplicityLowerEdgeResolutionWithRootBelow k Γ)
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F)
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m)
    {i j : I} (hij : i < j) :
    C.rank k Γ i <
      (C.stableLimitShiftState k Γ hfixed hbelow T hno).terminal.terminal.chain.stepValue
        k Γ 0 := by
  rcases C.rank_lt_stableLimit_firstStep_or_lowerEdge
      k Γ hfixed hbelow T hno hij with hlt | hlowerEdge
  · exact hlt
  · rcases hlowerEdge with ⟨hlowerEdge⟩
    exact False.elim
      (hno ((C.state j).root_transport (hlower hbelow ⟨hlowerEdge.obstruction⟩)))

private theorem
    KSameMultiplicityOrdinalJetChain.stableLimit_coeff_eq_state_of_lt_rank
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F)
    (C : KSameMultiplicityOrdinalJetChain k Γ I F m)
    {i : I} {γ : Γ} (hγ : γ < C.rank k Γ i) :
    (ofLex ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift : HahnField k Γ)).coeff γ =
      (ofLex ((C.state i).shift : HahnField k Γ)).coeff γ := by
  simpa [KSameMultiplicityOrdinalJetChain.stableLimitShiftState,
    KSameMultiplicityOrdinalJetChain.stableValuationSubring,
    KSameMultiplicityOrdinalJetChain.stableHahnSeries] using
      C.stableCoeff_eq_state_of_lt_rank k Γ hγ

private noncomputable def
    lowerEdgeRecoveryTerminalFrom
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (O : KSameMultiplicityLowerEdgeObstruction k Γ S.current m) :
    KOddClusterFixedStepTerminalFromData k Γ S.current m O.source :=
  Classical.choose
    (exists_KOddClusterFixedStepTerminalFromData_of_fixedLiftWithRootBelow_no_positiveRoot
      k Γ hfixed hbelow (S.no_positiveRoot_current k Γ hno) O.branch O.liftData
      O.source O.source_mem)

private theorem
    lowerEdgeRecoveryTerminalFrom_liftData_eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (O : KSameMultiplicityLowerEdgeObstruction k Γ S.current m) :
    (S.lowerEdgeRecoveryTerminalFrom k Γ hfixed hbelow hno O).chain.liftData =
      O.liftData :=
  Classical.choose_spec
    (exists_KOddClusterFixedStepTerminalFromData_of_fixedLiftWithRootBelow_no_positiveRoot
      k Γ hfixed hbelow (S.no_positiveRoot_current k Γ hno) O.branch O.liftData
      O.source O.source_mem)

private noncomputable def
    lowerEdgeRecoveryBaseState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (O : KSameMultiplicityLowerEdgeObstruction k Γ S.current m) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ S.current m := by
  let Tfrom := S.lowerEdgeRecoveryTerminalFrom k Γ hfixed hbelow hno O
  exact {
    current := S.current.comp (Polynomial.X + Polynomial.C
      (algebraMap (valuationSubring k Γ) (HahnField k Γ) O.source))
    shift := O.source
    shift_mem := O.source_mem
    current_eq := rfl
    terminal := Tfrom.toShiftedSameTerminalObstructionData k Γ O.branch
    root_transport := PositiveHahnRoot.of_comp_X_add_C k Γ O.source_mem }

private noncomputable def
    lowerEdgeRecoveryState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (O : KSameMultiplicityLowerEdgeObstruction k Γ S.current m) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m :=
  (S.trans k Γ (S.lowerEdgeRecoveryBaseState k Γ hfixed hbelow hno O))
    |>.advanceFirstSource k Γ

private theorem
    lowerEdgeRecoveryBaseState_firstStep_eq_delta
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (O : KSameMultiplicityLowerEdgeObstruction k Γ S.current m) :
    (S.lowerEdgeRecoveryBaseState k Γ hfixed hbelow hno O).terminal.terminal.chain.stepValue
        k Γ 0 = O.delta := by
  let Tfrom := S.lowerEdgeRecoveryTerminalFrom k Γ hfixed hbelow hno O
  have hsource := Tfrom.chain.source_eval_addVal_eq_nsmul_stepValue k Γ 0
  have hlift := S.lowerEdgeRecoveryTerminalFrom_liftData_eq k Γ hfixed hbelow hno O
  rw [hlift, Tfrom.chain.start_source, eval_map_algebraMap_eq_coe_eval,
    O.eval_eq, ← O.scale] at hsource
  have hscale : m • Tfrom.chain.stepValue k Γ 0 = m • O.delta :=
    WithTop.coe_injective hsource.symm
  have hstep : Tfrom.chain.stepValue k Γ 0 = O.delta :=
    (nsmul_right_strictMono (M := Γ)
      (Nat.ne_of_gt (zero_lt_one.trans O.branch.one_lt))).injective hscale
  change (Tfrom.chain.toShiftedChainData k Γ).stepValue k Γ 0 = O.delta
  rw [Tfrom.chain.toShiftedChainData_stepValue, hstep]

private theorem delta_lt_lowerEdgeRecovery_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (O : KSameMultiplicityLowerEdgeObstruction k Γ S.current m) :
    O.delta <
      (S.lowerEdgeRecoveryState k Γ hfixed hbelow hno O).terminal.terminal.chain.stepValue
        k Γ 0 := by
  let R := S.lowerEdgeRecoveryBaseState k Γ hfixed hbelow hno O
  have hlt := (S.trans k Γ R).firstStep_lt_advanceFirstSource k Γ
  rw [S.trans_terminal_stepValue k Γ R 0,
    S.lowerEdgeRecoveryBaseState_firstStep_eq_delta k Γ hfixed hbelow hno O] at hlt
  exact hlt

private theorem lowerEdgeRecovery_shift_sub_eq_singleOfNonneg
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (E : RankCoherentLowerEdge k Γ S) :
    (S.lowerEdgeRecoveryState k Γ hfixed hbelow hno E.obstruction).shift - S.shift =
      singleOfNonneg k Γ E.obstruction.delta
        ((S.trans k Γ (S.lowerEdgeRecoveryBaseState
          k Γ hfixed hbelow hno E.obstruction)).terminal.terminal.chain.stepCoeff k Γ 0)
        (le_of_lt E.obstruction.delta_pos) := by
  let O := E.obstruction
  let R := S.lowerEdgeRecoveryBaseState k Γ hfixed hbelow hno O
  let A := S.trans k Γ R
  let C := A.terminal.terminal.chain
  have hbase : A.shift = S.shift := by
    dsimp [A]
    rw [S.trans_shift k Γ R]
    change S.shift + O.source = S.shift
    rw [E.source_eq_zero]
    simp
  have hstep : C.stepValue k Γ 0 = O.delta := by
    dsimp [C, A]
    rw [S.trans_terminal_stepValue k Γ R 0,
      S.lowerEdgeRecoveryBaseState_firstStep_eq_delta k Γ hfixed hbelow hno O]
  have hsingle := C.stepDiff_eq_singleOfNonneg k Γ 0
  rw [C.start_source, sub_zero] at hsingle
  have hsingle' : (C.source 1).1 =
      singleOfNonneg k Γ O.delta (C.stepCoeff k Γ 0) (le_of_lt O.delta_pos) := by
    simpa only [Nat.zero_add, hstep] using hsingle
  change (A.advanceFirstSource k Γ).shift - S.shift = _
  rw [← hbase]
  rw [KSameMultiplicityFixedStepTerminalShiftState.advanceFirstSource,
    A.trans_shift k Γ, A.terminal.advanceFirstSource_shift k Γ]
  change A.shift + (C.source 1).1 - A.shift = _
  rw [hsingle']
  abel

private noncomputable def chosenRankCoherentLowerEdge
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hedge : Nonempty (RankCoherentLowerEdge k Γ S)) :
    RankCoherentLowerEdge k Γ S :=
  Classical.choice hedge

private noncomputable def
    terminalOrdinalNextState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m := by
  classical
  by_cases hedge : Nonempty (RankCoherentLowerEdge k Γ S)
  · exact S.lowerEdgeRecoveryState k Γ hfixed hbelow hno
      (S.chosenRankCoherentLowerEdge k Γ hedge).obstruction
  · exact S.advanceFirstSource k Γ

private theorem terminalOrdinalNextState_eq_lowerEdgeRecoveryState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (hedge : Nonempty (RankCoherentLowerEdge k Γ S)) :
    S.terminalOrdinalNextState k Γ hfixed hbelow hno =
      S.lowerEdgeRecoveryState k Γ hfixed hbelow hno
        (S.chosenRankCoherentLowerEdge k Γ hedge).obstruction := by
  unfold terminalOrdinalNextState
  simp only [dif_pos hedge]

private theorem terminalOrdinalNextState_eq_advanceFirstSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0)
    (hedge : ¬ Nonempty (RankCoherentLowerEdge k Γ S)) :
    S.terminalOrdinalNextState k Γ hfixed hbelow hno =
      S.advanceFirstSource k Γ := by
  unfold terminalOrdinalNextState
  simp only [dif_neg hedge]

private theorem terminalOrdinalNextState_shift_sub_eq_singleOfNonneg
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0) :
    ∃ c : k, c ≠ 0 ∧
      (S.terminalOrdinalNextState k Γ hfixed hbelow hno).shift - S.shift =
        singleOfNonneg k Γ (S.terminal.terminal.chain.stepValue k Γ 0) c
          (le_of_lt (S.terminal.terminal.chain.stepValue_pos k Γ 0)) := by
  classical
  by_cases hedge : Nonempty (RankCoherentLowerEdge k Γ S)
  · let E := S.chosenRankCoherentLowerEdge k Γ hedge
    rw [S.terminalOrdinalNextState_eq_lowerEdgeRecoveryState
      k Γ hfixed hbelow hno hedge]
    let R := S.lowerEdgeRecoveryBaseState k Γ hfixed hbelow hno E.obstruction
    let C := (S.trans k Γ R).terminal.terminal.chain
    have hsingle := S.lowerEdgeRecovery_shift_sub_eq_singleOfNonneg
      k Γ hfixed hbelow hno E
    refine ⟨C.stepCoeff k Γ 0,
      ?_, ?_⟩
    · exact C.stepCoeff_ne_zero k Γ 0
    · simpa only [C, R, E.delta_eq_firstStep] using hsingle
  · rw [S.terminalOrdinalNextState_eq_advanceFirstSource
      k Γ hfixed hbelow hno hedge]
    let C := S.terminal.terminal.chain
    have hsingle := C.stepDiff_eq_singleOfNonneg k Γ 0
    rw [C.start_source, sub_zero] at hsingle
    have hsingle' : (C.source 1).1 =
        singleOfNonneg k Γ (C.stepValue k Γ 0) (C.stepCoeff k Γ 0)
          (le_of_lt (C.stepValue_pos k Γ 0)) := by
      simpa only [Nat.zero_add] using hsingle
    refine ⟨C.stepCoeff k Γ 0, C.stepCoeff_ne_zero k Γ 0, ?_⟩
    rw [KSameMultiplicityFixedStepTerminalShiftState.advanceFirstSource,
      S.trans_shift k Γ, S.terminal.advanceFirstSource_shift k Γ]
    change S.shift + (C.source 1).1 - S.shift = _
    rw [hsingle']
    abel

private theorem terminalOrdinalNextState_shift_sub_addVal_eq_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0) :
    addVal k Γ
        (((S.terminalOrdinalNextState k Γ hfixed hbelow hno).shift : HahnField k Γ) -
          (S.shift : HahnField k Γ)) =
      (S.terminal.terminal.chain.stepValue k Γ 0 : WithTop Γ) := by
  rcases S.terminalOrdinalNextState_shift_sub_eq_singleOfNonneg
      k Γ hfixed hbelow hno with ⟨c, hc, hsingle⟩
  have hsingle' :
      ((S.terminalOrdinalNextState k Γ hfixed hbelow hno).shift : HahnField k Γ) -
          (S.shift : HahnField k Γ) =
        (singleOfNonneg k Γ (S.terminal.terminal.chain.stepValue k Γ 0) c
          (le_of_lt (S.terminal.terminal.chain.stepValue_pos k Γ 0)) : HahnField k Γ) := by
    simpa using congrArg (fun x : valuationSubring k Γ => (x : HahnField k Γ)) hsingle
  rw [hsingle']
  exact addVal_singleOfNonneg_of_ne k Γ
    (le_of_lt (S.terminal.terminal.chain.stepValue_pos k Γ 0)) hc

private noncomputable def terminalOrdinalNextCoeff
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) : k :=
  Classical.choose (S.terminalOrdinalNextState_shift_sub_eq_singleOfNonneg
    k Γ hfixed hbelow hno)

private theorem terminalOrdinalNextCoeff_spec
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) :
    (S.terminalOrdinalNextState k Γ hfixed hbelow hno).shift - S.shift =
      singleOfNonneg k Γ
        (S.terminal.terminal.chain.stepValue k Γ 0)
        (terminalOrdinalNextCoeff k Γ hfixed hbelow S hno)
        (le_of_lt (S.terminal.terminal.chain.stepValue_pos k Γ 0)) := by
  exact (Classical.choose_spec (S.terminalOrdinalNextState_shift_sub_eq_singleOfNonneg
    k Γ hfixed hbelow hno)).2

private noncomputable def terminalOrdinalPrefixIncrementSummableFamily
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal}
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0)) :
    HahnSeries.SummableFamily Γ k (Set.Iio o) :=
  singleInjectivePWOSummableFamily k Γ
    (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0)
    (fun i => terminalOrdinalNextCoeff k Γ hfixed hbelow (S i.1) hno)
    hstrict.injective
    ((isWF_range_of_strictMono hstrict).isPWO)

private theorem terminalOrdinalPrefixIncrementSummableFamily_apply
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal}
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0)) (i : Set.Iio o) :
    terminalOrdinalPrefixIncrementSummableFamily
        k Γ hfixed hbelow S hno hstrict i =
      ofLex ((((S i.1).terminalOrdinalNextState
        k Γ hfixed hbelow hno).shift - (S i.1).shift : valuationSubring k Γ) :
          HahnField k Γ) := by
  have hnext := terminalOrdinalNextCoeff_spec
    k Γ hfixed hbelow (S i.1) hno
  have hsucc := congrArg
    (fun x : valuationSubring k Γ => ofLex (x : HahnField k Γ)) hnext
  change HahnSeries.single
      ((S i.1).terminal.terminal.chain.stepValue k Γ 0)
      (terminalOrdinalNextCoeff k Γ hfixed hbelow (S i.1) hno) = _
  simpa [singleOfNonneg_coe] using hsucc.symm

private theorem terminalOrdinalPrefixIncrement_hstrict_restrict
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    {o : Ordinal}
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0))
    (i : Set.Iio o) :
    StrictMono (fun j : Set.Iio i.1 =>
      (S j.1).terminal.terminal.chain.stepValue k Γ 0) := by
  let emb : Set.Iio i.1 ↪ Set.Iio o :=
    { toFun := fun j => ⟨j.1, by
          have hji : j.1 < i.1 := by simpa only [Set.mem_Iio] using j.2
          have hio : i.1 < o := by simpa only [Set.mem_Iio] using i.2
          exact hji.trans hio⟩
      inj' := by
        intro j l h
        apply Subtype.ext
        simpa using congrArg Subtype.val h }
  intro j l hjl
  exact hstrict (show emb j < emb l by
    change j.1 < l.1
    exact hjl)

private theorem terminalOrdinalPrefixIncrement_hsum_coeff_eq_of_lt_rank
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal}
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0))
    (i : Set.Iio o) {γ : Γ}
    (hγ : γ < (S i.1).terminal.terminal.chain.stepValue k Γ 0) :
    (terminalOrdinalPrefixIncrementSummableFamily
      k Γ hfixed hbelow S hno hstrict).hsum.coeff γ =
      (terminalOrdinalPrefixIncrementSummableFamily
        k Γ hfixed hbelow S hno
        (terminalOrdinalPrefixIncrement_hstrict_restrict
          k Γ S hstrict i)).hsum.coeff γ := by
  let emb : Set.Iio i.1 ↪ Set.Iio o :=
    { toFun := fun j => ⟨j.1, by
          have hji : j.1 < i.1 := by simpa only [Set.mem_Iio] using j.2
          have hio : i.1 < o := by simpa only [Set.mem_Iio] using i.2
          exact hji.trans hio⟩
      inj' := by
        intro j l h
        apply Subtype.ext
        simpa using congrArg Subtype.val h }
  let P : HahnSeries.SummableFamily Γ k (Set.Iio i.1) :=
      terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno
      (terminalOrdinalPrefixIncrement_hstrict_restrict
        k Γ S hstrict i)
  let A : HahnSeries.SummableFamily Γ k (Set.Iio o) :=
    terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno hstrict
  have hterm : ∀ j : Set.Iio o, (A j).coeff γ = (P.embDomain emb j).coeff γ := by
    intro j
    by_cases hj : j.1 < i.1
    · let j' : Set.Iio i.1 := ⟨j.1, hj⟩
      have hemb : emb j' = j := Subtype.ext rfl
      rw [← hemb, HahnSeries.SummableFamily.embDomain_image]
      rfl
    · have hji : i.1 ≤ j.1 := le_of_not_gt hj
      have hrank :
          (S i.1).terminal.terminal.chain.stepValue k Γ 0 ≤
            (S j.1).terminal.terminal.chain.stepValue k Γ 0 := by
        exact hstrict.monotone (show i ≤ j by
          change i.1 ≤ j.1
          exact hji)
      have hzero : (A j).coeff γ = 0 := by
        change (HahnSeries.single
          ((S j.1).terminal.terminal.chain.stepValue k Γ 0)
          (terminalOrdinalNextCoeff k Γ hfixed hbelow (S j.1) hno)).coeff γ = 0
        exact HahnSeries.coeff_single_of_ne (fun hval =>
          (not_lt_of_ge (hrank.trans_eq hval.symm)) hγ)
      have hnotrange : j ∉ Set.range emb := by
        rintro ⟨l, rfl⟩
        apply hj
        change l.1 < i.1
        exact l.2
      rw [hzero,
        HahnSeries.SummableFamily.embDomain_of_notMem_range (s := P) (f := emb) hnotrange,
        HahnSeries.coeff_zero]
  calc
    A.hsum.coeff γ = ∑ᶠ j : Set.Iio o, (A j).coeff γ := by
      rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = ∑ᶠ j : Set.Iio o, (P.embDomain emb j).coeff γ := finsum_congr hterm
    _ = (P.embDomain emb).hsum.coeff γ := by
      rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = P.hsum.coeff γ := by
      rw [HahnSeries.SummableFamily.hsum_embDomain]

private theorem terminalOrdinalPrefixIncrement_hsum_succ_eq_add
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal}
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0))
    (hstrictSucc : StrictMono (fun i : Set.Iio (o + 1) =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0)) :
    (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno hstrictSucc).hsum =
      (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno hstrict).hsum +
        terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno hstrictSucc
          ⟨o, by
            change o < Order.succ o
            exact Order.lt_succ o⟩ := by
  classical
  let emb : Set.Iio o ↪ Set.Iio (o + 1) :=
    { toFun := fun i => ⟨i.1, by
          have hi : i.1 < o := by simpa only [Set.mem_Iio] using i.2
          exact hi.trans (by
            change o < Order.succ o
            exact Order.lt_succ o)⟩
      inj' := by
        intro i j h
        apply Subtype.ext
        simpa using congrArg Subtype.val h }
  let i₀ : Set.Iio (o + 1) :=
    ⟨o, by
      change o < Order.succ o
      exact Order.lt_succ o⟩
  let A := terminalOrdinalPrefixIncrementSummableFamily
    k Γ hfixed hbelow S hno hstrictSucc
  let B := terminalOrdinalPrefixIncrementSummableFamily
    k Γ hfixed hbelow S hno hstrict
  let C := B.embDomain emb + HahnSeries.SummableFamily.single i₀ (A i₀)
  have hfamily : A = C := by
    apply HahnSeries.SummableFamily.ext
    intro i
    by_cases hi : i.1 < o
    · let j : Set.Iio o := ⟨i.1, hi⟩
      have hemb : emb j = i := Subtype.ext rfl
      have hne : i ≠ i₀ := by
        intro h
        have : i.1 = o := congrArg Subtype.val h
        exact (not_lt_of_ge (le_of_eq this.symm)) hi
      change A i = (B.embDomain emb) i +
        (HahnSeries.SummableFamily.single i₀ (A i₀)) i
      rw [← hemb, HahnSeries.SummableFamily.embDomain_image]
      have hne' : emb j ≠ i₀ := by
        intro h
        exact hne (hemb.symm.trans h)
      have hsingle :
          (HahnSeries.SummableFamily.single i₀ (A i₀)) (emb j) = 0 := by
        rw [HahnSeries.SummableFamily.single_toFun, Pi.single_eq_of_ne hne']
      rw [hsingle, add_zero]
      change HahnSeries.single
          ((S j.1).terminal.terminal.chain.stepValue k Γ 0)
          (terminalOrdinalNextCoeff k Γ hfixed hbelow (S j.1) hno) =
        HahnSeries.single
          ((S j.1).terminal.terminal.chain.stepValue k Γ 0)
          (terminalOrdinalNextCoeff k Γ hfixed hbelow (S j.1) hno)
      rfl
    · have hilto : i.1 < o + 1 := by simpa only [Set.mem_Iio] using i.2
      have hile : i.1 ≤ o := (Order.lt_succ_iff.mp hilto)
      have hieq : i.1 = o := le_antisymm hile (le_of_not_gt hi)
      have hi₀ : i = i₀ := Subtype.ext hieq
      have hnotrange : i₀ ∉ Set.range emb := by
        rintro ⟨j, hj⟩
        have hj_eq : j.1 = o := congrArg Subtype.val hj
        exact (not_lt_of_ge (le_of_eq hj_eq.symm)) j.2
      change A i = (B.embDomain emb) i +
        (HahnSeries.SummableFamily.single i₀ (A i₀)) i
      rw [hi₀, HahnSeries.SummableFamily.embDomain_of_notMem_range
        (s := B) (f := emb) hnotrange]
      simp
  calc
    A.hsum = C.hsum := congrArg (fun D : HahnSeries.SummableFamily Γ k (Set.Iio (o + 1)) => D.hsum)
      hfamily
    _ = B.hsum + (HahnSeries.SummableFamily.single i₀ (A i₀)).hsum := by
      rw [HahnSeries.SummableFamily.hsum_add,
        HahnSeries.SummableFamily.hsum_embDomain]
    _ = B.hsum + A i₀ := by
      rw [HahnSeries.SummableFamily.hsum_single]

private theorem
    firstStep_lt_terminalOrdinalNextState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0) :
    S.terminal.terminal.chain.stepValue k Γ 0 <
      (S.terminalOrdinalNextState k Γ hfixed hbelow hno).terminal.terminal.chain.stepValue
        k Γ 0 := by
  classical
  by_cases hedge : Nonempty (RankCoherentLowerEdge k Γ S)
  · let E := S.chosenRankCoherentLowerEdge k Γ hedge
    rw [S.terminalOrdinalNextState_eq_lowerEdgeRecoveryState
      k Γ hfixed hbelow hno hedge]
    have hlt := S.delta_lt_lowerEdgeRecovery_firstStep
      k Γ hfixed hbelow hno E.obstruction
    rw [E.delta_eq_firstStep] at hlt
    exact hlt
  · rw [S.terminalOrdinalNextState_eq_advanceFirstSource
      k Γ hfixed hbelow hno hedge]
    exact S.firstStep_lt_advanceFirstSource k Γ

private theorem terminalOrdinalNextState_eval_sub_addVal_eq_nsmul_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0) :
    addVal k Γ
        (F0.eval (S.shift : HahnField k Γ) -
          F0.eval ((S.terminalOrdinalNextState
            k Γ hfixed hbelow hno).shift : HahnField k Γ)) =
      ((m • S.terminal.terminal.chain.stepValue k Γ 0 : Γ) : WithTop Γ) := by
  have hrank := S.firstStep_lt_terminalOrdinalNextState k Γ hfixed hbelow hno
  have hscale : m • S.terminal.terminal.chain.stepValue k Γ 0 <
      m • (S.terminalOrdinalNextState
        k Γ hfixed hbelow hno).terminal.terminal.chain.stepValue k Γ 0 :=
    (nsmul_right_strictMono (M := Γ)
      (Nat.ne_of_gt (zero_lt_one.trans S.terminal.terminal.chain.one_lt))) hrank
  have heval : addVal k Γ (F0.eval (S.shift : HahnField k Γ)) <
      addVal k Γ (F0.eval ((S.terminalOrdinalNextState
        k Γ hfixed hbelow hno).shift : HahnField k Γ)) := by
    rw [S.shift_eval_addVal_eq_nsmul_firstStep k Γ,
      (S.terminalOrdinalNextState
        k Γ hfixed hbelow hno).shift_eval_addVal_eq_nsmul_firstStep k Γ]
    exact WithTop.coe_lt_coe.mpr hscale
  calc
    addVal k Γ
        (F0.eval (S.shift : HahnField k Γ) -
          F0.eval ((S.terminalOrdinalNextState
            k Γ hfixed hbelow hno).shift : HahnField k Γ)) =
        addVal k Γ (F0.eval (S.shift : HahnField k Γ)) := by
          simpa [addVal_apply, map_sub] using
            (HahnSeries.orderTop_sub (R := k) (Γ := Γ) heval)
    _ = ((m • S.terminal.terminal.chain.stepValue k Γ 0 : Γ) : WithTop Γ) :=
      S.shift_eval_addVal_eq_nsmul_firstStep k Γ

private theorem terminalOrdinalNextState_eval_coeff_eq_of_lt_nsmul_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0) {γ : Γ}
    (hγ : γ < m • S.terminal.terminal.chain.stepValue k Γ 0) :
    (ofLex (F0.eval ((S.terminalOrdinalNextState
      k Γ hfixed hbelow hno).shift : HahnField k Γ))).coeff γ =
      (ofLex (F0.eval (S.shift : HahnField k Γ))).coeff γ := by
  let B := ofLex
    (F0.eval (S.shift : HahnField k Γ) -
      F0.eval ((S.terminalOrdinalNextState
        k Γ hfixed hbelow hno).shift : HahnField k Γ))
  have horder : B.orderTop =
      ((m • S.terminal.terminal.chain.stepValue k Γ 0 : Γ) : WithTop Γ) := by
    simpa [B, addVal_apply] using
      S.terminalOrdinalNextState_eval_sub_addVal_eq_nsmul_firstStep
        k Γ hfixed hbelow hno
  have hzero : B.coeff γ = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [horder]
      exact WithTop.coe_lt_coe.mpr hγ)
  change
    (ofLex (F0.eval (S.shift : HahnField k Γ))).coeff γ -
      (ofLex (F0.eval ((S.terminalOrdinalNextState
        k Γ hfixed hbelow hno).shift : HahnField k Γ))).coeff γ = 0 at hzero
  exact (sub_eq_zero.mp hzero).symm

private theorem
    terminalOrdinalNextState_shift_coeff_eq_of_lt_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0) {γ : Γ}
    (hγ : γ < S.terminal.terminal.chain.stepValue k Γ 0) :
    (ofLex ((S.terminalOrdinalNextState k Γ hfixed hbelow hno).shift : HahnField k Γ)).coeff
        γ = (ofLex (S.shift : HahnField k Γ)).coeff γ := by
  let B := ofLex
    (((S.terminalOrdinalNextState k Γ hfixed hbelow hno).shift : HahnField k Γ) -
      (S.shift : HahnField k Γ))
  have horder : B.orderTop =
      (S.terminal.terminal.chain.stepValue k Γ 0 : WithTop Γ) := by
    simpa [B, addVal_apply] using
      S.terminalOrdinalNextState_shift_sub_addVal_eq_firstStep
        k Γ hfixed hbelow hno
  have hzero : B.coeff γ = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [horder]
      exact WithTop.coe_lt_coe.mpr hγ)
  change
    (ofLex ((S.terminalOrdinalNextState k Γ hfixed hbelow hno).shift : HahnField k Γ)).coeff
        γ - (ofLex (S.shift : HahnField k Γ)).coeff γ = 0 at hzero
  exact sub_eq_zero.mp hzero

/-- Product indices used to expose the finite coefficient dependence of a power of an `hsum`. -/
private theorem terminalOrdinalStableLimitShift_of_prefix_hsum
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal} (ho : Order.IsSuccLimit o)
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (C : KSameMultiplicityOrdinalJetChain k Γ (Set.Iio o) F m)
    (hC : ∀ i : Set.Iio o, C.state i = S i.1)
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0))
    (hprefix : ∀ i : Set.Iio o,
      ofLex ((S i.1).shift : HahnField k Γ) =
        (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno
          (terminalOrdinalPrefixIncrement_hstrict_restrict
            k Γ S hstrict i)).hsum) :
    ofLex ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift : HahnField k Γ) =
      (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno hstrict).hsum := by
  let A := terminalOrdinalPrefixIncrementSummableFamily
    k Γ hfixed hbelow S hno hstrict
  ext γ
  change (C.stableHahnSeries k Γ).coeff γ = A.hsum.coeff γ
  by_cases hcut : ∃ i : Set.Iio o, γ < C.rank k Γ i
  · let i : Set.Iio o := Classical.choose hcut
    have hiγ : γ < C.rank k Γ i := Classical.choose_spec hcut
    have hstable := C.stableCoeff_eq_state_of_lt_rank k Γ hiγ
    have hstate : (ofLex ((C.state i).shift : HahnField k Γ)).coeff γ =
        (ofLex ((S i.1).shift : HahnField k Γ)).coeff γ := by
      rw [hC i]
    have hiγ' : γ < (S i.1).terminal.terminal.chain.stepValue k Γ 0 := by
      rw [← hC i]
      exact hiγ
    have hprefix_i := congrArg (fun x : HahnSeries Γ k => x.coeff γ) (hprefix i)
    have hrestrict := terminalOrdinalPrefixIncrement_hsum_coeff_eq_of_lt_rank
      k Γ hfixed hbelow S hno hstrict i hiγ'
    calc
      (C.stableHahnSeries k Γ).coeff γ = C.stableCoeff k Γ γ := by
        rfl
      _ = (ofLex ((C.state i).shift : HahnField k Γ)).coeff γ := hstable
      _ = (ofLex ((S i.1).shift : HahnField k Γ)).coeff γ := hstate
      _ = (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno
          (terminalOrdinalPrefixIncrement_hstrict_restrict
            k Γ S hstrict i)).hsum.coeff γ := hprefix_i
      _ = A.hsum.coeff γ := hrestrict.symm
  · have hstable : C.stableCoeff k Γ γ = 0 := by
      rw [KSameMultiplicityOrdinalJetChain.stableCoeff, dif_neg hcut]
    have hzero : A.hsum.coeff γ = 0 := by
      rw [HahnSeries.SummableFamily.coeff_hsum]
      rw [finsum_eq_zero_of_forall_eq_zero]
      intro i
      change (HahnSeries.single
        ((S i.1).terminal.terminal.chain.stepValue k Γ 0)
        (terminalOrdinalNextCoeff k Γ hfixed hbelow (S i.1) hno)).coeff γ = 0
      exact HahnSeries.coeff_single_of_ne (fun hval => by
        let j : Set.Iio o := ⟨Order.succ i.1, ho.succ_lt i.2⟩
        have hij : i < j := by
          change i.1 < Order.succ i.1
          exact Order.lt_succ _
        have hγj : γ < (S j.1).terminal.terminal.chain.stepValue k Γ 0 := by
          simpa [hval] using hstrict hij
        apply hcut
        refine ⟨j, ?_⟩
        rw [KSameMultiplicityOrdinalJetChain.rank, hC j]
        exact hγj)
    change C.stableCoeff k Γ γ = A.hsum.coeff γ
    rw [hstable, hzero]

private theorem terminalOrdinalPrefix_exists_gt_finset
    {o : Ordinal} (ho : Order.IsSuccLimit o) (i : Set.Iio o)
    (U : Finset (Set.Iio o)) :
    ∃ j : Set.Iio o, i < j ∧ ∀ l ∈ U, l < j := by
  classical
  let V := insert i U
  let a := V.max' (by simp [V])
  let j : Set.Iio o := ⟨Order.succ a.1, ho.succ_lt a.2⟩
  refine ⟨j, ?_, ?_⟩
  · change i.1 < j.1
    exact lt_of_le_of_lt
      (show i.1 ≤ a.1 from Finset.le_max' V i (by simp [V]))
      (Order.lt_succ _)
  · intro l hl
    change l.1 < j.1
    exact lt_of_le_of_lt
      (show l.1 ≤ a.1 from Finset.le_max' V l (by simp [V, hl]))
      (Order.lt_succ _)

private def terminalOrdinalPrefixIncrementOptionEmbedding (o : Ordinal) :
    Set.Iio o ↪ Option (Set.Iio o) :=
  { toFun := some
    inj' := Option.some_injective (Set.Iio o) }

private noncomputable def terminalOrdinalPrefixIncrementOptionFamily
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal}
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0)) :
    HahnSeries.SummableFamily Γ k (Option (Set.Iio o)) :=
  (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno hstrict).embDomain
    (terminalOrdinalPrefixIncrementOptionEmbedding o)

private theorem terminalOrdinalPrefixIncrementOptionFamily_predTrunc_hsum
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal}
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0))
    (j : Set.Iio o) :
    (HahnSummablePowerTrunc (k := k) (Γ := Γ)
        (terminalOrdinalPrefixIncrementOptionFamily
          k Γ hfixed hbelow S hno hstrict)
        (fun i : Set.Iio o => i.1 < j.1)).hsum =
      (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno
        (terminalOrdinalPrefixIncrement_hstrict_restrict k Γ S hstrict j)).hsum := by
  classical
  let p : Set.Iio o → Prop := fun i => i.1 < j.1
  let hrestrict := terminalOrdinalPrefixIncrement_hstrict_restrict
    k Γ S hstrict j
  let P := terminalOrdinalPrefixIncrementSummableFamily
    k Γ hfixed hbelow S hno hrestrict
  let embSome := terminalOrdinalPrefixIncrementOptionEmbedding o
  let emb : Set.Iio j.1 ↪ Option (Set.Iio o) :=
    { toFun := fun i => some ⟨i.1, (show i.1 < j.1 from i.2).trans j.2⟩
      inj' := by
        intro i l h
        change some _ = some _ at h
        have h' :
            (⟨i.1, (show i.1 < j.1 from i.2).trans j.2⟩ : Set.Iio o) =
              ⟨l.1, (show l.1 < j.1 from l.2).trans j.2⟩ :=
          Option.some.inj h
        apply Subtype.ext
        exact congrArg (fun x : Set.Iio o => x.1) h' }
  let A := terminalOrdinalPrefixIncrementOptionFamily
    k Γ hfixed hbelow S hno hstrict
  have hfamily :
      HahnSummablePowerTrunc (k := k) (Γ := Γ) A p = P.embDomain emb := by
    apply HahnSeries.SummableFamily.ext
    intro i
    cases i with
    | none =>
        have hnone : (none : Option (Set.Iio o)) ∉ Set.range emb := by
          rintro ⟨l, hl⟩
          cases hl
        have hA_none : A none = 0 := by
          change
            (terminalOrdinalPrefixIncrementSummableFamily
              k Γ hfixed hbelow S hno hstrict).embDomain embSome none = 0
          exact HahnSeries.SummableFamily.embDomain_of_notMem_range
            (terminalOrdinalPrefixIncrementSummableFamily
              k Γ hfixed hbelow S hno hstrict) embSome (by
                rintro ⟨x, hx⟩
                change (some x : Option (Set.Iio o)) = none at hx
                cases hx)
        rw [HahnSeries.SummableFamily.embDomain_of_notMem_range
          (s := P) (f := emb) hnone]
        simpa [HahnSummablePowerTrunc] using hA_none
    | some i =>
        by_cases hi : i.1 < j.1
        · let l : Set.Iio j.1 := ⟨i.1, hi⟩
          have hli : emb l = (some i : Option (Set.Iio o)) := by
            change some _ = some _
            apply congrArg (fun x : Set.Iio o => some x)
            apply Subtype.ext
            rfl
          rw [← hli, HahnSeries.SummableFamily.embDomain_image]
          have hAi : A (some i) = P l := by
            change
              (terminalOrdinalPrefixIncrementSummableFamily
              k Γ hfixed hbelow S hno hstrict).embDomain embSome (embSome i) = P l
            rw [HahnSeries.SummableFamily.embDomain_image]
            rfl
          simp only [HahnSummablePowerTrunc,
            HahnSeries.SummableFamily.smulFamily_toFun]
          rw [hli]
          have hpi : p i := by simpa [p] using hi
          have hsome : (some i : Option (Set.Iio o)).elim True p := hpi
          rw [if_pos hsome, one_smul]
          exact hAi
        · have hnot : some i ∉ Set.range emb := by
            rintro ⟨l, hl⟩
            change some _ = some i at hl
            have hval : l.1 = i.1 := congrArg Subtype.val (Option.some.inj hl)
            exact hi (hval ▸ l.2)
          rw [HahnSeries.SummableFamily.embDomain_of_notMem_range
            (s := P) (f := emb) hnot]
          have hpi : ¬p i := by simpa [p] using hi
          simp [HahnSummablePowerTrunc, hpi]
  rw [hfamily, HahnSeries.SummableFamily.hsum_embDomain]

private theorem terminalOrdinalStableLimit_eval_coeff_eq_of_lt_nsmul_rank
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (S : Ordinal → KSameMultiplicityFixedStepTerminalShiftState k Γ F m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : KSameMultiplicityOrdinalJetChain k Γ (Set.Iio o) F m)
    (hC : ∀ i : Set.Iio o, C.state i = S i.1)
    (hstrict : StrictMono (fun i : Set.Iio o =>
      (S i.1).terminal.terminal.chain.stepValue k Γ 0))
    (hprefix : ∀ i : Set.Iio o,
      ofLex ((S i.1).shift : HahnField k Γ) =
        (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow S hno
          (terminalOrdinalPrefixIncrement_hstrict_restrict
            k Γ S hstrict i)).hsum)
    (i : Set.Iio o) {γ : Γ}
    (hγ : γ < m • (S i.1).terminal.terminal.chain.stepValue k Γ 0) :
    (ofLex (F.eval
      ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift : HahnField k Γ))).coeff γ =
      (ofLex (F.eval ((S i.1).shift : HahnField k Γ))).coeff γ := by
  classical
  have hstable := terminalOrdinalStableLimitShift_of_prefix_hsum
    k Γ hfixed hbelow T hno ho S C hC hstrict hprefix
  let A := terminalOrdinalPrefixIncrementOptionFamily
    k Γ hfixed hbelow S hno hstrict
  let P := F.map (OrdinalSupport.ofLexRingHom (k := k) (Γ := Γ))
  have hA :
      A.hsum =
        ofLex ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift :
          HahnField k Γ) := by
    change
      ((terminalOrdinalPrefixIncrementSummableFamily
          k Γ hfixed hbelow S hno hstrict).embDomain
        (terminalOrdinalPrefixIncrementOptionEmbedding o)).hsum = _
    rw [HahnSeries.SummableFamily.hsum_embDomain]
    exact hstable.symm
  let U := HahnSummableEvalCoeffSupport (k := k) (Γ := Γ) A P γ
  rcases terminalOrdinalPrefix_exists_gt_finset ho i U with ⟨j, hij, hUj⟩
  let p : Set.Iio o → Prop := fun a => a.1 < j.1
  have hUp : ∀ a ∈ U, p a := by
    intro a ha
    simpa [p] using hUj a ha
  have heval :
      (P.eval A.hsum).coeff γ =
        (P.eval
          (HahnSummablePowerTrunc (k := k) (Γ := Γ) A p).hsum).coeff γ := by
    apply HahnSummableFamily.eval_coeff_eq_predTrunc_of_support
      (k := k) (Γ := Γ) A p P γ
    intro a ha
    exact hUp a (by simpa [U] using ha)
  have htrunc :
      (HahnSummablePowerTrunc (k := k) (Γ := Γ) A p).hsum =
        ofLex ((S j.1).shift : HahnField k Γ) := by
    calc
      (HahnSummablePowerTrunc (k := k) (Γ := Γ) A p).hsum =
          (terminalOrdinalPrefixIncrementSummableFamily
            k Γ hfixed hbelow S hno
            (terminalOrdinalPrefixIncrement_hstrict_restrict
              k Γ S hstrict j)).hsum := by
        simpa [A, p] using
          terminalOrdinalPrefixIncrementOptionFamily_predTrunc_hsum
            k Γ hfixed hbelow S hno hstrict j
      _ = ofLex ((S j.1).shift : HahnField k Γ) := (hprefix j).symm
  have hstableEval :
      (ofLex (F.eval
        ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift :
          HahnField k Γ))).coeff γ =
        (ofLex (F.eval ((S j.1).shift : HahnField k Γ))).coeff γ := by
    calc
      (ofLex (F.eval
        ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift :
          HahnField k Γ))).coeff γ =
          (P.eval (ofLex
            ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift :
              HahnField k Γ))).coeff γ := by
        simpa [P] using congrArg (fun x : HahnSeries Γ k => x.coeff γ)
          (ofLexRingHom_eval k Γ F
            ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift :
              HahnField k Γ)).symm
      _ = (P.eval A.hsum).coeff γ := by rw [hA]
      _ = (P.eval
          (HahnSummablePowerTrunc (k := k) (Γ := Γ) A p).hsum).coeff γ := heval
      _ = (P.eval (ofLex ((S j.1).shift : HahnField k Γ))).coeff γ := by
        rw [htrunc]
      _ = (ofLex (F.eval ((S j.1).shift : HahnField k Γ))).coeff γ := by
        simpa [P] using congrArg (fun x : HahnSeries Γ k => x.coeff γ)
          (ofLexRingHom_eval k Γ F ((S j.1).shift : HahnField k Γ))
  have hrank :
      (S i.1).terminal.terminal.chain.stepValue k Γ 0 <
        (S j.1).terminal.terminal.chain.stepValue k Γ 0 :=
    hstrict hij
  have hmul :
      m • (S i.1).terminal.terminal.chain.stepValue k Γ 0 <
        m • (S j.1).terminal.terminal.chain.stepValue k Γ 0 :=
    (nsmul_right_strictMono (M := Γ)
      (Nat.ne_of_gt (zero_lt_one.trans
        (S i.1).terminal.terminal.chain.one_lt))) hrank
  have hγj : γ < m • (S j.1).terminal.terminal.chain.stepValue k Γ 0 :=
    hγ.trans hmul
  have hzero (r : Set.Iio o)
      (hr : γ < m • (S r.1).terminal.terminal.chain.stepValue k Γ 0) :
      (ofLex (F.eval ((S r.1).shift : HahnField k Γ))).coeff γ = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    change (γ : WithTop Γ) <
      addVal k Γ (F.eval ((S r.1).shift : HahnField k Γ))
    rw [(S r.1).shift_eval_addVal_eq_nsmul_firstStep k Γ]
    exact WithTop.coe_lt_coe.mpr hr
  calc
    (ofLex (F.eval
      ((C.stableLimitShiftState k Γ hfixed hbelow T hno).shift :
        HahnField k Γ))).coeff γ = 0 := hstableEval.trans (hzero j hγj)
    _ = (ofLex (F.eval ((S i.1).shift : HahnField k Γ))).coeff γ :=
      (hzero i hγ).symm

private noncomputable def iterateFixedLiftTerminalOrdinalPrefixState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) (o : Ordinal) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ F m := by
  classical
  exact Ordinal.limitRecOn o
    (KSameMultiplicityFixedStepTerminalShiftState.initial k Γ T)
    (fun _ S => S.terminalOrdinalNextState k Γ hfixed hbelow hno)
    (fun o _ho IH =>
      if hchain : ∃ C : KSameMultiplicityOrdinalJetChain
          k Γ (Set.Iio o) F m, ∀ i : Set.Iio o, C.state i = IH i.1 i.2 then
        (Classical.choose hchain).stableLimitShiftState k Γ hfixed hbelow T hno
      else KSameMultiplicityFixedStepTerminalShiftState.initial k Γ T)

private theorem iterateFixedLiftTerminalOrdinalPrefixState_zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) :
    iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno 0 =
      KSameMultiplicityFixedStepTerminalShiftState.initial k Γ T := by
  unfold iterateFixedLiftTerminalOrdinalPrefixState
  rw [Ordinal.limitRecOn_zero]

private theorem iterateFixedLiftTerminalOrdinalPrefixState_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) (o : Ordinal) :
    iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno (o + 1) =
      (iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno o
        |>.terminalOrdinalNextState k Γ hfixed hbelow hno) := by
  unfold iterateFixedLiftTerminalOrdinalPrefixState
  rw [Ordinal.limitRecOn_add_one]

private theorem iterateFixedLiftTerminalOrdinalPrefixState_limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) {o : Ordinal} (ho : Order.IsSuccLimit o)
    (hchain : ∃ C : KSameMultiplicityOrdinalJetChain
        k Γ (Set.Iio o) F m, ∀ i : Set.Iio o, C.state i =
          iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno i.1) :
    ∃ C : KSameMultiplicityOrdinalJetChain k Γ (Set.Iio o) F m,
      (∀ i : Set.Iio o, C.state i =
        iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno i.1) ∧
      iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno o =
        C.stableLimitShiftState k Γ hfixed hbelow T hno := by
  classical
  unfold iterateFixedLiftTerminalOrdinalPrefixState
  rw [Ordinal.limitRecOn_limit _ _ _ _ ho]
  split
  next h =>
    refine ⟨Classical.choose h, ?_, rfl⟩
    intro i
    simpa [iterateFixedLiftTerminalOrdinalPrefixState] using Classical.choose_spec h i
  next hnot =>
    exfalso
    apply hnot
    rcases hchain with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro i
    simpa [iterateFixedLiftTerminalOrdinalPrefixState] using hC i

private theorem iterateFixedLiftTerminalOrdinalPrefixState_invariant
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) (o : Ordinal) :
    let S := iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno
    ((∀ i < o, (S i).terminal.terminal.chain.stepValue k Γ 0 <
        (S o).terminal.terminal.chain.stepValue k Γ 0) ∧
      (∀ i ≤ o, ∀ {γ : Γ},
        γ < (S i).terminal.terminal.chain.stepValue k Γ 0 →
          (ofLex ((S o).shift : HahnField k Γ)).coeff γ =
            (ofLex ((S i).shift : HahnField k Γ)).coeff γ) ∧
      (∀ i ≤ o, ∀ {γ : Γ},
        γ < m • (S i).terminal.terminal.chain.stepValue k Γ 0 →
          (ofLex (F.eval ((S o).shift : HahnField k Γ))).coeff γ =
            (ofLex (F.eval ((S i).shift : HahnField k Γ))).coeff γ) ∧
      ∃ hstrict : StrictMono (fun i : Set.Iio o =>
        (S i.1).terminal.terminal.chain.stepValue k Γ 0),
        ofLex ((S o).shift : HahnField k Γ) =
          (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow
            S hno hstrict).hsum) := by
  let S := iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno
  change
    ((∀ i < o, (S i).terminal.terminal.chain.stepValue k Γ 0 <
        (S o).terminal.terminal.chain.stepValue k Γ 0) ∧
      (∀ i ≤ o, ∀ {γ : Γ},
        γ < (S i).terminal.terminal.chain.stepValue k Γ 0 →
          (ofLex ((S o).shift : HahnField k Γ)).coeff γ =
            (ofLex ((S i).shift : HahnField k Γ)).coeff γ) ∧
      (∀ i ≤ o, ∀ {γ : Γ},
        γ < m • (S i).terminal.terminal.chain.stepValue k Γ 0 →
          (ofLex (F.eval ((S o).shift : HahnField k Γ))).coeff γ =
            (ofLex (F.eval ((S i).shift : HahnField k Γ))).coeff γ) ∧
      ∃ hstrict : StrictMono (fun i : Set.Iio o =>
        (S i.1).terminal.terminal.chain.stepValue k Γ 0),
        ofLex ((S o).shift : HahnField k Γ) =
          (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow
            S hno hstrict).hsum)
  induction o using Ordinal.limitRecOn with
  | zero =>
      constructor
      · intro i hi
        exact False.elim ((not_lt_of_ge bot_le) hi)
      · constructor
        · intro i hi
          have hiz : i = 0 := le_antisymm hi bot_le
          subst i
          intro γ hγ
          rfl
        · constructor
          · intro i hi
            have hiz : i = 0 := le_antisymm hi bot_le
            subst i
            intro γ hγ
            rfl
          · have hzero : S 0 =
                KSameMultiplicityFixedStepTerminalShiftState.initial k Γ T := by
              simpa [S] using iterateFixedLiftTerminalOrdinalPrefixState_zero
                k Γ hfixed hbelow T hno
            let hstrict : StrictMono (fun i : Set.Iio (0 : Ordinal) =>
                (S i.1).terminal.terminal.chain.stepValue k Γ 0) := by
              intro i j hij
              exact False.elim ((not_lt_of_ge bot_le)
                (show i.1 < (0 : Ordinal) from i.2))
            refine ⟨hstrict, ?_⟩
            rw [hzero]
            ext γ
            change (0 : k) = _
            rw [HahnSeries.SummableFamily.coeff_hsum]
            symm
            apply finsum_eq_zero_of_forall_eq_zero
            intro i
            exact False.elim ((not_lt_of_ge bot_le)
              (show i.1 < (0 : Ordinal) from i.2))
  | add_one o IH =>
      rcases IH with ⟨hprogress, hshift, heval, hprefix⟩
      have hsucc : S (o + 1) =
          (S o).terminalOrdinalNextState k Γ hfixed hbelow hno := by
        simpa [S] using iterateFixedLiftTerminalOrdinalPrefixState_succ
          k Γ hfixed hbelow T hno o
      constructor
      · intro i hi
        have hi' : i < Order.succ o := by
          rw [Order.succ_eq_add_one]
          exact hi
        have hio : i ≤ o := Order.lt_succ_iff.mp hi'
        rw [hsucc]
        rcases hio.eq_or_lt with rfl | hilt
        · exact (S i).firstStep_lt_terminalOrdinalNextState
            k Γ hfixed hbelow hno
        · exact (hprogress i hilt).trans
            ((S o).firstStep_lt_terminalOrdinalNextState
              k Γ hfixed hbelow hno)
      · constructor
        · intro i hi γ hγ
          rcases hi.eq_or_lt with rfl | hilt
          · rfl
          · have hilt' : i < Order.succ o := by
              rw [Order.succ_eq_add_one]
              exact hilt
            have hio : i ≤ o := Order.lt_succ_iff.mp hilt'
            have hγo : γ < (S o).terminal.terminal.chain.stepValue k Γ 0 := by
              rcases hio.eq_or_lt with rfl | hio'
              · exact hγ
              · exact hγ.trans (hprogress i hio')
            rw [hsucc]
            exact ((S o).terminalOrdinalNextState_shift_coeff_eq_of_lt_firstStep
              k Γ hfixed hbelow hno hγo).trans (hshift i hio hγ)
        · constructor
          · intro i hi γ hγ
            rcases hi.eq_or_lt with rfl | hilt
            · rfl
            · have hilt' : i < Order.succ o := by
                rw [Order.succ_eq_add_one]
                exact hilt
              have hio : i ≤ o := Order.lt_succ_iff.mp hilt'
              have hrank :
                  (S i).terminal.terminal.chain.stepValue k Γ 0 ≤
                    (S o).terminal.terminal.chain.stepValue k Γ 0 := by
                rcases hio.eq_or_lt with rfl | hio'
                · exact le_rfl
                · exact (hprogress i hio').le
              have hγo : γ < m •
                  (S o).terminal.terminal.chain.stepValue k Γ 0 :=
                hγ.trans_le ((nsmul_right_strictMono (M := Γ)
                  (Nat.ne_of_gt (zero_lt_one.trans
                    (S o).terminal.terminal.chain.one_lt))).monotone hrank)
              have hstable :
                  (ofLex (F.eval ((S (o + 1)).shift : HahnField k Γ))).coeff γ =
                    (ofLex (F.eval ((S o).shift : HahnField k Γ))).coeff γ := by
                rw [hsucc]
                exact (S o).terminalOrdinalNextState_eval_coeff_eq_of_lt_nsmul_firstStep
                  k Γ hfixed hbelow hno hγo
              exact hstable.trans (heval i hio hγ)
          · rcases hprefix with ⟨hstrict, hprefix⟩
            have hstrictSucc : StrictMono (fun i : Set.Iio (o + 1) =>
                (S i.1).terminal.terminal.chain.stepValue k Γ 0) := by
              intro i j hij
              change i.1 < j.1 at hij
              have hjlt : j.1 < o + 1 := by
                simpa only [Set.mem_Iio] using j.2
              have hjo : j.1 ≤ o := Order.lt_succ_iff.mp hjlt
              rcases hjo.eq_or_lt with hjeq | hjo
              · have hij' : i.1 < o := by
                  simpa [hjeq] using hij
                change (S i.1).terminal.terminal.chain.stepValue k Γ 0 <
                  (S j.1).terminal.terminal.chain.stepValue k Γ 0
                rw [hjeq]
                exact hprogress i.1 hij'
              · let ii : Set.Iio o := ⟨i.1, hij.trans hjo⟩
                let jj : Set.Iio o := ⟨j.1, hjo⟩
                exact @hstrict ii jj hij
            let i₀ : Set.Iio (o + 1) :=
              ⟨o, by
                change o < Order.succ o
                exact Order.lt_succ o⟩
            have hterm := terminalOrdinalPrefixIncrementSummableFamily_apply
              k Γ hfixed hbelow S hno hstrictSucc i₀
            have hterm' :
                terminalOrdinalPrefixIncrementSummableFamily
                    k Γ hfixed hbelow S hno hstrictSucc i₀ =
                  ofLex (((S (o + 1)).shift - (S o).shift :
                    valuationSubring k Γ) : HahnField k Γ) := by
              simpa [i₀, hsucc] using hterm
            have hsplit : (S (o + 1)).shift =
                (S o).shift + ((S (o + 1)).shift - (S o).shift) := by
              rw [add_comm]
              exact (sub_add_cancel _ _).symm
            have hsplitH : ((S (o + 1)).shift : HahnField k Γ) =
                (S o).shift +
                  (((S (o + 1)).shift - (S o).shift :
                    valuationSubring k Γ) : HahnField k Γ) := by
              calc
                ((S (o + 1)).shift : HahnField k Γ) =
                    (((S o).shift + ((S (o + 1)).shift - (S o).shift) :
                      valuationSubring k Γ) : HahnField k Γ) :=
                  congrArg (fun x : valuationSubring k Γ =>
                    (x : HahnField k Γ)) hsplit
                _ = (S o).shift +
                    (((S (o + 1)).shift - (S o).shift :
                      valuationSubring k Γ) : HahnField k Γ) := by
                  simpa only [Algebra.algebraMap_ofSubsemiring_apply] using
                    (map_add (algebraMap (valuationSubring k Γ) (HahnField k Γ))
                      (S o).shift ((S (o + 1)).shift - (S o).shift))
            refine ⟨hstrictSucc, ?_⟩
            calc
              ofLex ((S (o + 1)).shift : HahnField k Γ) =
                  ofLex ((S o).shift : HahnField k Γ) +
                    ofLex (((S (o + 1)).shift - (S o).shift :
                      valuationSubring k Γ) : HahnField k Γ) := by
                rw [hsplitH, ofLex_add]
              _ = ofLex ((S o).shift : HahnField k Γ) +
                    terminalOrdinalPrefixIncrementSummableFamily
                      k Γ hfixed hbelow S hno hstrictSucc i₀ := by
                rw [hterm']
              _ = (terminalOrdinalPrefixIncrementSummableFamily
                    k Γ hfixed hbelow S hno hstrict).hsum +
                    terminalOrdinalPrefixIncrementSummableFamily
                      k Γ hfixed hbelow S hno hstrictSucc i₀ := by
                rw [hprefix]
              _ = (terminalOrdinalPrefixIncrementSummableFamily
                    k Γ hfixed hbelow S hno hstrictSucc).hsum := by
                symm
                simpa [i₀] using terminalOrdinalPrefixIncrement_hsum_succ_eq_add
                  k Γ hfixed hbelow S hno hstrict hstrictSucc
  | limit o ho IH =>
      have hprogress : ∀ j < o,
          ∀ i < j, (S i).terminal.terminal.chain.stepValue k Γ 0 <
            (S j).terminal.terminal.chain.stepValue k Γ 0 := by
        intro j hj
        exact (IH j hj).1
      let hstrict : StrictMono (fun i : Set.Iio o =>
          (S i.1).terminal.terminal.chain.stepValue k Γ 0) := by
        intro i j hij
        exact hprogress j.1 j.2 i.1 hij
      have hprefix : ∀ i : Set.Iio o,
          ofLex ((S i.1).shift : HahnField k Γ) =
            (terminalOrdinalPrefixIncrementSummableFamily k Γ hfixed hbelow
              S hno (terminalOrdinalPrefixIncrement_hstrict_restrict
                k Γ S hstrict i)).hsum := by
        intro i
        rcases (IH i.1 i.2) with ⟨_, _, _, hprefix_i⟩
        rcases hprefix_i with ⟨hstrict_i, hprefix_i⟩
        simpa using hprefix_i
      let C : KSameMultiplicityOrdinalJetChain
          k Γ (Set.Iio o) F m := {
        state := fun i => S i.1
        rank_strictMono := by
          intro i j hij
          exact hprogress j.1 j.2 i.1 hij
        shift_coeff_stable := by
          intro i j hij γ hγ
          rcases hij.eq_or_lt with rfl | hij'
          · rfl
          · exact (IH j.1 j.2).2.1 i.1 (le_of_lt hij') hγ }
      have hchain : ∃ D : KSameMultiplicityOrdinalJetChain
          k Γ (Set.Iio o) F m, ∀ i : Set.Iio o, D.state i = S i.1 :=
        ⟨C, fun _ => rfl⟩
      rcases iterateFixedLiftTerminalOrdinalPrefixState_limit
          k Γ hfixed hbelow T hno ho hchain with ⟨D, hD, hstate⟩
      change ∀ i : Set.Iio o, D.state i = S i.1 at hD
      change S o = D.stableLimitShiftState k Γ hfixed hbelow T hno at hstate
      let L := D.stableLimitShiftState k Γ hfixed hbelow T hno
      have hallLe : ∀ i : Set.Iio o, D.rank k Γ i ≤
          L.terminal.terminal.chain.stepValue k Γ 0 := by
        intro i
        have horder :
            ((m • D.rank k Γ i : Γ) : WithTop Γ) ≤
              (ofLex (F.eval (L.shift : HahnField k Γ))).orderTop := by
          apply HahnSeries.le_orderTop_iff_forall.mpr
          intro γ hγ
          have hγ' : γ < m • D.rank k Γ i := WithTop.coe_lt_coe.mp hγ
          have hγS : γ < m •
              (S i.1).terminal.terminal.chain.stepValue k Γ 0 := by
            change γ < m • (D.state i).terminal.terminal.chain.stepValue k Γ 0 at hγ'
            rw [hD i] at hγ'
            exact hγ'
          have heq := terminalOrdinalStableLimit_eval_coeff_eq_of_lt_nsmul_rank
            k Γ hfixed hbelow S T hno ho D hD hstrict hprefix i hγS
          have hzero :
              (ofLex (F.eval ((S i.1).shift : HahnField k Γ))).coeff γ = 0 := by
            apply HahnSeries.coeff_eq_zero_of_lt_orderTop
            change (γ : WithTop Γ) <
              addVal k Γ (F.eval ((S i.1).shift : HahnField k Γ))
            rw [(S i.1).shift_eval_addVal_eq_nsmul_firstStep k Γ]
            exact WithTop.coe_lt_coe.mpr hγS
          exact heq.trans hzero
        have horder' :
            ((m • D.rank k Γ i : Γ) : WithTop Γ) ≤
              addVal k Γ (F.eval (L.shift : HahnField k Γ)) := by
          simpa [addVal_apply] using horder
        rw [L.shift_eval_addVal_eq_nsmul_firstStep k Γ] at horder'
        have hscale : m • D.rank k Γ i ≤
            m • L.terminal.terminal.chain.stepValue k Γ 0 :=
          WithTop.coe_le_coe.mp horder'
        exact (nsmul_right_strictMono (M := Γ)
          (Nat.ne_of_gt (zero_lt_one.trans T.terminal.chain.one_lt))).le_iff_le.mp hscale
      have hprogressLimit : ∀ i : Set.Iio o, D.rank k Γ i <
          L.terminal.terminal.chain.stepValue k Γ 0 := by
        intro i
        let j : Set.Iio o := ⟨Order.succ i.1, ho.succ_lt i.2⟩
        have hij : i < j := by
          change i.1 < Order.succ i.1
          exact Order.lt_succ _
        have hstrictD : D.rank k Γ i < D.rank k Γ j := by
          change (D.state i).terminal.terminal.chain.stepValue k Γ 0 <
            (D.state j).terminal.terminal.chain.stepValue k Γ 0
          rw [hD i, hD j]
          exact hstrict hij
        exact hstrictD.trans_le (hallLe j)
      constructor
      · intro i hi
        let ii : Set.Iio o := ⟨i, hi⟩
        have hlt := hprogressLimit ii
        have hlt' : (S i).terminal.terminal.chain.stepValue k Γ 0 <
            L.terminal.terminal.chain.stepValue k Γ 0 := by
          change (D.state ii).terminal.terminal.chain.stepValue k Γ 0 <
            L.terminal.terminal.chain.stepValue k Γ 0 at hlt
          rw [hD ii] at hlt
          exact hlt
        rw [hstate]
        simpa [L, ii] using hlt'
      · constructor
        · intro i hi γ hγ
          rcases hi.eq_or_lt with rfl | hio
          · rfl
          · let ii : Set.Iio o := ⟨i, hio⟩
            have hγD : γ < D.rank k Γ ii := by
              change γ < (D.state ii).terminal.terminal.chain.stepValue k Γ 0
              rw [hD ii]
              exact hγ
            have heq := D.stableLimit_coeff_eq_state_of_lt_rank
              k Γ hfixed hbelow T hno (i := ii) hγD
            rw [hD ii] at heq
            rw [hstate]
            simpa [ii] using heq
        · constructor
          · intro i hi γ hγ
            rcases hi.eq_or_lt with rfl | hio
            · rfl
            · let ii : Set.Iio o := ⟨i, hio⟩
              have heq := terminalOrdinalStableLimit_eval_coeff_eq_of_lt_nsmul_rank
                k Γ hfixed hbelow S T hno ho D hD hstrict hprefix ii hγ
              rw [hstate]
              simpa [ii] using heq
          · refine ⟨hstrict, ?_⟩
            rw [hstate]
            exact terminalOrdinalStableLimitShift_of_prefix_hsum
              k Γ hfixed hbelow T hno ho S D hD hstrict hprefix

private theorem false_of_no_positiveRoot_fixedLiftTerminal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m)
    (hno : ¬ PositiveHahnRoot k Γ F) : False := by
  let H : Ordinal.{u_2} := (Order.succ (Cardinal.mk Γ)).ord
  let S : Ordinal.{u_2} → KSameMultiplicityFixedStepTerminalShiftState k Γ F m :=
    iterateFixedLiftTerminalOrdinalPrefixState k Γ hfixed hbelow T hno
  have hinvariant : ∀ o : Ordinal.{u_2}, ∀ i < o,
      (S i).terminal.terminal.chain.stepValue k Γ 0 <
        (S o).terminal.terminal.chain.stepValue k Γ 0 := by
    intro o i hi
    have h := iterateFixedLiftTerminalOrdinalPrefixState_invariant
      k Γ hfixed hbelow T hno o
    change
      ((∀ i < o, (S i).terminal.terminal.chain.stepValue k Γ 0 <
          (S o).terminal.terminal.chain.stepValue k Γ 0) ∧ _) at h
    exact h.1 i hi
  let f : H.ToType → Γ := fun i =>
    (S ((Ordinal.ToType.mk (o := H)).symm i).1).terminal.terminal.chain.stepValue k Γ 0
  have hf : StrictMono f := by
    intro i j hij
    exact hinvariant ((Ordinal.ToType.mk (o := H)).symm j).1
      ((Ordinal.ToType.mk (o := H)).symm i).1
      ((Ordinal.ToType.mk (o := H)).symm.strictMono hij)
  have hcard : Cardinal.mk H.ToType ≤ Cardinal.mk Γ :=
    Cardinal.mk_le_of_injective hf.injective
  change Cardinal.mk ((Order.succ (Cardinal.mk Γ)).ord.ToType) ≤ Cardinal.mk Γ at hcard
  rw [Cardinal.mk_ord_toType] at hcard
  exact (Order.lt_succ (Cardinal.mk Γ)).not_ge hcard

private theorem positiveHahnRoot_of_fixedLiftTerminal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m) :
    PositiveHahnRoot k Γ F := by
  by_contra hno
  exact false_of_no_positiveRoot_fixedLiftTerminal
    k Γ hfixed hbelow T hno

end KSameMultiplicityFixedStepTerminalShiftState

theorem positiveHahnRoot_of_edgeStep_rootOrStep_terminalResolution
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hstep : KSameMultiplicityRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m) :
    PositiveHahnRoot k Γ F := by
  let hfixed : KSameMultiplicityFixedLiftRootOrStepWithRootBelow k Γ := by
    intro F m hbelow hbranch D A hA
    rcases hstep hbelow hbranch with ⟨D', hD'⟩
    have hmap :
        D'.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ)) =
          D.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ)) := by
      rw [D'.map_eq, D.map_eq]
    have hlift : D'.lift = D.lift := by
      exact Polynomial.map_injective
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))
        (show Function.Injective
            (algebraMap (valuationSubring k Γ) (HahnField k Γ)) from
          fun a b h => Subtype.ext h) hmap
    rw [← hlift]
    exact hD' A hA
  exact KSameMultiplicityFixedStepTerminalShiftState.positiveHahnRoot_of_fixedLiftTerminal
    k Γ hfixed hbelow T

end KSameMultiplicityFixedStepTerminalObstructionData

open KSameMultiplicityFixedStepTerminalObstructionData

namespace KOddClusterFixedStepTerminalFromData

theorem positiveHahnRoot_of_edgeStep_rootOrStep_terminalResolution
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hstep : KSameMultiplicityRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (T : KOddClusterFixedStepTerminalFromData k Γ F m start)
    (hbranch : KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    PositiveHahnRoot k Γ F := by
  have hshift :
      PositiveHahnRoot k Γ
        (F.comp (Polynomial.X +
          Polynomial.C (algebraMap (valuationSubring k Γ) (HahnField k Γ) start))) :=
    let T' := T.toShiftedSameTerminalObstructionData k Γ hbranch
    T'.positiveHahnRoot_of_edgeStep_rootOrStep_terminalResolution
      k Γ hstep hbelow
  exact PositiveHahnRoot.of_comp_X_add_C k Γ (T.chain.start_mem k Γ) hshift

end KOddClusterFixedStepTerminalFromData

end HahnField

end

end HahnKaplanskyRealClosedness
