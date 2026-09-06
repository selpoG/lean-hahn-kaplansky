/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Foundation.Core

/-!
# Natural block chains and successor extension for omega limits
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- A natural-number chain of block successors.  This is the finite/omega-shaped fragment of
the eventual transfinite block recursion: every block target is definitionally recorded as the
next source. -/
structure OneClusterBlockNatChain
    (F : Polynomial (valuationSubring k Γ)) where
  state : ℕ → OneClusterState k Γ F
  block : ∀ n : ℕ, OneClusterBlockSuccessor k Γ (state n)
  next_eq : ∀ n : ℕ, (block n).next = state (n + 1)

namespace OneClusterBlockNatChain

/-- The valuation-subring correction contributed by the `n`th block. -/
def blockDiff {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockNatChain k Γ F) (n : ℕ) :
    valuationSubring k Γ :=
  (C.state (n + 1)).source - (C.state n).source

/-- The finite partial source correction through the first `n` blocks. -/
def blockPartialValuationSubring {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockNatChain k Γ F) (n : ℕ) :
    valuationSubring k Γ :=
  (Finset.range n).sum (C.blockDiff k Γ)

theorem blockPartial_add_start_eq {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockNatChain k Γ F) (n : ℕ) :
    C.blockPartialValuationSubring k Γ n + (C.state 0).source =
      (C.state n).source := by
  change
    (Finset.range n).sum (fun i => (C.state (i + 1)).source - (C.state i).source) +
      (C.state 0).source = (C.state n).source
  exact SimpleClusterChain.sum_stepDiff_range_add_zero k Γ
    (fun i : ℕ => (C.state i).source) n

theorem state_val_lt_succ {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockNatChain k Γ F) (n : ℕ) :
    (C.state n).val k Γ < (C.state (n + 1)).val k Γ := by
  have h := (C.block n).val_lt
  rwa [C.next_eq n] at h

theorem state_val_strictMono {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockNatChain k Γ F) :
    StrictMono (fun n : ℕ => (C.state n).val k Γ) := by
  exact strictMono_nat_of_lt_succ (fun n => C.state_val_lt_succ k Γ n)

theorem block_next_val_le_state_val_of_lt {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockNatChain k Γ F) {i j : ℕ} (hij : i < j) :
    (C.block i).next.val k Γ ≤ (C.state j).val k Γ := by
  have hnext :
      (C.block i).next.val k Γ = (C.state (i + 1)).val k Γ := by
    rw [C.next_eq i]
  rw [hnext]
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hij) with hlt | heq
  · exact le_of_lt (C.state_val_strictMono k Γ hlt)
  · rw [← heq]

end OneClusterBlockNatChain

def SimpleClusterOmegaChain.blockDiff
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (_hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    valuationSubring k Γ :=
  U (n + 1) - U n

def SimpleClusterOmegaChain.blockPartialValuationSubring
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    valuationSubring k Γ :=
  (Finset.range n).sum (SimpleClusterOmegaChain.blockDiff k Γ hchain)

theorem SimpleClusterOmegaChain.blockPartial_add_start_eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    SimpleClusterOmegaChain.blockPartialValuationSubring k Γ hchain n + U 0 = U n := by
  change
    (Finset.range n).sum (fun i => U (i + 1) - U i) + U 0 = U n
  exact SimpleClusterChain.sum_stepDiff_range_add_zero k Γ U n

theorem SimpleClusterOmegaBlock.limitSource_sub_start_eq_correction
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    SimpleClusterOmegaBlock.limitSource k Γ hblock - A =
      simpleClusterCorrectionValuationSubringOfNoRoot k Γ
          (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
          (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
          (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) -
        simpleClusterApproxOfOneCluster k Γ
          (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
          (SimpleClusterOmegaBlock.translatedUnit k Γ hblock) 0 := by
  change
    simpleClusterCorrectionValuationSubringOfNoRoot k Γ
          (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
          (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
          (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) + A - A =
      simpleClusterCorrectionValuationSubringOfNoRoot k Γ
          (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
          (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
          (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) - 0
  abel

theorem SimpleClusterOmegaBlock.ofLex_limitSource_sub_start_eq_correctionHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    ofLex (((SimpleClusterOmegaBlock.limitSource k Γ hblock - A :
      valuationSubring k Γ) : HahnField k Γ)) =
      simpleClusterCorrectionHahnSeriesOfNoRoot k Γ
        (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
        (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
        (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) := by
  have hsub := congrArg
    (fun x : valuationSubring k Γ => ofLex ((x : valuationSubring k Γ) : HahnField k Γ))
    (SimpleClusterOmegaBlock.limitSource_sub_start_eq_correction k Γ hblock)
  simpa [simpleClusterApproxOfOneCluster,
    simpleClusterCorrectionValuationSubringOfNoRoot,
    simpleClusterCorrectionHahnFieldOfNoRoot] using hsub

theorem SimpleClusterOmegaBlock.addVal_eval_start_eq_first_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    addVal k Γ ((F.eval A : valuationSubring k Γ) : HahnField k Γ) =
      (simpleClusterApproxStepValueOfNoRoot k Γ
        (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
        (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
        (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) 0 :
        WithTop Γ) := by
  let G : Polynomial (valuationSubring k Γ) := F.comp (Polynomial.X + Polynomial.C A)
  let hsmallA := SimpleClusterOmegaBlock.translatedSmall k Γ hblock
  let hunitA := SimpleClusterOmegaBlock.translatedUnit k Γ hblock
  let hnoroot := SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock
  have hG :
      addVal k Γ ((G.eval (0 : valuationSubring k Γ) : valuationSubring k Γ) :
          HahnField k Γ) =
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmallA hunitA hnoroot 0 :
          WithTop Γ) := by
    have hG' := simpleClusterApprox_addVal_eval_eq_evalValue_of_no_root
      k Γ hsmallA hunitA hnoroot 0
    rw [← simpleClusterApprox_stepValue_eq_evalValue_of_no_root
      k Γ hsmallA hunitA hnoroot 0] at hG'
    simpa [G, simpleClusterApproxOfOneCluster] using hG'
  simpa [G, eval_comp_X_add_C] using hG

theorem SimpleClusterOmegaBlock.limitSource_sub_start_support_subset_Ici_stateVal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {S : OneClusterState k Γ F}
    {A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F S.source A') :
    (ofLex (((SimpleClusterOmegaBlock.limitSource k Γ hblock - S.source :
      valuationSubring k Γ) : HahnField k Γ))).support ⊆ Set.Ici (S.val k Γ) := by
  have hSfirst :
      S.val k Γ =
        simpleClusterApproxStepValueOfNoRoot k Γ
          (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
          (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
          (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) 0 := by
    apply WithTop.coe_injective
    rw [← OneClusterState.val_spec k Γ S,
      SimpleClusterOmegaBlock.addVal_eval_start_eq_first_stepValue k Γ hblock]
  intro γ hγ
  rw [hSfirst]
  have hγ' :
      γ ∈ (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ
        (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
        (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
        (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock)).support := by
    change (ofLex (((SimpleClusterOmegaBlock.limitSource k Γ hblock - S.source :
      valuationSubring k Γ) : HahnField k Γ))).coeff γ ≠ 0 at hγ
    rw [SimpleClusterOmegaBlock.ofLex_limitSource_sub_start_eq_correctionHahnSeries
      k Γ hblock] at hγ
    exact hγ
  exact simpleClusterCorrectionHahnSeriesOfNoRoot_support_ge_first_stepValue
    k Γ
    (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
    (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
    (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock)
    hγ'

theorem SimpleClusterOmegaBlock.translatedStepValue_lt_eval_limitSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') (n : ℕ) :
    (simpleClusterApproxStepValueOfNoRoot k Γ
      (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
      (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
      (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) n :
      WithTop Γ) <
      addVal k Γ
        ((F.eval (SimpleClusterOmegaBlock.limitSource k Γ hblock) :
          valuationSubring k Γ) : HahnField k Γ) := by
  let G : Polynomial (valuationSubring k Γ) := F.comp (Polynomial.X + Polynomial.C A)
  let hsmallA := SimpleClusterOmegaBlock.translatedSmall k Γ hblock
  let hunitA := SimpleClusterOmegaBlock.translatedUnit k Γ hblock
  let hnoroot := SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock
  have hG :
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmallA hunitA hnoroot n :
        WithTop Γ) <
        addVal k Γ
          ((G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            (simpleClusterCorrectionValuationSubringOfNoRoot
              k Γ hsmallA hunitA hnoroot : HahnField k Γ)) :=
    simpleClusterCorrection_eval_addVal_gt_stepValue k Γ hsmallA hunitA hnoroot n
  rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) G
    (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmallA hunitA hnoroot)] at hG
  simpa [G, SimpleClusterOmegaBlock.limitSource, hsmallA, hunitA, hnoroot,
    eval_comp_X_add_C] using hG

theorem SimpleClusterOmegaBlock.limitSource_sub_start_support_subset_Iio_limitSourceStateVal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    (ofLex (((SimpleClusterOmegaBlock.limitSource k Γ hblock - A :
      valuationSubring k Γ) : HahnField k Γ))).support ⊆
      Set.Iio ((SimpleClusterOmegaBlock.limitSourceState k Γ hblock).val k Γ) := by
  intro γ hγ
  have hγ' :
      γ ∈ (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ
        (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
        (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
        (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock)).support := by
    change (ofLex (((SimpleClusterOmegaBlock.limitSource k Γ hblock - A :
      valuationSubring k Γ) : HahnField k Γ))).coeff γ ≠ 0 at hγ
    rw [SimpleClusterOmegaBlock.ofLex_limitSource_sub_start_eq_correctionHahnSeries
      k Γ hblock] at hγ
    exact hγ
  rcases simpleClusterCorrectionHahnSeriesOfNoRoot_support_subset_stepValue_range
      k Γ
      (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
      (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
      (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock)
      hγ' with ⟨n, rfl⟩
  have hlt := SimpleClusterOmegaBlock.translatedStepValue_lt_eval_limitSource
    k Γ hblock n
  have hval :
      addVal k Γ
          ((F.eval (SimpleClusterOmegaBlock.limitSource k Γ hblock) :
            valuationSubring k Γ) : HahnField k Γ) =
        ((SimpleClusterOmegaBlock.limitSourceState k Γ hblock).val k Γ : WithTop Γ) :=
    OneClusterState.val_spec k Γ (SimpleClusterOmegaBlock.limitSourceState k Γ hblock)
  rw [hval] at hlt
  exact WithTop.coe_lt_coe.mp hlt

theorem SimpleClusterOmegaBlock.stateVal_lt_limitSourceStateVal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {S : OneClusterState k Γ F}
    {A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F S.source A') :
    S.val k Γ < (SimpleClusterOmegaBlock.limitSourceState k Γ hblock).val k Γ := by
  have hSfirst :
      S.val k Γ =
        simpleClusterApproxStepValueOfNoRoot k Γ
          (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
          (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
          (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) 0 := by
    apply WithTop.coe_injective
    rw [← OneClusterState.val_spec k Γ S,
      SimpleClusterOmegaBlock.addVal_eval_start_eq_first_stepValue k Γ hblock]
  have hlt := SimpleClusterOmegaBlock.translatedStepValue_lt_eval_limitSource
    k Γ hblock 0
  have hnext :
      addVal k Γ
          ((F.eval (SimpleClusterOmegaBlock.limitSource k Γ hblock) :
            valuationSubring k Γ) : HahnField k Γ) =
        ((SimpleClusterOmegaBlock.limitSourceState k Γ hblock).val k Γ : WithTop Γ) :=
    OneClusterState.val_spec k Γ (SimpleClusterOmegaBlock.limitSourceState k Γ hblock)
  rw [hnext] at hlt
  rw [hSfirst]
  exact WithTop.coe_lt_coe.mp hlt

noncomputable def SimpleClusterOmegaBlock.limitSource_blockSuccessor
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {S : OneClusterState k Γ F}
    {A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F S.source A') :
    OneClusterBlockSuccessor k Γ S := by
  let T := SimpleClusterOmegaBlock.limitSourceState k Γ hblock
  have hval : S.val k Γ < T.val k Γ :=
    SimpleClusterOmegaBlock.stateVal_lt_limitSourceStateVal k Γ hblock
  have hlow :=
    SimpleClusterOmegaBlock.limitSource_sub_start_support_subset_Ici_stateVal
      k Γ hblock
  have hhigh :=
    SimpleClusterOmegaBlock.limitSource_sub_start_support_subset_Iio_limitSourceStateVal
      k Γ hblock
  refine ⟨T, hval, ?_⟩
  intro γ hγ
  constructor
  · exact hlow hγ
  · exact hhigh hγ

theorem rootInMaximalIdeal_or_exists_blockSuccessor_at_state
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) (S : OneClusterState k Γ F) :
    RootInMaximalIdeal k Γ F ∨ Nonempty (OneClusterBlockSuccessor k Γ S) := by
  rcases exists_maximalIdeal_root_or_exists_simpleClusterOmegaBlock_at_start
      k Γ hsmall hunit S.source_mem with hroot | hblock
  · exact Or.inl hroot
  · rcases hblock with ⟨A', hblock⟩
    exact Or.inr ⟨SimpleClusterOmegaBlock.limitSource_blockSuccessor k Γ hblock⟩

noncomputable def oneClusterBlockSuccessorOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (S : OneClusterState k Γ F) :
    OneClusterBlockSuccessor k Γ S := by
  classical
  have hsucc : Nonempty (OneClusterBlockSuccessor k Γ S) := by
    rcases rootInMaximalIdeal_or_exists_blockSuccessor_at_state k Γ hsmall hunit S with
      hroot | hsucc
    · exact False.elim (hno hroot)
    · exact hsucc
  exact Classical.choice hsucc

noncomputable def OneClusterBlockChain.succExtendBlock
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (j : Set.Iio (Order.succ (Order.succ o))) :
    OneClusterBlockSuccessor k Γ (C.succExtendState k Γ j) := by
  classical
  by_cases htop : j = (ordinalIioSuccOrderTop (Order.succ o)).top
  · subst j
    let B :=
      oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno (C.succTopState k Γ)
    have hstate :
        C.succTopState k Γ =
          C.succExtendState k Γ (ordinalIioSuccOrderTop (Order.succ o)).top := by
      rw [C.succExtendState_top k Γ]
    exact Eq.ndrec B hstate
  · let hmem :=
      ordinalIioSuccPred (Order.succ o) j htop
    let i : Set.Iio (Order.succ o) := hmem
    have hi : ordinalIioSuccEmb (Order.succ o) i = j :=
      ordinalIioSuccEmb_pred (Order.succ o) j htop
    have hstate : C.state i = C.succExtendState k Γ j := by
      rw [← hi, C.succExtendState_emb k Γ i]
    exact Eq.ndrec (C.block i) hstate

theorem OneClusterBlockChain.succExtendBlock_emb_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (j : Set.Iio (Order.succ (Order.succ o)))
    (hj : j ≠ (ordinalIioSuccOrderTop (Order.succ o)).top) :
    ((C.succExtendBlock k Γ hsmall hunit hno
        j).next.val k Γ) =
      (C.block (ordinalIioSuccPred (Order.succ o) j hj)).next.val k Γ := by
  dsimp [succExtendBlock]
  rw [dif_neg hj]
  exact OneClusterBlockSuccessor.next_val_eq_of_eq k Γ _ _

theorem OneClusterBlockChain.succExtendBlock_emb_next_val'
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    ((C.succExtendBlock k Γ hsmall hunit hno
        (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  rw [C.succExtendBlock_emb_next_val k Γ hsmall hunit hno
    (ordinalIioSuccEmb (Order.succ o) i) (ordinalIioSuccEmb_ne_top (Order.succ o) i)]
  have hpred :
      ordinalIioSuccPred (Order.succ o)
          (ordinalIioSuccEmb (Order.succ o) i)
          (ordinalIioSuccEmb_ne_top (Order.succ o) i) = i := by
    apply (ordinalIioSuccEmb (Order.succ o)).injective
    exact ordinalIioSuccEmb_pred (Order.succ o)
      (ordinalIioSuccEmb (Order.succ o) i)
      (ordinalIioSuccEmb_ne_top (Order.succ o) i)
  rw [hpred]

theorem OneClusterBlockChain.succExtendBlock_not_top_diffHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (j : Set.Iio (Order.succ (Order.succ o)))
    (hj : j ≠ (ordinalIioSuccOrderTop (Order.succ o)).top) :
    (C.succExtendBlock k Γ hsmall hunit hno j).diffHahnSeries k Γ =
      (C.block (ordinalIioSuccPred (Order.succ o) j hj)).diffHahnSeries k Γ := by
  dsimp [succExtendBlock]
  rw [dif_neg hj]
  exact OneClusterBlockSuccessor.diffHahnSeries_eq_of_eq k Γ _ _

theorem OneClusterBlockChain.succExtendBlock_emb_diffHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    (C.succExtendBlock k Γ hsmall hunit hno
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeries k Γ =
      (C.block i).diffHahnSeries k Γ := by
  rw [C.succExtendBlock_not_top_diffHahnSeries k Γ hsmall hunit hno
    (ordinalIioSuccEmb (Order.succ o) i) (ordinalIioSuccEmb_ne_top (Order.succ o) i)]
  rw [ordinalIioSuccPred_emb]

noncomputable def OneClusterBlockChain.succExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    OneClusterBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F where
  state := C.succExtendState k Γ
  block := C.succExtendBlock k Γ hsmall hunit hno
  separated := by
    intro i j hij
    by_cases hjtop : j = (ordinalIioSuccOrderTop (Order.succ o)).top
    · have hitop : i ≠ (ordinalIioSuccOrderTop (Order.succ o)).top := by
        intro hi
        rw [hi, hjtop] at hij
        exact (lt_irrefl (ordinalIioSuccOrderTop (Order.succ o)).top) hij
      rw [hjtop]
      rw [C.succExtendBlock_emb_next_val k Γ hsmall hunit hno i hitop]
      rw [C.succExtendState_top k Γ]
      exact C.block_next_val_le_succTopState_val k Γ
        (ordinalIioSuccPred (Order.succ o) i hitop)
    · have hitop : i ≠ (ordinalIioSuccOrderTop (Order.succ o)).top := by
        intro hi
        rw [hi] at hij
        exact (not_lt_of_ge ((ordinalIioSuccOrderTop (Order.succ o)).le_top j)) hij
      rw [C.succExtendBlock_emb_next_val k Γ hsmall hunit hno i hitop]
      rw [C.succExtendState_not_top k Γ j hjtop]
      exact C.separated
        (ordinalIioSuccEmb_choose_lt_choose_of_lt (o := Order.succ o) hjtop hij)

theorem OneClusterBlockChain.succExtend_restrictTop_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    (((C.succExtend k Γ hsmall hunit hno).restrictLT k Γ
        (ordinalIioSuccOrderTop (Order.succ o)).top).diffHahnSeriesLimit k Γ) =
      C.diffHahnSeriesLimit k Γ := by
  classical
  let R :=
    (C.succExtend k Γ hsmall hunit hno).restrictLT k Γ
      (ordinalIioSuccOrderTop (Order.succ o)).top
  let E := ordinalIioSuccTopIioEquiv (Order.succ o)
  let sR := R.diffSummableFamily k Γ
  let sC := C.diffSummableFamily k Γ
  have hterm :
      ∀ i : Set.Iio (Order.succ o),
        (HahnSeries.SummableFamily.Equiv E sR i) = sC i := by
    intro i
    change
      ((C.succExtendBlock k Γ hsmall hunit hno
          (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeries k Γ) =
        (C.block i).diffHahnSeries k Γ
    exact C.succExtendBlock_emb_diffHahnSeries k Γ hsmall hunit hno i
  ext γ
  calc
    (((C.succExtend k Γ hsmall hunit hno).restrictLT k Γ
        (ordinalIioSuccOrderTop (Order.succ o)).top).diffHahnSeriesLimit k Γ).coeff γ
        = (sR.hsum).coeff γ := rfl
    _ = ((HahnSeries.SummableFamily.Equiv E sR).hsum).coeff γ := by
          rw [HahnSeries.SummableFamily.hsum_equiv]
    _ = ∑ᶠ i : Set.Iio (Order.succ o),
          ((HahnSeries.SummableFamily.Equiv E sR) i).coeff γ := by
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = ∑ᶠ i : Set.Iio (Order.succ o), (sC i).coeff γ := by
          apply finsum_congr
          intro i
          rw [hterm i]
    _ = (sC.hsum).coeff γ := by
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = (C.diffHahnSeriesLimit k Γ).coeff γ := rfl

theorem OneClusterBlockChain.succExtend_restrictEmb_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    (((C.succExtend k Γ hsmall hunit hno).restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) =
      ((C.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
  classical
  let R :=
    (C.succExtend k Γ hsmall hunit hno).restrictLT k Γ
      (ordinalIioSuccEmb (Order.succ o) i)
  let P := C.restrictLT k Γ i
  let E := ordinalIioSuccEmbIioEquiv (Order.succ o) i
  let sR := R.diffSummableFamily k Γ
  let sP := P.diffSummableFamily k Γ
  have hterm :
      ∀ j : Set.Iio i,
        (HahnSeries.SummableFamily.Equiv E sR j) = sP j := by
    intro j
    dsimp [HahnSeries.SummableFamily.Equiv, sR, sP, R, P,
      OneClusterBlockChain.diffSummableFamily]
    exact C.succExtendBlock_emb_diffHahnSeries k Γ hsmall hunit hno j.1
  ext γ
  calc
    (((C.succExtend k Γ hsmall hunit hno).restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ).coeff γ
        = (sR.hsum).coeff γ := rfl
    _ = ((HahnSeries.SummableFamily.Equiv E sR).hsum).coeff γ := by
          rw [HahnSeries.SummableFamily.hsum_equiv]
    _ = ∑ᶠ j : Set.Iio i, ((HahnSeries.SummableFamily.Equiv E sR) j).coeff γ := by
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = ∑ᶠ j : Set.Iio i, (sP j).coeff γ := by
          apply finsum_congr
          intro j
          rw [hterm j]
    _ = (sP.hsum).coeff γ := by
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = ((C.restrictLT k Γ i).diffHahnSeriesLimit k Γ).coeff γ := rfl

noncomputable def OneClusterCoherentBlockChain.succExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F where
  toOneClusterBlockChain :=
    C.toOneClusterBlockChain.succExtend k Γ hsmall hunit hno
  coherent_source := by
    intro j
    by_cases hjtop : j = (ordinalIioSuccOrderTop (Order.succ o)).top
    · subst j
      dsimp [OneClusterBlockChain.succExtend]
      rw [C.toOneClusterBlockChain.succExtendState_top k Γ]
      have hbot :
          (⊥ : Set.Iio (Order.succ (Order.succ o))) =
            ordinalIioSuccEmb (Order.succ o) (⊥ : Set.Iio (Order.succ o)) := rfl
      rw [hbot, C.toOneClusterBlockChain.succExtendState_emb k Γ
        (⊥ : Set.Iio (Order.succ o))]
      have hrestrict :
          OneClusterBlockChain.diffHahnSeriesLimit k Γ
            (OneClusterBlockChain.restrictLT k Γ
              { state := OneClusterBlockChain.succExtendState k Γ C.toOneClusterBlockChain,
                block := OneClusterBlockChain.succExtendBlock k Γ hsmall hunit hno
                  C.toOneClusterBlockChain,
                separated := (C.toOneClusterBlockChain.succExtend k Γ hsmall hunit hno).separated }
              (ordinalIioSuccOrderTop (Order.succ o)).top) =
            C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
        change
          (((C.toOneClusterBlockChain.succExtend k Γ hsmall hunit hno).restrictLT k Γ
              (ordinalIioSuccOrderTop (Order.succ o)).top).diffHahnSeriesLimit k Γ) =
            C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ
        exact C.toOneClusterBlockChain.succExtend_restrictTop_diffHahnSeriesLimit k Γ
          hsmall hunit hno
      rw [hrestrict]
      exact C.ofLex_succTopState_sub_bot_eq_diffHahnSeriesLimit k Γ
    · let i : Set.Iio (Order.succ o) := ordinalIioSuccPred (Order.succ o) j hjtop
      have hji : ordinalIioSuccEmb (Order.succ o) i = j :=
        ordinalIioSuccEmb_pred (Order.succ o) j hjtop
      rw [← hji]
      dsimp [OneClusterBlockChain.succExtend]
      rw [C.toOneClusterBlockChain.succExtendState_emb k Γ i]
      have hbot :
          (⊥ : Set.Iio (Order.succ (Order.succ o))) =
            ordinalIioSuccEmb (Order.succ o) (⊥ : Set.Iio (Order.succ o)) := rfl
      rw [hbot, C.toOneClusterBlockChain.succExtendState_emb k Γ
        (⊥ : Set.Iio (Order.succ o))]
      have hrestrict :
          OneClusterBlockChain.diffHahnSeriesLimit k Γ
            (OneClusterBlockChain.restrictLT k Γ
              { state := OneClusterBlockChain.succExtendState k Γ C.toOneClusterBlockChain,
                block := OneClusterBlockChain.succExtendBlock k Γ hsmall hunit hno
                  C.toOneClusterBlockChain,
                separated := (C.toOneClusterBlockChain.succExtend k Γ hsmall hunit hno).separated }
              (ordinalIioSuccEmb (Order.succ o) i)) =
            ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
        change
          (((C.toOneClusterBlockChain.succExtend k Γ hsmall hunit hno).restrictLT k Γ
              (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) =
            ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ)
        exact C.toOneClusterBlockChain.succExtend_restrictEmb_diffHahnSeriesLimit k Γ
          hsmall hunit hno i
      rw [hrestrict]
      exact C.coherent_source i

theorem OneClusterCoherentBlockChain.succExtend_restrictTop_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    (((C.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccOrderTop (Order.succ o)).top).diffHahnSeriesLimit k Γ) =
      C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ :=
  C.toOneClusterBlockChain.succExtend_restrictTop_diffHahnSeriesLimit k Γ hsmall hunit hno

theorem OneClusterCoherentBlockChain.succExtend_restrictEmb_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    (((C.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) =
      ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) :=
  C.toOneClusterBlockChain.succExtend_restrictEmb_diffHahnSeriesLimit k Γ hsmall hunit hno i

@[simp]
theorem OneClusterCoherentBlockChain.succExtend_state_emb
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    (C.succExtend k Γ hsmall hunit hno).state
        (ordinalIioSuccEmb (Order.succ o) i) =
      C.state i := by
  change
    C.toOneClusterBlockChain.succExtendState k Γ
        (ordinalIioSuccEmb (Order.succ o) i) =
      C.state i
  rw [OneClusterBlockChain.succExtendState_emb]

@[simp]
theorem OneClusterCoherentBlockChain.succExtend_state_bot_source
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    ((C.succExtend k Γ hsmall hunit hno).state
        (⊥ : Set.Iio (Order.succ (Order.succ o)))).source =
      (C.state (⊥ : Set.Iio (Order.succ o))).source := by
  have hbot :
      (⊥ : Set.Iio (Order.succ (Order.succ o))) =
        ordinalIioSuccEmb (Order.succ o) (⊥ : Set.Iio (Order.succ o)) := rfl
  rw [hbot, C.succExtend_state_emb k Γ hsmall hunit hno (⊥ : Set.Iio (Order.succ o))]

theorem OneClusterCoherentBlockChain.BotSourceEq.succExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    {s₀ : valuationSubring k Γ}
    (hC : OneClusterCoherentBlockChain.BotSourceEq k Γ C s₀) :
    OneClusterCoherentBlockChain.BotSourceEq k Γ
      (C.succExtend k Γ hsmall hunit hno) s₀ := by
  unfold OneClusterCoherentBlockChain.BotSourceEq at hC ⊢
  rw [C.succExtend_state_bot_source k Γ hsmall hunit hno, hC]

theorem OneClusterCoherentBlockChain.BotBlockNextValEq.succExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    {v₀ : Γ}
    (hC : OneClusterCoherentBlockChain.BotBlockNextValEq k Γ C v₀) :
    OneClusterCoherentBlockChain.BotBlockNextValEq k Γ
      (C.succExtend k Γ hsmall hunit hno) v₀ := by
  unfold OneClusterCoherentBlockChain.BotBlockNextValEq at hC ⊢
  have hbot :
      (⊥ : Set.Iio (Order.succ (Order.succ o))) =
        ordinalIioSuccEmb (Order.succ o) (⊥ : Set.Iio (Order.succ o)) := rfl
  rw [hbot]
  change
    ((C.toOneClusterBlockChain.succExtendBlock k Γ hsmall hunit hno
        (ordinalIioSuccEmb (Order.succ o) (⊥ : Set.Iio (Order.succ o)))).next.val k Γ) =
      v₀
  rw [C.toOneClusterBlockChain.succExtendBlock_emb_next_val'
    k Γ hsmall hunit hno (⊥ : Set.Iio (Order.succ o)), hC]

end HahnField

end

end HahnKaplanskyRealClosedness
