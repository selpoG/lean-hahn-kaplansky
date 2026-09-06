/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Foundation.NatChain

/-!
# Limit extension bookkeeping for positive ordinal-indexed chains
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

theorem OneClusterCoherentBlockChain.succExtend_block_emb_diffHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    ((C.succExtend k Γ hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeries k Γ =
      (C.block i).diffHahnSeries k Γ := by
  change
    (C.toOneClusterBlockChain.succExtendBlock k Γ hsmall hunit hno
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeries k Γ =
      (C.block i).diffHahnSeries k Γ
  exact C.toOneClusterBlockChain.succExtendBlock_emb_diffHahnSeries k Γ hsmall hunit hno i

theorem OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq.succExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    {d₀ : HahnSeries Γ k}
    (hC : OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq k Γ C d₀) :
    OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq k Γ
      (C.succExtend k Γ hsmall hunit hno) d₀ := by
  unfold OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq at hC ⊢
  have hbot :
      (⊥ : Set.Iio (Order.succ (Order.succ o))) =
        ordinalIioSuccEmb (Order.succ o) (⊥ : Set.Iio (Order.succ o)) := rfl
  rw [hbot, C.succExtend_block_emb_diffHahnSeries k Γ hsmall hunit hno, hC]

noncomputable def OneClusterCoherentBlockChain.limitExtendState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (_ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (j : Set.Iio (Order.succ o)) :
    OneClusterState k Γ F :=
  if htop : j = (ordinalIioSuccOrderTop o).top then
    oneClusterLimitStateOfNoRoot k Γ hsmall hno C
  else
    C.state (ordinalIioSuccPred o j htop)

@[simp]
theorem OneClusterCoherentBlockChain.limitExtendState_top
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F) :
    C.limitExtendState k Γ ho hsmall hno (ordinalIioSuccOrderTop o).top =
      oneClusterLimitStateOfNoRoot k Γ hsmall hno C := by
  simp [limitExtendState]

@[simp]
theorem OneClusterCoherentBlockChain.limitExtendState_emb
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (i : Set.Iio o) :
    C.limitExtendState k Γ ho hsmall hno (ordinalIioSuccEmb o i) =
      C.state i := by
  dsimp [limitExtendState]
  have hne :
      ordinalIioSuccEmb o i ≠ (ordinalIioSuccOrderTop o).top :=
    ordinalIioSuccEmb_ne_top o i
  rw [dif_neg hne]
  rw [ordinalIioSuccPred_emb]

noncomputable def OneClusterCoherentBlockChain.limitExtendBlock
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (j : Set.Iio (Order.succ o)) :
    OneClusterBlockSuccessor k Γ (C.limitExtendState k Γ ho hsmall hno j) := by
  classical
  by_cases htop : j = (ordinalIioSuccOrderTop o).top
  · subst j
    let B :=
      oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterLimitStateOfNoRoot k Γ hsmall hno C)
    have hstate :
        oneClusterLimitStateOfNoRoot k Γ hsmall hno C =
          C.limitExtendState k Γ ho hsmall hno (ordinalIioSuccOrderTop o).top := by
      rw [C.limitExtendState_top k Γ ho hsmall hno]
    exact Eq.ndrec B hstate
  · let i : Set.Iio o := ordinalIioSuccPred o j htop
    have hi : ordinalIioSuccEmb o i = j :=
      ordinalIioSuccEmb_pred o j htop
    have hstate : C.state i = C.limitExtendState k Γ ho hsmall hno j := by
      rw [← hi, C.limitExtendState_emb k Γ ho hsmall hno i]
    exact Eq.ndrec (C.block i) hstate

theorem OneClusterCoherentBlockChain.limitExtendBlock_emb_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (j : Set.Iio (Order.succ o))
    (hj : j ≠ (ordinalIioSuccOrderTop o).top) :
    ((C.limitExtendBlock k Γ ho hsmall hunit hno j).next.val k Γ) =
      (C.block (ordinalIioSuccPred o j hj)).next.val k Γ := by
  dsimp [limitExtendBlock]
  rw [dif_neg hj]
  exact OneClusterBlockChain.OneClusterBlockSuccessor.next_val_eq_of_eq k Γ _ _

theorem OneClusterCoherentBlockChain.limitExtendBlock_emb_next_val'
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (i : Set.Iio o) :
    ((C.limitExtendBlock k Γ ho hsmall hunit hno
        (ordinalIioSuccEmb o i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  rw [C.limitExtendBlock_emb_next_val k Γ ho hsmall hunit hno
    (ordinalIioSuccEmb o i) (ordinalIioSuccEmb_ne_top o i)]
  have hpred :
      ordinalIioSuccPred o
          (ordinalIioSuccEmb o i)
          (ordinalIioSuccEmb_ne_top o i) = i := by
    apply (ordinalIioSuccEmb o).injective
    exact ordinalIioSuccEmb_pred o
      (ordinalIioSuccEmb o i) (ordinalIioSuccEmb_ne_top o i)
  rw [hpred]

theorem OneClusterCoherentBlockChain.limitExtendBlock_emb_diffHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (i : Set.Iio o) :
    (C.limitExtendBlock k Γ ho hsmall hunit hno
        (ordinalIioSuccEmb o i)).diffHahnSeries k Γ =
      (C.block i).diffHahnSeries k Γ := by
  classical
  dsimp [limitExtendBlock]
  rw [dif_neg (ordinalIioSuccEmb_ne_top o i)]
  rw [OneClusterBlockChain.OneClusterBlockSuccessor.diffHahnSeries_eq_of_eq]
  have hpred :
      ordinalIioSuccPred o (ordinalIioSuccEmb o i) (ordinalIioSuccEmb_ne_top o i) = i := by
    apply Subtype.ext
    have hs :=
      ordinalIioSuccEmb_pred o (ordinalIioSuccEmb o i) (ordinalIioSuccEmb_ne_top o i)
    simpa using congrArg Subtype.val hs
  rw [hpred]

noncomputable def OneClusterCoherentBlockChain.limitExtendBlockChain
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F) :
    OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F where
  state := C.limitExtendState k Γ ho hsmall hno
  block := C.limitExtendBlock k Γ ho hsmall hunit hno
  separated := by
    intro i j hij
    by_cases hjtop : j = (ordinalIioSuccOrderTop o).top
    · have hitop : i ≠ (ordinalIioSuccOrderTop o).top := by
        intro hi
        rw [hi, hjtop] at hij
        exact (lt_irrefl (ordinalIioSuccOrderTop o).top) hij
      let i₀ : Set.Iio o := ordinalIioSuccPred o i hitop
      rw [hjtop]
      rw [C.limitExtendBlock_emb_next_val k Γ ho hsmall hunit hno i hitop]
      rw [C.limitExtendState_top k Γ ho hsmall hno]
      rcases ordinalIio_forward_of_isSuccLimit ho i₀ with ⟨j₀, hij₀⟩
      exact (C.separated hij₀).trans
        (le_of_lt (state_val_lt_oneClusterLimitStateOfNoRoot_val k Γ hsmall hno C
          (ordinalIio_forward_of_isSuccLimit ho) j₀))
    · have hitop : i ≠ (ordinalIioSuccOrderTop o).top := by
        intro hi
        rw [hi] at hij
        exact (not_lt_of_ge ((ordinalIioSuccOrderTop o).le_top j)) hij
      rw [C.limitExtendBlock_emb_next_val k Γ ho hsmall hunit hno i hitop]
      have hj_eq : ordinalIioSuccEmb o (ordinalIioSuccPred o j hjtop) = j :=
        ordinalIioSuccEmb_pred o j hjtop
      rw [← hj_eq]
      rw [C.limitExtendState_emb k Γ ho hsmall hno
        (ordinalIioSuccPred o j hjtop)]
      exact C.separated (ordinalIioSuccEmb_choose_lt_choose_of_lt (o := o) hjtop hij)

theorem OneClusterCoherentBlockChain.limitExtend_restrictTop_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F) :
    (((C.limitExtendBlockChain k Γ ho hsmall hunit hno).restrictLT k Γ
        (ordinalIioSuccOrderTop o).top).diffHahnSeriesLimit k Γ) =
      C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
  classical
  let R :=
    (C.limitExtendBlockChain k Γ ho hsmall hunit hno).restrictLT k Γ
      (ordinalIioSuccOrderTop o).top
  let E := ordinalIioSuccTopIioEquiv o
  let sR := R.diffSummableFamily k Γ
  let sC := C.toOneClusterBlockChain.diffSummableFamily k Γ
  have hterm :
      ∀ i : Set.Iio o,
        (HahnSeries.SummableFamily.Equiv E sR i) = sC i := by
    intro i
    change
      ((C.limitExtendBlock k Γ ho hsmall hunit hno
          (ordinalIioSuccEmb o i)).diffHahnSeries k Γ) =
        (C.block i).diffHahnSeries k Γ
    exact C.limitExtendBlock_emb_diffHahnSeries k Γ ho hsmall hunit hno i
  ext γ
  calc
    (((C.limitExtendBlockChain k Γ ho hsmall hunit hno).restrictLT k Γ
        (ordinalIioSuccOrderTop o).top).diffHahnSeriesLimit k Γ).coeff γ
        = (sR.hsum).coeff γ := rfl
    _ = ((HahnSeries.SummableFamily.Equiv E sR).hsum).coeff γ := by
          rw [HahnSeries.SummableFamily.hsum_equiv]
    _ = ∑ᶠ i : Set.Iio o,
          ((HahnSeries.SummableFamily.Equiv E sR) i).coeff γ := by
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = ∑ᶠ i : Set.Iio o, (sC i).coeff γ := by
          apply finsum_congr
          intro i
          rw [hterm i]
    _ = (sC.hsum).coeff γ := by
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = (C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ).coeff γ := rfl

theorem OneClusterCoherentBlockChain.limitExtend_restrictEmb_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (i : Set.Iio o) :
    (((C.limitExtendBlockChain k Γ ho hsmall hunit hno).restrictLT k Γ
        (ordinalIioSuccEmb o i)).diffHahnSeriesLimit k Γ) =
      ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
  classical
  let R :=
    (C.limitExtendBlockChain k Γ ho hsmall hunit hno).restrictLT k Γ
      (ordinalIioSuccEmb o i)
  let P := C.toOneClusterBlockChain.restrictLT k Γ i
  let E := ordinalIioSuccEmbIioEquiv o i
  let sR := R.diffSummableFamily k Γ
  let sP := P.diffSummableFamily k Γ
  have hterm :
      ∀ j : Set.Iio i,
        (HahnSeries.SummableFamily.Equiv E sR j) = sP j := by
    intro j
    dsimp [HahnSeries.SummableFamily.Equiv, sR, sP, R, P,
      OneClusterBlockChain.diffSummableFamily]
    exact C.limitExtendBlock_emb_diffHahnSeries k Γ ho hsmall hunit hno j.1
  ext γ
  calc
    (((C.limitExtendBlockChain k Γ ho hsmall hunit hno).restrictLT k Γ
        (ordinalIioSuccEmb o i)).diffHahnSeriesLimit k Γ).coeff γ
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
    _ = ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ).coeff γ := rfl

noncomputable def OneClusterCoherentBlockChain.limitExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F) :
    OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F where
  toOneClusterBlockChain :=
    C.limitExtendBlockChain k Γ ho hsmall hunit hno
  coherent_source := by
    intro j
    by_cases hjtop : j = (ordinalIioSuccOrderTop o).top
    · subst j
      dsimp [limitExtendBlockChain]
      rw [C.limitExtendState_top k Γ ho hsmall hno]
      have hbot :
          ordinalIioSuccEmb o (⊥ : Set.Iio o) =
            (⊥ : Set.Iio (Order.succ o)) :=
        ordinalIioSuccEmb_bot_eq_bot ho.bot_lt
      rw [← hbot, C.limitExtendState_emb k Γ ho hsmall hno (⊥ : Set.Iio o)]
      have hbotpos : 0 < (C.state ⊥).val k Γ :=
        (C.state ⊥).val_pos_of_cluster_pos k Γ hsmall Nat.zero_lt_one
      have hleft :
          ofLex (((oneClusterLimitStateOfNoRoot k Γ hsmall hno C).source -
            (C.state ⊥).source : valuationSubring k Γ) : HahnField k Γ) =
            C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
        dsimp [oneClusterLimitStateOfNoRoot, OneClusterCoherentBlockChain.limitStateFromBot]
        exact C.toOneClusterBlockChain.ofLex_limitSourceFromBot_sub_bot_eq_diffHahnSeriesLimit
          k Γ (le_of_lt hbotpos)
      have hrestrict :
          OneClusterBlockChain.diffHahnSeriesLimit k Γ
            (OneClusterBlockChain.restrictLT k Γ
              (C.limitExtendBlockChain k Γ ho hsmall hunit hno)
              (ordinalIioSuccOrderTop o).top) =
            C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
        exact C.limitExtend_restrictTop_diffHahnSeriesLimit k Γ ho hsmall hunit hno
      change
        ofLex (((oneClusterLimitStateOfNoRoot k Γ hsmall hno C).source -
          (C.state ⊥).source : valuationSubring k Γ) : HahnField k Γ) =
          (((C.limitExtendBlockChain k Γ ho hsmall hunit hno).restrictLT k Γ
            (ordinalIioSuccOrderTop o).top).diffHahnSeriesLimit k Γ)
      rw [hrestrict]
      exact hleft
    · let i : Set.Iio o := ordinalIioSuccPred o j hjtop
      have hji : ordinalIioSuccEmb o i = j :=
        ordinalIioSuccEmb_pred o j hjtop
      rw [← hji]
      dsimp [limitExtendBlockChain]
      rw [C.limitExtendState_emb k Γ ho hsmall hno i]
      have hbot :
          ordinalIioSuccEmb o (⊥ : Set.Iio o) =
            (⊥ : Set.Iio (Order.succ o)) :=
        ordinalIioSuccEmb_bot_eq_bot ho.bot_lt
      rw [← hbot, C.limitExtendState_emb k Γ ho hsmall hno (⊥ : Set.Iio o)]
      have hrestrict :
          OneClusterBlockChain.diffHahnSeriesLimit k Γ
            (OneClusterBlockChain.restrictLT k Γ
              (C.limitExtendBlockChain k Γ ho hsmall hunit hno)
              (ordinalIioSuccEmb o i)) =
            ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
        exact C.limitExtend_restrictEmb_diffHahnSeriesLimit k Γ ho hsmall hunit hno i
      change
        ofLex (((C.state i).source - (C.state ⊥).source : valuationSubring k Γ) :
          HahnField k Γ) =
          (((C.limitExtendBlockChain k Γ ho hsmall hunit hno).restrictLT k Γ
            (ordinalIioSuccEmb o i)).diffHahnSeriesLimit k Γ)
      rw [hrestrict]
      exact C.coherent_source i

theorem OneClusterCoherentBlockChain.limitExtend_toBlockChain_restrictTop_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F) :
    (((C.limitExtend k Γ ho hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccOrderTop o).top).diffHahnSeriesLimit k Γ) =
      C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ :=
  C.limitExtend_restrictTop_diffHahnSeriesLimit k Γ ho hsmall hunit hno

theorem OneClusterCoherentBlockChain.limitExtend_toBlockChain_restrictEmb_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (i : Set.Iio o) :
    (((C.limitExtend k Γ ho hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb o i)).diffHahnSeriesLimit k Γ) =
      ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) :=
  C.limitExtend_restrictEmb_diffHahnSeriesLimit k Γ ho hsmall hunit hno i

@[simp]
theorem OneClusterCoherentBlockChain.limitExtend_state_emb
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (i : Set.Iio o) :
    (C.limitExtend k Γ ho hsmall hunit hno).state
        (ordinalIioSuccEmb o i) =
      C.state i := by
  change
    C.limitExtendState k Γ ho hsmall hno (ordinalIioSuccEmb o i) =
      C.state i
  rw [C.limitExtendState_emb k Γ ho hsmall hno i]

@[simp]
theorem OneClusterCoherentBlockChain.limitExtend_state_bot_source
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F) :
    ((C.limitExtend k Γ ho hsmall hunit hno).state
        (⊥ : Set.Iio (Order.succ o))).source =
      (C.state (⊥ : Set.Iio o)).source := by
  have hbot :
      ordinalIioSuccEmb o (⊥ : Set.Iio o) =
        (⊥ : Set.Iio (Order.succ o)) :=
    ordinalIioSuccEmb_bot_eq_bot ho.bot_lt
  rw [← hbot, C.limitExtend_state_emb k Γ ho hsmall hunit hno (⊥ : Set.Iio o)]

theorem OneClusterCoherentBlockChain.BotSourceEq.limitExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    {s₀ : valuationSubring k Γ}
    (hC : OneClusterCoherentBlockChain.BotSourceEq k Γ C s₀) :
    OneClusterCoherentBlockChain.BotSourceEq k Γ
      (C.limitExtend k Γ ho hsmall hunit hno) s₀ := by
  unfold OneClusterCoherentBlockChain.BotSourceEq at hC ⊢
  rw [C.limitExtend_state_bot_source k Γ ho hsmall hunit hno, hC]

theorem OneClusterCoherentBlockChain.limitExtend_block_emb_diffHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (i : Set.Iio o) :
    ((C.limitExtend k Γ ho hsmall hunit hno).block
        (ordinalIioSuccEmb o i)).diffHahnSeries k Γ =
      (C.block i).diffHahnSeries k Γ := by
  change
    (C.limitExtendBlock k Γ ho hsmall hunit hno
        (ordinalIioSuccEmb o i)).diffHahnSeries k Γ =
      (C.block i).diffHahnSeries k Γ
  exact C.limitExtendBlock_emb_diffHahnSeries k Γ ho hsmall hunit hno i

theorem OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq.limitExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    {d₀ : HahnSeries Γ k}
    (hC : OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq k Γ C d₀) :
    OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq k Γ
      (C.limitExtend k Γ ho hsmall hunit hno) d₀ := by
  unfold OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq at hC ⊢
  have hbot :
      ordinalIioSuccEmb o (⊥ : Set.Iio o) =
        (⊥ : Set.Iio (Order.succ o)) :=
    ordinalIioSuccEmb_bot_eq_bot ho.bot_lt
  rw [← hbot, C.limitExtend_block_emb_diffHahnSeries k Γ ho hsmall hunit hno, hC]

abbrev PositiveIioCoherentChain
    (o : Ordinal) (hpos : (0 : Ordinal) < o)
    (F : Polynomial (valuationSubring k Γ)) : Type _ :=
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  OneClusterCoherentBlockChain k Γ (Set.Iio o) F

theorem PositiveIioCoherentChain.not_hartogs
    {F : Polynomial (valuationSubring k Γ)} :
    ¬ Nonempty (PositiveIioCoherentChain k Γ (hartogsOrdinal Γ)
      (hartogsOrdinal_pos Γ) F) := by
  let _ : OrderBot (Set.Iio (hartogsOrdinal Γ)) :=
    ordinalIioOrderBotOfPos (hartogsOrdinal_pos Γ)
  exact OneClusterCoherentBlockChain.not_hartogs_iio k Γ

abbrev PositiveIioCoherentChainAt
    (o : Ordinal) (F : Polynomial (valuationSubring k Γ)) : Type _ :=
  ∀ hpos : (0 : Ordinal) < o, PositiveIioCoherentChain k Γ o hpos F

def PositiveIioCoherentChainAt.BotSourceEq
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAt k Γ o F)
    (s₀ : valuationSubring k Γ) : Prop :=
  ∀ hpos : (0 : Ordinal) < o,
    letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
    OneClusterCoherentBlockChain.BotSourceEq k Γ (C hpos) s₀

def PositiveIioCoherentChainAt.BotBlockNextValEq
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAt k Γ o F) (v₀ : Γ) : Prop :=
  ∀ hpos : (0 : Ordinal) < o,
    letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
    OneClusterCoherentBlockChain.BotBlockNextValEq k Γ (C hpos) v₀

def PositiveIioCoherentChainAt.BotBlockDiffHahnSeriesEq
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAt k Γ o F) (d₀ : HahnSeries Γ k) : Prop :=
  ∀ hpos : (0 : Ordinal) < o,
    letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
    OneClusterCoherentBlockChain.BotBlockDiffHahnSeriesEq k Γ (C hpos) d₀

theorem PositiveIioCoherentChainAt.not_hartogs
    {F : Polynomial (valuationSubring k Γ)} :
    ¬ Nonempty (PositiveIioCoherentChainAt k Γ (hartogsOrdinal Γ) F) := by
  rintro ⟨C⟩
  exact PositiveIioCoherentChain.not_hartogs k Γ ⟨C (hartogsOrdinal_pos Γ)⟩

theorem PositiveIioCoherentChain.cast_state_bot_source
    {o o' : Ordinal} {hpos : (0 : Ordinal) < o} {hpos' : (0 : Ordinal) < o'}
    {F : Polynomial (valuationSubring k Γ)}
    (ho : o = o') (C : PositiveIioCoherentChain k Γ o hpos F) :
    (letI : OrderBot (Set.Iio o') := ordinalIioOrderBotOfPos hpos'
     ((cast (by subst o'; rfl) C :
        PositiveIioCoherentChain k Γ o' hpos' F).state (⊥ : Set.Iio o')).source) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       (C.state (⊥ : Set.Iio o)).source) := by
  subst o'
  simp

theorem PositiveIioCoherentChain.cast_state_bot_source'
    {o o' : Ordinal} {hpos : (0 : Ordinal) < o} {hpos' : (0 : Ordinal) < o'}
    {F : Polynomial (valuationSubring k Γ)}
    (ho : o = o') (C : PositiveIioCoherentChain k Γ o hpos F)
    (e : PositiveIioCoherentChain k Γ o hpos F =
      PositiveIioCoherentChain k Γ o' hpos' F) :
    (letI : OrderBot (Set.Iio o') := ordinalIioOrderBotOfPos hpos'
     ((cast e C : PositiveIioCoherentChain k Γ o' hpos' F).state
        (⊥ : Set.Iio o')).source) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       (C.state (⊥ : Set.Iio o)).source) := by
  subst o'
  simp

@[simp]
theorem PositiveIioCoherentChain.cast_block_next_val_same
    {o : Ordinal} {hpos hpos' : (0 : Ordinal) < o}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (e : PositiveIioCoherentChain k Γ o hpos F =
      PositiveIioCoherentChain k Γ o hpos' F)
    (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos'
     ((cast e C : PositiveIioCoherentChain k Γ o hpos' F).block i).next.val k Γ) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
      (C.block i).next.val k Γ) := by
  simp

@[simp]
theorem PositiveIioCoherentChain.cast_cast_block_next_val_same
    {o : Ordinal} {hpos hpos' hpos'' : (0 : Ordinal) < o}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (e₁ : PositiveIioCoherentChain k Γ o hpos F =
      PositiveIioCoherentChain k Γ o hpos' F)
    (e₂ : PositiveIioCoherentChain k Γ o hpos' F =
      PositiveIioCoherentChain k Γ o hpos'' F)
    (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos''
     ((cast e₂ (cast e₁ C) : PositiveIioCoherentChain k Γ o hpos'' F).block i).next.val k Γ) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       (C.block i).next.val k Γ) := by
  simp

def PositiveIioCoherentChain.succEndpointTopState
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ (Order.succ o)
      (lt_of_le_of_lt bot_le (Order.lt_succ o)) F) :
    OneClusterState k Γ F :=
  letI : OrderBot (Set.Iio (Order.succ o)) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
  C.toOneClusterBlockChain.topState k Γ

def PositiveIioCoherentChain.succEndpointTopBlock
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ (Order.succ o)
      (lt_of_le_of_lt bot_le (Order.lt_succ o)) F) :
    OneClusterBlockSuccessor k Γ (C.succEndpointTopState k Γ) :=
  letI : OrderBot (Set.Iio (Order.succ o)) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
  C.toOneClusterBlockChain.topBlock k Γ

theorem PositiveIioCoherentChain.succEndpointTopBlock_next_val_eq_of_eq
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    {C D : PositiveIioCoherentChain k Γ (Order.succ o)
      (lt_of_le_of_lt bot_le (Order.lt_succ o)) F}
    (h : C = D) :
    (C.succEndpointTopBlock k Γ).next.val k Γ =
      (D.succEndpointTopBlock k Γ).next.val k Γ := by
  cases h
  rfl

theorem PositiveIioCoherentChain.succEndpointTopBlock_diffHahnSeries_eq_of_eq
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    {C D : PositiveIioCoherentChain k Γ (Order.succ o)
      (lt_of_le_of_lt bot_le (Order.lt_succ o)) F}
    (h : C = D) :
    (C.succEndpointTopBlock k Γ).diffHahnSeries k Γ =
      (D.succEndpointTopBlock k Γ).diffHahnSeries k Γ := by
  cases h
  rfl

theorem OneClusterCoherentBlockChain.succExtend_block_emb_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    (((C.succExtend k Γ hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  change
    ((C.toOneClusterBlockChain.succExtendBlock k Γ hsmall hunit hno
        (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ) =
      (C.block i).next.val k Γ
  exact C.toOneClusterBlockChain.succExtendBlock_emb_next_val'
    k Γ hsmall hunit hno i

theorem PositiveIioCoherentChain.succExtend_block_emb_top_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F) :
    (((C.succExtend k Γ hsmall hunit hno).block
      (ordinalIioSuccEmb (Order.succ p) (ordinalIioSuccOrderTop p).top)).next.val k Γ) =
      (C.succEndpointTopBlock k Γ).next.val k Γ := by
  change _ = (C.block (ordinalIioSuccOrderTop p).top).next.val k Γ
  exact OneClusterCoherentBlockChain.succExtend_block_emb_next_val
    (k := k) (Γ := Γ) hsmall hunit hno C (ordinalIioSuccOrderTop p).top

theorem PositiveIioCoherentChain.succExtend_block_emb_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F)
    (i : Set.Iio (Order.succ p)) :
    (((C.succExtend k Γ hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ p) i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  exact OneClusterCoherentBlockChain.succExtend_block_emb_next_val
    (k := k) (Γ := Γ) hsmall hunit hno C i

@[simp]
theorem OneClusterCoherentBlockChain.succExtend_cast_cast_block_emb_next_val_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₁ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    (((cast e₂ (cast e₁ C) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
        |>.succExtend k Γ hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ =
      ((C.succExtend k Γ hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ := by
  simp

theorem OneClusterCoherentBlockChain.succExtend_cast_cast_restrictEmb_diffHahnSeriesLimit_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₁ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    ((((cast e₂ (cast e₁ C) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
        |>.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) =
      (((C.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) := by
  simp

theorem OneClusterCoherentBlockChain.cast_succExtend_cast_restrictEmb_diffHahnSeriesLimit_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (ein : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (eout : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F)
    (i : Set.Iio (Order.succ o)) :
    (((cast eout
        ((cast ein C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
          |>.succExtend k Γ hsmall hunit hno) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F)
        |>.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) =
      ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
  calc
    (((cast eout
        ((cast ein C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
          |>.succExtend k Γ hsmall hunit hno) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F)
        |>.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ)
        =
      ((((cast ein C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
        |>.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) := by
        simp
    _ =
      (((cast ein C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
        |>.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
        exact OneClusterCoherentBlockChain.succExtend_restrictEmb_diffHahnSeriesLimit
          (k := k) (Γ := Γ) hsmall hunit hno
          (cast ein C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F) i
    _ = ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
        simp

theorem OneClusterCoherentBlockChain.cast_cast_succExtend_cast_cast_block_emb_next_val_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₁ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₃ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F)
    (e₄ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F)
    (i : Set.Iio (Order.succ o)) :
    (let D : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F :=
        cast e₄ (cast e₃
          (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
            (cast e₂ (cast e₁ C) :
              OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)));
     (D.block (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  calc
    (let D : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F :=
        cast e₄ (cast e₃
          (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
            (cast e₂ (cast e₁ C) :
              OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)));
     (D.block (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ)
        =
      ((((cast e₂ (cast e₁ C) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
        |>.succExtend k Γ hsmall hunit hno).block
          (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ) := by
        exact OneClusterCoherentBlockChain.cast_cast_block_next_val_same
          k Γ
          (((cast e₂ (cast e₁ C) :
            OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
            |>.succExtend k Γ hsmall hunit hno))
          e₃ e₄ (ordinalIioSuccEmb (Order.succ o) i)
    _ =
      (((cast e₂ (cast e₁ C) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
        |>.block i).next.val k Γ) := by
        exact OneClusterCoherentBlockChain.succExtend_block_emb_next_val
          k Γ hsmall hunit hno
          (cast e₂ (cast e₁ C) :
            OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
          i
    _ = (C.block i).next.val k Γ := by
        exact OneClusterCoherentBlockChain.cast_cast_block_next_val_same
          k Γ C e₁ e₂ i

theorem OneClusterCoherentBlockChain.cast_cast_succExtend_cast_cast_block_emb_diffHahnSeries_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₁ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (e₃ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F)
    (e₄ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F =
      OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F)
    (i : Set.Iio (Order.succ o)) :
    (let D : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F :=
        cast e₄ (cast e₃
          (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
            (cast e₂ (cast e₁ C) :
              OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)));
     (D.block (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeries k Γ) =
      (C.block i).diffHahnSeries k Γ := by
  calc
    (let D : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ o))) F :=
        cast e₄ (cast e₃
          (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
            (cast e₂ (cast e₁ C) :
              OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)));
     (D.block (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeries k Γ)
        =
      ((((cast e₂ (cast e₁ C) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
        |>.succExtend k Γ hsmall hunit hno).block
          (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeries k Γ) := by
        exact OneClusterCoherentBlockChain.cast_cast_block_diffHahnSeries_same
          k Γ
          (((cast e₂ (cast e₁ C) :
            OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
            |>.succExtend k Γ hsmall hunit hno))
          e₃ e₄ (ordinalIioSuccEmb (Order.succ o) i)
    _ =
      (((cast e₂ (cast e₁ C) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
        |>.block i).diffHahnSeries k Γ) := by
        exact OneClusterCoherentBlockChain.succExtend_block_emb_diffHahnSeries
          k Γ hsmall hunit hno
          (cast e₂ (cast e₁ C) :
            OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F)
          i
    _ = (C.block i).diffHahnSeries k Γ := by
        exact OneClusterCoherentBlockChain.cast_cast_block_diffHahnSeries_same
          k Γ C e₁ e₂ i

@[simp]
theorem PositiveIioCoherentChain.succExtend_cast_cast_block_emb_next_val_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos hpos' hpos'' : (0 : Ordinal) < Order.succ o}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ o) hpos F)
    (e₁ : PositiveIioCoherentChain k Γ (Order.succ o) hpos F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos' F)
    (e₂ : PositiveIioCoherentChain k Γ (Order.succ o) hpos' F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos'' F)
    (i : Set.Iio (Order.succ o)) :
    (((cast e₂ (cast e₁ C) :
        PositiveIioCoherentChain k Γ (Order.succ o) hpos'' F)
        |>.succExtend k Γ hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ =
      ((C.succExtend k Γ hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ := by
  simp [PositiveIioCoherentChain]

theorem PositiveIioCoherentChain.cast_cast_succExtend_cast_cast_block_emb_next_val_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos hpos' hpos'' : (0 : Ordinal) < Order.succ o}
    {hout hout' hout'' : (0 : Ordinal) < Order.succ (Order.succ o)}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ o) hpos F)
    (e₁ : PositiveIioCoherentChain k Γ (Order.succ o) hpos F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos' F)
    (e₂ : PositiveIioCoherentChain k Γ (Order.succ o) hpos' F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos'' F)
    (e₃ : PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout F =
      PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout' F)
    (e₄ : PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout' F =
      PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout'' F)
    (i : Set.Iio (Order.succ o)) :
    (let D : PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout'' F :=
        cast e₄ (cast e₃
          (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
            (cast e₂ (cast e₁ C) :
              PositiveIioCoherentChain k Γ (Order.succ o) hpos'' F)));
     (D.block (ordinalIioSuccEmb (Order.succ o) i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  simpa [PositiveIioCoherentChain] using
    (OneClusterCoherentBlockChain.cast_cast_succExtend_cast_cast_block_emb_next_val_same
      (k := k) (Γ := Γ) hsmall hunit hno C e₁ e₂ e₃ e₄ i)

theorem PositiveIioCoherentChain.cast_cast_succExtend_cast_cast_block_emb_diffHahnSeries_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos hpos' hpos'' : (0 : Ordinal) < Order.succ o}
    {hout hout' hout'' : (0 : Ordinal) < Order.succ (Order.succ o)}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ o) hpos F)
    (e₁ : PositiveIioCoherentChain k Γ (Order.succ o) hpos F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos' F)
    (e₂ : PositiveIioCoherentChain k Γ (Order.succ o) hpos' F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos'' F)
    (e₃ : PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout F =
      PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout' F)
    (e₄ : PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout' F =
      PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout'' F)
    (i : Set.Iio (Order.succ o)) :
    (let D : PositiveIioCoherentChain k Γ (Order.succ (Order.succ o)) hout'' F :=
        cast e₄ (cast e₃
          (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
            (cast e₂ (cast e₁ C) :
              PositiveIioCoherentChain k Γ (Order.succ o) hpos'' F)));
     (D.block (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeries k Γ) =
      (C.block i).diffHahnSeries k Γ := by
  simpa [PositiveIioCoherentChain] using
    (OneClusterCoherentBlockChain.cast_cast_succExtend_cast_cast_block_emb_diffHahnSeries_same
      (k := k) (Γ := Γ) hsmall hunit hno C e₁ e₂ e₃ e₄ i)

theorem PositiveIioCoherentChain.succExtend_cast_cast_restrictEmb_diffHahnSeriesLimit_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos hpos' hpos'' : (0 : Ordinal) < Order.succ o}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ o) hpos F)
    (e₁ : PositiveIioCoherentChain k Γ (Order.succ o) hpos F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos' F)
    (e₂ : PositiveIioCoherentChain k Γ (Order.succ o) hpos' F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos'' F)
    (i : Set.Iio (Order.succ o)) :
    (((cast e₂ (cast e₁ C) :
        PositiveIioCoherentChain k Γ (Order.succ o) hpos'' F)
        |>.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ =
    (((C.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) := by
  simp [PositiveIioCoherentChain]

theorem PositiveIioCoherentChain.cast_succExtend_cast_restrictEmb_diffHahnSeriesLimit_same
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos hpos' : (0 : Ordinal) < Order.succ o}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ o) hpos F)
    (ein : PositiveIioCoherentChain k Γ (Order.succ o) hpos F =
      PositiveIioCoherentChain k Γ (Order.succ o) hpos' F)
    (eout : PositiveIioCoherentChain k Γ (Order.succ (Order.succ o))
        (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ o))) F =
      PositiveIioCoherentChain k Γ (Order.succ (Order.succ o))
        (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ o))) F)
    (i : Set.Iio (Order.succ o)) :
    (((cast eout
        ((cast ein C : PositiveIioCoherentChain k Γ (Order.succ o) hpos' F)
          |>.succExtend k Γ hsmall hunit hno) :
        PositiveIioCoherentChain k Γ (Order.succ (Order.succ o))
          (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ o))) F)
        |>.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) =
      (((C.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ) := by
  simp [PositiveIioCoherentChain]

universe u

theorem PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_restrictEmb_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p q r : Ordinal.{u}} {hp : (0 : Ordinal) < Order.succ p}
    {hq : (0 : Ordinal) < Order.succ q} {hr : (0 : Ordinal) < r}
    {F : Polynomial (valuationSubring k Γ)}
    (hqp : q = p) (hrp : r = Order.succ (Order.succ p))
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p) hp F)
    (ein₁ : PositiveIioCoherentChain k Γ (Order.succ p) hp F =
      PositiveIioCoherentChain k Γ (Order.succ q) hq F)
    (ein₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ q)) F =
      PositiveIioCoherentChain k Γ (Order.succ q) hq F)
    (eout₁ : PositiveIioCoherentChain k Γ (Order.succ (Order.succ q))
        (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ q))) F =
      PositiveIioCoherentChain k Γ r hr F)
    (eout₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ p))) F =
      PositiveIioCoherentChain k Γ r hr F)
    (i : Set.Iio (Order.succ p)) :
    (((eout₂.mpr (eout₁.mp
        (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
          (ein₂.mpr (ein₁.mp C)))) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ p))) F)
      |>.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ p) i)).diffHahnSeriesLimit k Γ) =
      ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
  subst q
  subst r
  cases ein₁
  cases ein₂
  cases eout₁
  cases eout₂
  exact OneClusterCoherentBlockChain.succExtend_restrictEmb_diffHahnSeriesLimit
    (k := k) (Γ := Γ) hsmall hunit hno C i

theorem PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_block_emb_top_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p q r : Ordinal.{u}} {hp : (0 : Ordinal) < Order.succ p}
    {hq : (0 : Ordinal) < Order.succ q} {hr : (0 : Ordinal) < r}
    {F : Polynomial (valuationSubring k Γ)}
    (hqp : q = p) (hrp : r = Order.succ (Order.succ p))
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p) hp F)
    (ein₁ : PositiveIioCoherentChain k Γ (Order.succ p) hp F =
      PositiveIioCoherentChain k Γ (Order.succ q) hq F)
    (ein₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ q)) F =
      PositiveIioCoherentChain k Γ (Order.succ q) hq F)
    (eout₁ : PositiveIioCoherentChain k Γ (Order.succ (Order.succ q))
        (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ q))) F =
      PositiveIioCoherentChain k Γ r hr F)
    (eout₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ p))) F =
      PositiveIioCoherentChain k Γ r hr F) :
    (((eout₂.mpr (eout₁.mp
        (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
          (ein₂.mpr (ein₁.mp C)))) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ p))) F)
      |>.block (ordinalIioSuccEmb (Order.succ p) (ordinalIioSuccOrderTop p).top)).next.val k Γ) =
      (C.succEndpointTopBlock k Γ).next.val k Γ := by
  subst q
  subst r
  cases ein₁
  cases ein₂
  cases eout₁
  cases eout₂
  exact PositiveIioCoherentChain.succExtend_block_emb_top_next_val
    (k := k) (Γ := Γ) hsmall hunit hno C

theorem PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_block_emb_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p q r : Ordinal.{u}} {hp : (0 : Ordinal) < Order.succ p}
    {hq : (0 : Ordinal) < Order.succ q} {hr : (0 : Ordinal) < r}
    {F : Polynomial (valuationSubring k Γ)}
    (hqp : q = p) (hrp : r = Order.succ (Order.succ p))
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p) hp F)
    (ein₁ : PositiveIioCoherentChain k Γ (Order.succ p) hp F =
      PositiveIioCoherentChain k Γ (Order.succ q) hq F)
    (ein₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ q)) F =
      PositiveIioCoherentChain k Γ (Order.succ q) hq F)
    (eout₁ : PositiveIioCoherentChain k Γ (Order.succ (Order.succ q))
        (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ q))) F =
      PositiveIioCoherentChain k Γ r hr F)
    (eout₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ p))) F =
      PositiveIioCoherentChain k Γ r hr F)
    (i : Set.Iio (Order.succ p)) :
    (((eout₂.mpr (eout₁.mp
        (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
          (ein₂.mpr (ein₁.mp C)))) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ p))) F)
      |>.block (ordinalIioSuccEmb (Order.succ p) i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  subst q
  subst r
  cases ein₁
  cases ein₂
  cases eout₁
  cases eout₂
  exact PositiveIioCoherentChain.succExtend_block_emb_next_val
    (k := k) (Γ := Γ) hsmall hunit hno C i

theorem PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_block_emb_diffHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p q r : Ordinal.{u}} {hp : (0 : Ordinal) < Order.succ p}
    {hq : (0 : Ordinal) < Order.succ q} {hr : (0 : Ordinal) < r}
    {F : Polynomial (valuationSubring k Γ)}
    (hqp : q = p) (hrp : r = Order.succ (Order.succ p))
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p) hp F)
    (ein₁ : PositiveIioCoherentChain k Γ (Order.succ p) hp F =
      PositiveIioCoherentChain k Γ (Order.succ q) hq F)
    (ein₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ q)) F =
      PositiveIioCoherentChain k Γ (Order.succ q) hq F)
    (eout₁ : PositiveIioCoherentChain k Γ (Order.succ (Order.succ q))
        (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ q))) F =
      PositiveIioCoherentChain k Γ r hr F)
    (eout₂ : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ p))) F =
      PositiveIioCoherentChain k Γ r hr F)
    (i : Set.Iio (Order.succ p)) :
    (((eout₂.mpr (eout₁.mp
        (OneClusterCoherentBlockChain.succExtend k Γ hsmall hunit hno
          (ein₂.mpr (ein₁.mp C)))) :
        OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (Order.succ p))) F)
      |>.block (ordinalIioSuccEmb (Order.succ p) i)).diffHahnSeries k Γ) =
      (C.block i).diffHahnSeries k Γ := by
  subst q
  subst r
  cases ein₁
  cases ein₂
  cases eout₁
  cases eout₂
  exact OneClusterCoherentBlockChain.succExtend_block_emb_diffHahnSeries
    (k := k) (Γ := Γ) hsmall hunit hno C i

theorem OneClusterCoherentBlockChain.limitExtend_block_emb_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    (i : Set.Iio o) :
    (((C.limitExtend k Γ ho hsmall hunit hno).block
        (ordinalIioSuccEmb o i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  change
    ((C.limitExtendBlock k Γ ho hsmall hunit hno
        (ordinalIioSuccEmb o i)).next.val k Γ) =
      (C.block i).next.val k Γ
  exact C.limitExtendBlock_emb_next_val' k Γ ho hsmall hunit hno i

theorem OneClusterCoherentBlockChain.BotBlockNextValEq.limitExtend
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} [OrderBot (Set.Iio o)]
    (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio o) F)
    {v₀ : Γ}
    (hC : OneClusterCoherentBlockChain.BotBlockNextValEq k Γ C v₀) :
    OneClusterCoherentBlockChain.BotBlockNextValEq k Γ
      (C.limitExtend k Γ ho hsmall hunit hno) v₀ := by
  unfold OneClusterCoherentBlockChain.BotBlockNextValEq at hC ⊢
  have hbot :
      ordinalIioSuccEmb o (⊥ : Set.Iio o) =
        (⊥ : Set.Iio (Order.succ o)) :=
    ordinalIioSuccEmb_bot_eq_bot ho.bot_lt
  rw [← hbot, C.limitExtend_block_emb_next_val k Γ ho hsmall hunit hno, hC]

end HahnField

end

end HahnKaplanskyRealClosedness
