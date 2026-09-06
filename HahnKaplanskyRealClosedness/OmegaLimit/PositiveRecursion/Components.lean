/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.PositiveRecursion.Core

/-!
# Basic positive recursion component endpoints
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Local split-top components from current block-prefix fields.

This is the current-stage part of the final limit extension, with no global external recursion
`R`: once the positive projection, bottom source/next fields, and current block-prefix fields are
available on the below-chain `C`, they assemble the split-top components directly. -/
noncomputable def PositiveIioCoherentChainAtBelow.splitTopComponents_of_blockPrefix
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {s₀ : valuationSubring k Γ} {v₀ : Γ}
    (hpositive : C.succStageTopNextValProjectionCompatiblePositive k Γ ho)
    (hbotSource : C.BotSourceEq k Γ s₀)
    (hlimitBotSource :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀)
    (hbotNext : C.succStageBotBlockNextValEq k Γ ho v₀)
    (hlimitBotNext :
      ∀ i : Set.Iio o, (i : Ordinal) = 0 →
        (C.limitBlock k Γ ho i).next.val k Γ = v₀)
    (hlimitBlock :
      let htop : C.succStageTopNextValProjectionCompatible k Γ ho :=
        C.succStageTopNextValProjectionCompatible_of_bot_positive k Γ ho
          (fun hij hi =>
            C.succStageTopNextValProjectionCompatible_bot k Γ ho
              hbotNext hlimitBotNext hij hi)
          hpositive
      let hnext : C.succStageNextValCompatible k Γ ho :=
        fun {_ _} hij =>
          C.succStageNextValCompatible_of_prefixTop k Γ ho
            (C.prefixTopNextValCompatible_of_projection k Γ ho htop) hij
      let hlimnext : C.limitNextValCompatible k Γ ho :=
        fun {_ _} hij =>
          C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext hij
      let hsep : C.limitSeparated k Γ ho :=
        fun {_ _} hij => C.limitSeparated_of_nextValCompatible k Γ ho hlimnext hij
      C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep)
    (hstageBlock : C.succStageRestrictedBlockPrefixCompatible k Γ ho) :
    C.SplitTopComponents k Γ ho := by
  let htop : C.succStageTopNextValProjectionCompatible k Γ ho :=
    C.succStageTopNextValProjectionCompatible_of_bot_positive k Γ ho
      (fun hij hi =>
        C.succStageTopNextValProjectionCompatible_bot k Γ ho
          hbotNext hlimitBotNext hij hi)
      hpositive
  let hnext : C.succStageNextValCompatible k Γ ho :=
    fun {_ _} hij =>
      C.succStageNextValCompatible_of_prefixTop k Γ ho
        (C.prefixTopNextValCompatible_of_projection k Γ ho htop) hij
  let hlimnext : C.limitNextValCompatible k Γ ho :=
    fun {_ _} hij =>
      C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext hij
  let hsep : C.limitSeparated k Γ ho :=
    fun {_ _} hij => C.limitSeparated_of_nextValCompatible k Γ ho hlimnext hij
  refine
    { source := s₀
      botValue := v₀
      botSource := ?_
      limitBotSource := ?_
      botNext := ?_
      limitBotNext := ?_
      positiveProjection := hpositive
      limitPrefix := ?_
      stagePrefix := ?_ }
  · exact hbotSource
  · exact hlimitBotSource
  · exact hbotNext
  · exact hlimitBotNext
  · dsimp [htop, hnext, hlimnext, hsep] at hlimitBlock ⊢
    exact hlimitBlock
  · exact hstageBlock

/-- Local natural components from current block-prefix fields.

This is the limit-extension assembly step after the local positive projection has been supplied:
it does not mention a global external recursion `R`. -/
theorem PositiveIioCoherentChainAtBelow.naturalComponents_of_blockPrefix
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {s₀ : valuationSubring k Γ} {v₀ : Γ}
    (hpositive : C.succStageTopNextValProjectionCompatiblePositive k Γ ho)
    (hbotSource : C.BotSourceEq k Γ s₀)
    (hlimitBotSource :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀)
    (hbotNext : C.succStageBotBlockNextValEq k Γ ho v₀)
    (hlimitBotNext :
      ∀ i : Set.Iio o, (i : Ordinal) = 0 →
        (C.limitBlock k Γ ho i).next.val k Γ = v₀)
    (hlimitBlock :
      let htop : C.succStageTopNextValProjectionCompatible k Γ ho :=
        C.succStageTopNextValProjectionCompatible_of_bot_positive k Γ ho
          (fun hij hi =>
            C.succStageTopNextValProjectionCompatible_bot k Γ ho
              hbotNext hlimitBotNext hij hi)
          hpositive
      let hnext : C.succStageNextValCompatible k Γ ho :=
        fun {_ _} hij =>
          C.succStageNextValCompatible_of_prefixTop k Γ ho
            (C.prefixTopNextValCompatible_of_projection k Γ ho htop) hij
      let hlimnext : C.limitNextValCompatible k Γ ho :=
        fun {_ _} hij =>
          C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext hij
      let hsep : C.limitSeparated k Γ ho :=
        fun {_ _} hij => C.limitSeparated_of_nextValCompatible k Γ ho hlimnext hij
      C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep)
    (hstageBlock : C.succStageRestrictedBlockPrefixCompatible k Γ ho) :
    C.NaturalComponents k Γ ho :=
  C.naturalComponents_of_splitTopComponents k Γ ho
    (C.splitTopComponents_of_blockPrefix k Γ ho
      hpositive hbotSource hlimitBotSource hbotNext hlimitBotNext hlimitBlock hstageBlock)

/-- Bottom next-value preservation for an externally presented positive no-root recursion.

This is the generated-recursion analogue of `recOfNoRoot_botBlockNextValEq`: the successor case is
fixed by `succOfNoRoot`, while each limit step only has to preserve the canonical bottom next-value
from the externally presented below-chain. -/
theorem PositiveIioCoherentChainAt.externalRecursion_botBlockNextValEq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    (hlimitBotNext :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        (∀ i : Set.Iio o, (i : Ordinal) = 0 →
          (C.limitBlock k Γ ho i).next.val k Γ =
            (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
              (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) →
        (R o).BotBlockNextValEq k Γ
          ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ))
    (o : Ordinal) :
    (R o).BotBlockNextValEq k Γ
      ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) := by
  induction o using Ordinal.limitRecOn with
  | zero =>
      intro hpos
      exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
  | add_one o ih =>
      change (R (Order.succ o)).BotBlockNextValEq k Γ
        ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
          (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ)
      rw [hsucc o]
      by_cases hpos : (0 : Ordinal) < o
      · exact PositiveIioCoherentChainAt.succOfNoRoot_botBlockNextValEq_of_pos
          k Γ hsmall hunit hno (R o) hpos ih
      · have hzero : o = 0 := le_antisymm (le_of_not_gt hpos) bot_le
        subst o
        intro hsucc0
        rw [PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
          k Γ hsmall hunit hno (R 0) hsucc0]
        exact OneClusterCoherentBlockChain.initialOfNoRoot_botBlockNextValEq
          k Γ hsmall hunit hno
  | limit o ho _IH =>
      exact hlimitBotNext ho
        (by
          intro i hi
          exact PositiveIioCoherentChainAt.externalRecursion_limitBlock_next_val_of_val_eq_zero
            k Γ hsmall hunit hno R hsucc ho i hi)

/-- Bottom next-value preservation for an external recursion whose limit stages are built from
generated natural components. -/
theorem PositiveIioCoherentChainAt.externalRecursion_botBlockNextValEq_of_naturalLimitStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    (hnat :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        C.NaturalComponents k Γ ho)
    (hlimit :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        R o = C.limitStepOfNaturalComponents k Γ ho (hnat ho))
    (o : Ordinal) :
    (R o).BotBlockNextValEq k Γ
      ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) := by
  induction o using Ordinal.limitRecOn with
  | zero =>
      intro hpos
      exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
  | add_one o ih =>
      change (R (Order.succ o)).BotBlockNextValEq k Γ
        ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
          (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ)
      rw [hsucc o]
      by_cases hpos : (0 : Ordinal) < o
      · exact PositiveIioCoherentChainAt.succOfNoRoot_botBlockNextValEq_of_pos
          k Γ hsmall hunit hno (R o) hpos ih
      · have hzero : o = 0 := le_antisymm (le_of_not_gt hpos) bot_le
        subst o
        intro hsucc0
        rw [PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
          k Γ hsmall hunit hno (R 0) hsucc0]
        exact OneClusterCoherentBlockChain.initialOfNoRoot_botBlockNextValEq
          k Γ hsmall hunit hno
  | limit o ho _IH =>
      let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
      change (R o).BotBlockNextValEq k Γ
        ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
          (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ)
      rw [hlimit ho]
      exact C.limitStepOfNaturalComponents_botBlockNextValEq k Γ ho (hnat ho)
        (by
          intro i hi
          exact PositiveIioCoherentChainAt.externalRecursion_limitBlock_next_val_of_val_eq_zero
            k Γ hsmall hunit hno R hsucc ho i hi)

/-- External-recursion successor-stage bottom next-value compatibility. -/
theorem PositiveIioCoherentChainAt.externalRecursion_succStageBotBlockNextValEq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    (hlimitBotNext :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        (∀ i : Set.Iio o, (i : Ordinal) = 0 →
          (C.limitBlock k Γ ho i).next.val k Γ =
            (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
              (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) →
        (R o).BotBlockNextValEq k Γ
          ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ))
    {o : Ordinal} (ho : Order.IsSuccLimit o) :
    PositiveIioCoherentChainAtBelow.succStageBotBlockNextValEq k Γ ho
      (fun i : Set.Iio o => R i.1 : PositiveIioCoherentChainAtBelow k Γ o F)
        ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
          (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) := by
  intro i
  change ((R (Order.succ i.1)
    (lt_of_le_of_lt bot_le (Order.lt_succ i.1))).block
      (⊥ : Set.Iio (Order.succ i.1))).next.val k Γ =
    (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
      (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ
  exact PositiveIioCoherentChainAt.externalRecursion_botBlockNextValEq
    k Γ hsmall hunit hno R hsucc hlimitBotNext (Order.succ i.1)
    (lt_of_le_of_lt bot_le (Order.lt_succ i.1))

end HahnField

end

end HahnKaplanskyRealClosedness
