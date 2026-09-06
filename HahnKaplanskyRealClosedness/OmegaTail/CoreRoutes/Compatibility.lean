/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaTail.CoreRoutes.Tower

/-!
# Limit compatibility and generated external inputs
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

universe u v

namespace HahnField

variable (k : Type u) (Γ : Type v)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

open PositiveIioCoherentChainAt

@[simp]
theorem PositiveIioCoherentChainAt.recOfNoRoot_limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (limitStep :
      ∀ {o : Ordinal}, Order.IsSuccLimit o →
        PositiveIioCoherentChainAtBelow k Γ o F →
        PositiveIioCoherentChainAt k Γ o F)
    {o : Ordinal} (ho : Order.IsSuccLimit o) :
    PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep o =
      limitStep ho
        (fun i =>
          PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep i.1) := by
  unfold PositiveIioCoherentChainAt.recOfNoRoot
  rw [Ordinal.limitRecOn_limit _ _ _ _ ho]

/-- Uniqueness for externally presented positive no-root recursions. -/
theorem PositiveIioCoherentChainAt.recOfNoRoot_eq_of_recursion_eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (limitStep :
      ∀ {o : Ordinal}, Order.IsSuccLimit o →
        PositiveIioCoherentChainAtBelow k Γ o F →
        PositiveIioCoherentChainAt k Γ o F)
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    (hlimit :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        R o = limitStep ho (fun i => R i.1)) :
    ∀ o : Ordinal,
      PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep o = R o := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero =>
      funext hpos
      exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
  | add_one o ih =>
      change
        PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep
            (Order.succ o) =
          R (Order.succ o)
      rw [PositiveIioCoherentChainAt.recOfNoRoot_succ k Γ hsmall hunit hno limitStep o,
        ih]
      exact (hsucc o).symm
  | limit o ho IH =>
      calc
        PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep o =
            limitStep ho
              (fun i =>
                PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep i.1) := by
          exact PositiveIioCoherentChainAt.recOfNoRoot_limit
            k Γ hsmall hunit hno limitStep ho
        _ = limitStep ho (fun i => R i.1) := by
          congr 1
          funext i
          exact IH i.1 i.2
        _ = R o := (hlimit ho).symm

/-- External simultaneous recursion data provide fixed generated natural-bottom data.

The final construction can build a chain `R` and its generated component data together.  If the
same total `limitStep` agrees with `R` on successor and limit stages, the uniqueness lemma for
`recOfNoRoot` identifies the generated branch with `R`, allowing the existing generated
natural-bottom route to be used without asking for components of every abstract below-chain. -/
noncomputable def kGeneratedNaturalBotComponentsData_of_externalRecursion
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (limitStep : KOneClusterPositiveLimitStepData k Γ F)
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    (hlimit :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        R o = limitStep ho (fun i => R i.1))
    (hbot :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        { v₀ : Γ //
          C.NaturalComponents k Γ ho ∧
            C.succStageBotBlockNextValEq k Γ ho v₀ ∧
              ∀ i : Set.Iio o, (i : Ordinal) = 0 →
                (C.limitBlock k Γ ho i).next.val k Γ = v₀ }) :
    Σ limitStep : KOneClusterPositiveLimitStepData k Γ F,
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C :=
          PositiveIioCoherentChainAt.recBelowOfNoRoot
            k Γ hsmall hunit hno limitStep ho
        { v₀ : Γ //
          C.NaturalComponents k Γ ho ∧
            C.succStageBotBlockNextValEq k Γ ho v₀ ∧
              ∀ i : Set.Iio o, (i : Ordinal) = 0 →
                (C.limitBlock k Γ ho i).next.val k Γ = v₀ } := by
  refine ⟨limitStep, ?_⟩
  intro o ho
  let Cgen :=
    PositiveIioCoherentChainAt.recBelowOfNoRoot
      k Γ hsmall hunit hno limitStep ho
  let Cext : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
  have hC : Cgen = Cext := by
    funext i
    exact PositiveIioCoherentChainAt.recOfNoRoot_eq_of_recursion_eq
      k Γ hsmall hunit hno limitStep R hsucc hlimit i.1
  change
    { v₀ : Γ //
      Cgen.NaturalComponents k Γ ho ∧
        Cgen.succStageBotBlockNextValEq k Γ ho v₀ ∧
          ∀ i : Set.Iio o, (i : Ordinal) = 0 →
            (Cgen.limitBlock k Γ ho i).next.val k Γ = v₀ }
  rw [hC]
  exact hbot ho

/-- External simultaneous recursion data provide fixed generated natural-bottom data using the
recursion itself as the total limit step.

This is the non-fallback entry point for the final construction: once a simultaneous recursion
builds `R` and natural-bottom data on its own below-chain, the generated `limitStep` can ignore an
arbitrary below-chain input and return the already constructed limit-stage value `R o`. -/
noncomputable def kGeneratedNaturalBotComponentsData_of_externalRecursionChain
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    (hbot :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        { v₀ : Γ //
          C.NaturalComponents k Γ ho ∧
            C.succStageBotBlockNextValEq k Γ ho v₀ ∧
              ∀ i : Set.Iio o, (i : Ordinal) = 0 →
                (C.limitBlock k Γ ho i).next.val k Γ = v₀ }) :
    Σ limitStep : KOneClusterPositiveLimitStepData k Γ F,
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C :=
          PositiveIioCoherentChainAt.recBelowOfNoRoot
            k Γ hsmall hunit hno limitStep ho
        { v₀ : Γ //
          C.NaturalComponents k Γ ho ∧
            C.succStageBotBlockNextValEq k Γ ho v₀ ∧
              ∀ i : Set.Iio o, (i : Ordinal) = 0 →
                (C.limitBlock k Γ ho i).next.val k Γ = v₀ } := by
  let limitStep : KOneClusterPositiveLimitStepData k Γ F :=
    fun {o} _ho _C => R o
  exact kGeneratedNaturalBotComponentsData_of_externalRecursion
    k Γ limitStep R hsucc (fun {_o} _ho => rfl) hbot

/-- External simultaneous recursion data provide generated natural-bottom data once natural
components are supplied on the external below-chain.

The successor-stage bottom next-value field is not an input here: it is recovered from the
successor law for `R`, the limit-stage bottom-next preservation, and the canonical zero
limit-block computation. -/
noncomputable def kGeneratedNaturalBotComponentsData_of_externalNaturalComponents
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    (hnat :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        C.NaturalComponents k Γ ho)
    (hlimitBotNext :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        (∀ i : Set.Iio o, (i : Ordinal) = 0 →
          (C.limitBlock k Γ ho i).next.val k Γ =
            (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
              (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) →
        (R o).BotBlockNextValEq k Γ
          ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ)) :
    Σ limitStep : KOneClusterPositiveLimitStepData k Γ F,
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C :=
          PositiveIioCoherentChainAt.recBelowOfNoRoot
            k Γ hsmall hunit hno limitStep ho
        { v₀ : Γ //
          C.NaturalComponents k Γ ho ∧
            C.succStageBotBlockNextValEq k Γ ho v₀ ∧
              ∀ i : Set.Iio o, (i : Ordinal) = 0 →
                (C.limitBlock k Γ ho i).next.val k Γ = v₀ } := by
  exact kGeneratedNaturalBotComponentsData_of_externalRecursionChain
    k Γ R hsucc
    (by
      intro o ho
      let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
      let v₀ : Γ :=
        (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
          (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ
      refine ⟨v₀, ?_, ?_, ?_⟩
      · exact hnat ho
      · exact PositiveIioCoherentChainAt.externalRecursion_succStageBotBlockNextValEq
          k Γ hsmall hunit hno R hsucc hlimitBotNext ho
      · intro i hi
        exact PositiveIioCoherentChainAt.externalRecursion_limitBlock_next_val_of_val_eq_zero
          k Γ hsmall hunit hno R hsucc ho i hi)

/-- External simultaneous recursion data provide generated natural-bottom data when the limit
branch is the natural-component limit step.

This is the final-shape bottom-next boundary for the simultaneous recursion: `BotBlockNextValEq`
for the limit states is derived from `limitStepOfNaturalComponents`, so it is not an independent
input. -/
noncomputable def kGeneratedNaturalBotComponentsData_of_externalNaturalLimitStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
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
        R o = C.limitStepOfNaturalComponents k Γ ho (hnat ho)) :
    Σ limitStep : KOneClusterPositiveLimitStepData k Γ F,
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C :=
          PositiveIioCoherentChainAt.recBelowOfNoRoot
            k Γ hsmall hunit hno limitStep ho
        { v₀ : Γ //
          C.NaturalComponents k Γ ho ∧
            C.succStageBotBlockNextValEq k Γ ho v₀ ∧
              ∀ i : Set.Iio o, (i : Ordinal) = 0 →
                (C.limitBlock k Γ ho i).next.val k Γ = v₀ } := by
  exact kGeneratedNaturalBotComponentsData_of_externalNaturalComponents
    k Γ R hsucc hnat
    (by
      intro o ho
      dsimp
      intro _hzero
      exact PositiveIioCoherentChainAt.externalRecursion_botBlockNextValEq_of_naturalLimitStep
        k Γ hsmall hunit hno R hsucc hnat hlimit o)

end HahnField

end

end HahnKaplanskyRealClosedness
