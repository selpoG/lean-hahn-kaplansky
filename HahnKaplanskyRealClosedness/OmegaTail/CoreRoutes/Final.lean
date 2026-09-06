/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaTail.CoreRoutes.Compatibility
import HahnKaplanskyRealClosedness.OmegaTail.Data

/-!
# Final generated natural-limit and block-projection core data
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

universe u v

namespace HahnField

variable (k : Type u) (Γ : Type v)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

open PositiveIioCoherentChainAt

/-- Assemble generated block-projection core data once the generated bottom-source and bottom
fields themselves are available. -/
noncomputable def kGeneratedBlockProjectionCoreData_of_generatedFieldsSourceBot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (limitStep : KOneClusterPositiveLimitStepData k Γ F)
    (botSource :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        ∃ s₀ : valuationSubring k Γ,
          (PositiveIioCoherentChainAt.recBelowOfNoRoot
            k Γ hsmall hunit hno limitStep ho).BotSourceEq k Γ s₀ ∧
          (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
           ((PositiveIioCoherentChainAt.recBelowOfNoRoot
            k Γ hsmall hunit hno limitStep ho).limitState k Γ ho ⊥).source) = s₀)
    (bot :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C := PositiveIioCoherentChainAt.recBelowOfNoRoot
          k Γ hsmall hunit hno limitStep ho
        { v₀ : Γ //
          C.succStageBotBlockNextValEq k Γ ho v₀ ∧
            ∀ i : Set.Iio o, (i : Ordinal) = 0 →
              (C.limitBlock k Γ ho i).next.val k Γ = v₀ })
    (components :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        (PositiveIioCoherentChainAt.recBelowOfNoRoot k Γ hsmall hunit hno limitStep ho)
          |>.BlockProjectionComponents k Γ ho) :
    KOneClusterPositiveGeneratedBlockProjectionCoreData k Γ hsmall hunit hno :=
  { limitStep := limitStep
    botSource := botSource
    bot := bot
    components := components }

/-- Fixed generated natural-bottom component data provide fixed generated block-projection core
data. -/
noncomputable def kGeneratedBlockProjectionCoreData_of_generatedNaturalBotComponentsData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (hstep :
      Σ limitStep : KOneClusterPositiveLimitStepData k Γ F,
        ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
          let C :=
            PositiveIioCoherentChainAt.recBelowOfNoRoot
              k Γ hsmall hunit hno limitStep ho
          { v₀ : Γ //
            C.NaturalComponents k Γ ho ∧
              C.succStageBotBlockNextValEq k Γ ho v₀ ∧
                ∀ i : Set.Iio o, (i : Ordinal) = 0 →
                  (C.limitBlock k Γ ho i).next.val k Γ = v₀ }) :
    KOneClusterPositiveGeneratedBlockProjectionCoreData k Γ hsmall hunit hno := by
  refine kGeneratedBlockProjectionCoreData_of_generatedFieldsSourceBot k Γ hstep.1 ?_ ?_ ?_
  · intro o ho
    rcases hstep.2 ho with ⟨_v₀, hnat, _hbotNext, _hzero⟩
    rcases hnat with ⟨s₀, hsource, hbotSource, _hnext, _hlimit, _hstage⟩
    exact ⟨s₀, hsource, hbotSource⟩
  · intro o ho
    rcases hstep.2 ho with ⟨v₀, _hnat, hbotNext, hzero⟩
    exact ⟨v₀, hbotNext, hzero⟩
  · intro o ho
    let C := PositiveIioCoherentChainAt.recBelowOfNoRoot k Γ hsmall hunit hno hstep.1 ho
    exact C.blockProjectionComponents_of_natural k Γ ho (hstep.2 ho).2.1

/-- Final external natural-limit recursion data supply generated natural-bottom data. -/
noncomputable def
    KOneClusterPositiveFinalExternalNaturalLimitStepData.generatedNaturalBotComponentsData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (D : KOneClusterPositiveFinalExternalNaturalLimitStepData k Γ hsmall hunit hno) :
    Σ limitStep : KOneClusterPositiveLimitStepData k Γ F,
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C :=
          PositiveIioCoherentChainAt.recBelowOfNoRoot
            k Γ hsmall hunit hno limitStep ho
        { v₀ : Γ //
          C.NaturalComponents k Γ ho ∧
            C.succStageBotBlockNextValEq k Γ ho v₀ ∧
              ∀ i : Set.Iio o, (i : Ordinal) = 0 →
                (C.limitBlock k Γ ho i).next.val k Γ = v₀ } :=
  kGeneratedNaturalBotComponentsData_of_externalNaturalLimitStep
    k Γ D.R D.hsucc D.hnat D.hlimit

/-- Final external natural-limit recursion data supply generated block-projection core data. -/
noncomputable def
    KOneClusterPositiveFinalExternalNaturalLimitStepData.generatedBlockProjectionCoreData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (D : KOneClusterPositiveFinalExternalNaturalLimitStepData k Γ hsmall hunit hno) :
    KOneClusterPositiveGeneratedBlockProjectionCoreData k Γ hsmall hunit hno :=
  kGeneratedBlockProjectionCoreData_of_generatedNaturalBotComponentsData k Γ
    D.generatedNaturalBotComponentsData

/-- The final ordinal stack recursion supplies generated block-projection core data. -/
noncomputable def kGeneratedBlockProjectionCoreData_of_ordinalStackRec
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F} :
    KOneClusterPositiveGeneratedBlockProjectionCoreData k Γ hsmall hunit hno :=
  KOneClusterPositiveFinalExternalNaturalLimitStepData.ofOrdinalStackRec
    (k := k) (Γ := Γ) |>.generatedBlockProjectionCoreData (k := k) (Γ := Γ)

/-- The final ordinal stack recursion proves the positive generated block-projection core
hypothesis. -/
theorem kGeneratedBlockProjectionCore_of_ordinalStackRec
    [IsRealClosed k] [DivisibleBy Γ ℕ] :
    KOneClusterPositiveGeneratedBlockProjectionCoreHypothesis k Γ := by
  intro F hsmall hunit hno
  exact ⟨kGeneratedBlockProjectionCoreData_of_ordinalStackRec (k := k) (Γ := Γ)⟩

/-- Generated limit-step compatibility data provides the generated primitive limit-step input. -/
theorem kOneClusterPositiveGeneratedLimitStepHypothesis_of_generatedLimitStepCompat
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hlimit : KOneClusterPositiveGeneratedLimitStepCompatHypothesis k Γ) :
    KOneClusterPositiveGeneratedLimitStepHypothesis k Γ := by
  intro F hsmall hunit hno
  rcases hlimit hsmall hunit hno with ⟨hstep⟩
  exact ⟨hstep.limitStep⟩

/-- Fixed generated block-projection core data specialize to generated limit-step compatibility
data.

Unlike the component boundary above, this uses only generated-chain bottom-source data. -/
noncomputable def kGeneratedLimitStepCompatData_of_generatedBlockProjectionCoreData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (hstep : KOneClusterPositiveGeneratedBlockProjectionCoreData k Γ hsmall hunit hno) :
    KOneClusterPositiveGeneratedLimitStepCompatData k Γ hsmall hunit hno := by
  refine {
    limitStep := hstep.limitStep
    bot := hstep.bot
    components := ?_ }
  intro o ho
  let C := PositiveIioCoherentChainAt.recBelowOfNoRoot k Γ hsmall hunit hno
    hstep.limitStep ho
  rcases hstep.botSource ho with ⟨s₀, hsource, hbotSource⟩
  exact C.naturalComponents_of_blockProjectionComponents k Γ ho
    hsource hbotSource
    (hstep.components ho)

/-- Generated block-projection core data specializes to generated limit-step compatibility data. -/
theorem kOneClusterPositiveGeneratedLimitStepCompatHypothesis_of_generatedBlockProjectionCore
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hlimit : KOneClusterPositiveGeneratedBlockProjectionCoreHypothesis k Γ) :
    KOneClusterPositiveGeneratedLimitStepCompatHypothesis k Γ := by
  intro F hsmall hunit hno
  rcases hlimit hsmall hunit hno with ⟨hstep⟩
  exact ⟨kGeneratedLimitStepCompatData_of_generatedBlockProjectionCoreData k Γ hstep⟩

/-- Short alias from generated block-projection core data to generated limit-step compatibility. -/
theorem kGeneratedLimitStepCompat_of_generatedBlockProjectionCore
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hlimit : KOneClusterPositiveGeneratedBlockProjectionCoreHypothesis k Γ) :
    KOneClusterPositiveGeneratedLimitStepCompatHypothesis k Γ :=
  kOneClusterPositiveGeneratedLimitStepCompatHypothesis_of_generatedBlockProjectionCore
    k Γ hlimit

end HahnField

end

end HahnKaplanskyRealClosedness
