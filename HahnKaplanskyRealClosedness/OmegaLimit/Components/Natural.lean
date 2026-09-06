/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Components.Projection

/-!
# Natural positive limit-chain components
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

def PositiveIioCoherentChainAtBelow.NaturalComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∃ s₀ : valuationSubring k Γ,
    C.BotSourceEq k Γ s₀ ∧
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
     (C.limitState k Γ ho ⊥).source) = s₀ ∧
    ∃ hnext : C.succStageNextValCompatible k Γ ho,
      (let hsep : C.limitSeparated k Γ ho :=
        fun {_ _} hij =>
          C.limitSeparated_of_nextValCompatible k Γ ho
            (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext) hij
       C.limitPrefixCompatibleWithSuccStage k Γ ho hsep) ∧
      C.succStageRestrictedPrefixCompatible k Γ ho

theorem PositiveIioCoherentChainAtBelow.naturalComponentsNext
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho) :
    C.succStageNextValCompatible k Γ ho := by
  classical
  let hs₀ := Classical.choose_spec hcompat
  exact
    @Classical.choose (C.succStageNextValCompatible k Γ ho)
      (fun hnext =>
        (let hsep : C.limitSeparated k Γ ho :=
          fun {_ _} hij =>
            C.limitSeparated_of_nextValCompatible k Γ ho
              (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext) hij
         C.limitPrefixCompatibleWithSuccStage k Γ ho hsep) ∧
        C.succStageRestrictedPrefixCompatible k Γ ho)
      hs₀.2.2

theorem PositiveIioCoherentChainAtBelow.naturalComponentsSeparated
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho) :
    C.limitSeparated k Γ ho :=
  fun {_ _} hij =>
    C.limitSeparated_of_nextValCompatible k Γ ho
      (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho
        (C.naturalComponentsNext k Γ ho hcompat)) hij

theorem PositiveIioCoherentChainAtBelow.limitPrefixCompatibleWithSuccStage_of_naturalComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho) :
    C.limitPrefixCompatibleWithSuccStage k Γ ho
      (C.naturalComponentsSeparated k Γ ho hcompat) := by
  classical
  let hs₀ := Classical.choose_spec hcompat
  have htailSpec :
      (let hsep : C.limitSeparated k Γ ho :=
        fun {_ _} hij =>
          C.limitSeparated_of_nextValCompatible k Γ ho
            (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho
              (C.naturalComponentsNext k Γ ho hcompat)) hij
       C.limitPrefixCompatibleWithSuccStage k Γ ho hsep) ∧
        C.succStageRestrictedPrefixCompatible k Γ ho :=
    @Classical.choose_spec (C.succStageNextValCompatible k Γ ho)
      (fun hnext =>
        (let hsep : C.limitSeparated k Γ ho :=
          fun {_ _} hij =>
            C.limitSeparated_of_nextValCompatible k Γ ho
              (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext) hij
         C.limitPrefixCompatibleWithSuccStage k Γ ho hsep) ∧
        C.succStageRestrictedPrefixCompatible k Γ ho)
      hs₀.2.2
  change ∀ {i j : Set.Iio o} (hij : i < j),
    C.limitPrefixDiffHahnSeriesLimit k Γ ho
        (C.naturalComponentsSeparated k Γ ho hcompat) i =
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij
  exact htailSpec.1

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixCompatible_of_naturalComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho) :
    C.succStageRestrictedPrefixCompatible k Γ ho := by
  classical
  let hs₀ := Classical.choose_spec hcompat
  have htailSpec :
      (let hsep : C.limitSeparated k Γ ho :=
        fun {_ _} hij =>
          C.limitSeparated_of_nextValCompatible k Γ ho
            (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho
              (C.naturalComponentsNext k Γ ho hcompat)) hij
       C.limitPrefixCompatibleWithSuccStage k Γ ho hsep) ∧
        C.succStageRestrictedPrefixCompatible k Γ ho :=
    @Classical.choose_spec (C.succStageNextValCompatible k Γ ho)
      (fun hnext =>
        (let hsep : C.limitSeparated k Γ ho :=
          fun {_ _} hij =>
            C.limitSeparated_of_nextValCompatible k Γ ho
              (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext) hij
         C.limitPrefixCompatibleWithSuccStage k Γ ho hsep) ∧
        C.succStageRestrictedPrefixCompatible k Γ ho)
      hs₀.2.2
  change ∀ {i j : Set.Iio o} (hij : i < j),
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  exact htailSpec.2

theorem PositiveIioCoherentChainAtBelow.blockProjectionComponents_of_natural
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho) :
    C.BlockProjectionComponents k Γ ho := by
  rcases hcompat with ⟨s₀, hC, hbot, hnext, hlimit, hstage⟩
  exact C.blockProjectionComponents_of_botSourceEq_compat k Γ ho
    hnext hC hbot hlimit hstage

theorem PositiveIioCoherentChainAtBelow.naturalComponents_of_blockProjectionComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {s₀ : valuationSubring k Γ}
    (hC : C.BotSourceEq k Γ s₀)
    (hbot :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀)
    (hcompat : C.BlockProjectionComponents k Γ ho) :
    C.NaturalComponents k Γ ho := by
  let hnext : C.succStageNextValCompatible k Γ ho :=
    fun {_ _} hij =>
      C.succStageNextValCompatible_of_prefixTop k Γ ho
        (C.prefixTopNextValCompatible_of_projection k Γ ho hcompat.next) hij
  refine ⟨s₀, hC, hbot, hnext, ?_, ?_⟩
  · let hsep : C.limitSeparated k Γ ho :=
      fun {_ _} hij =>
        C.limitSeparated_of_nextValCompatible k Γ ho
          (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext) hij
    change C.limitPrefixCompatibleWithSuccStage k Γ ho hsep
    exact C.limitPrefixCompatibleWithSuccStage_of_blockPrefix k Γ ho hsep
      hcompat.limitPrefix
  · exact C.succStageRestrictedPrefixCompatible_of_blockPrefix k Γ ho
      hcompat.stagePrefix

theorem PositiveIioCoherentChainAtBelow.naturalComponents_of_splitTop
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {s₀ : valuationSubring k Γ} {v₀ : Γ}
    (hC : C.BotSourceEq k Γ s₀)
    (hbotSource :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀)
    (hbotNext : C.succStageBotBlockNextValEq k Γ ho v₀)
    (hlimitBotNext :
      ∀ i : Set.Iio o, (i : Ordinal) = 0 →
        (C.limitBlock k Γ ho i).next.val k Γ = v₀)
    (hpositive : C.succStageTopNextValProjectionCompatiblePositive k Γ ho)
    (hlimit :
      let hnext : C.succStageTopNextValProjectionCompatible k Γ ho :=
        C.succStageTopNextValProjectionCompatible_of_bot_positive k Γ ho
          (fun hij hi =>
            C.succStageTopNextValProjectionCompatible_bot k Γ ho
              hbotNext hlimitBotNext hij hi)
          hpositive
      let hnext' : C.succStageNextValCompatible k Γ ho :=
        fun {_ _} hij =>
          C.succStageNextValCompatible_of_prefixTop k Γ ho
            (C.prefixTopNextValCompatible_of_projection k Γ ho hnext) hij
      let hlimnext : C.limitNextValCompatible k Γ ho :=
        fun {_ _} hij =>
          C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext' hij
      let hsep : C.limitSeparated k Γ ho :=
        fun {_ _} hij => C.limitSeparated_of_nextValCompatible k Γ ho hlimnext hij
      C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep)
    (hstage : C.succStageRestrictedBlockPrefixCompatible k Γ ho) :
    C.NaturalComponents k Γ ho := by
  let hcompat : C.BlockProjectionComponents k Γ ho :=
    C.blockProjectionComponents_of_splitTop k Γ ho hC hbotSource
      hbotNext hlimitBotNext hpositive hlimit hstage
  exact C.naturalComponents_of_blockProjectionComponents k Γ ho hC hbotSource hcompat

theorem PositiveIioCoherentChainAtBelow.naturalComponents_of_splitTopComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.SplitTopComponents k Γ ho) :
    C.NaturalComponents k Γ ho := by
  rcases hcompat with
    ⟨s₀, v₀, hC, hbotSource, hbotNext, hlimitBotNext, hpositive, hlimit, hstage⟩
  exact C.naturalComponents_of_splitTop k Γ ho
    hC hbotSource hbotNext hlimitBotNext hpositive hlimit hstage

theorem PositiveIioCoherentChainAtBelow.limitCompatible_of_blockProjectionComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.BlockProjectionComponents k Γ ho) :
    C.LimitCompatible k Γ ho := by
  let hnext : C.succStageNextValCompatible k Γ ho :=
    fun {_ _} hij => by
      rw [C.succStageRestrictedTopNextVal_eq k Γ ho hij]
      exact (hcompat.next hij).symm
  let hlimnext : C.limitNextValCompatible k Γ ho :=
    fun {_ _} hij =>
      C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext hij
  let hsep : C.limitSeparated k Γ ho :=
    fun {_ _} hij => C.limitSeparated_of_nextValCompatible k Γ ho hlimnext hij
  have hsource : C.limitCoherentSourceCompatible k Γ ho :=
    C.limitCoherentSourceCompatible_of_succStageBot k Γ ho
      (C.succStageBotSourceCompatible_of_restrictedBot k Γ ho
        (C.restrictedBotSourceCompatible_of_projection k Γ ho hcompat.bot))
  have hprefix : C.limitCoherentPrefixCompatible k Γ ho hsep :=
    C.limitCoherentPrefixCompatible_of_restricted k Γ ho hsep
      (C.limitPrefixCompatibleWithSuccStage_of_blockPrefix k Γ ho hsep
        hcompat.limitPrefix)
      (C.succStageRestrictedPrefixCompatible_of_blockPrefix k Γ ho
        hcompat.stagePrefix)
  exact
    { nextVal := hlimnext
      coherent := C.limitCoherent_of_source_prefix_compatible k Γ ho hsep hsource hprefix }

/-- Natural recursive component data can be consumed directly as full limit compatibility. -/
theorem PositiveIioCoherentChainAtBelow.limitCompatible_of_natural
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho) :
    C.LimitCompatible k Γ ho :=
  C.limitCompatible_of_blockProjectionComponents k Γ ho
    (C.blockProjectionComponents_of_natural k Γ ho hcompat)

end HahnField

end

end HahnKaplanskyRealClosedness
