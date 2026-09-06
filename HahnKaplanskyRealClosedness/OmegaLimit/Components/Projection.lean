/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Components.Restrict

/-!
# Projection positive limit-chain components
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

structure PositiveIioCoherentChainAtBelow.BlockProjectionComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop where
  next : C.succStageTopNextValProjectionCompatible k Γ ho
  bot : C.succStageBotSourceProjectionCompatible k Γ ho
  limitPrefix :
    let hnext' : C.succStageNextValCompatible k Γ ho :=
      fun {_ _} hij =>
        C.succStageNextValCompatible_of_prefixTop k Γ ho
          (C.prefixTopNextValCompatible_of_projection k Γ ho next) hij
    let hlimnext : C.limitNextValCompatible k Γ ho :=
      fun {_ _} hij =>
        C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext' hij
    let hsep : C.limitSeparated k Γ ho :=
      fun {_ _} hij => C.limitSeparated_of_nextValCompatible k Γ ho hlimnext hij
    C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep
  stagePrefix : C.succStageRestrictedBlockPrefixCompatible k Γ ho

/-- Projection-level next-value and bottom-source compatibility, plus block-prefix coherence,
assemble the block-projection component package. -/
theorem PositiveIioCoherentChainAtBelow.blockProjectionComponents_of_projection
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hnext : C.succStageTopNextValProjectionCompatible k Γ ho)
    (hbot : C.succStageBotSourceProjectionCompatible k Γ ho)
    (hlimit :
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
    C.BlockProjectionComponents k Γ ho where
  next := hnext
  bot := hbot
  limitPrefix := hlimit
  stagePrefix := hstage

/-- A full successor-stage next-value compatibility can be used in the projection-level
component constructor. -/
theorem PositiveIioCoherentChainAtBelow.blockProjectionComponents_of_next_projection
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hnext : C.succStageNextValCompatible k Γ ho)
    (hbot : C.succStageBotSourceProjectionCompatible k Γ ho)
    (hlimit :
      let hsep : C.limitSeparated k Γ ho :=
        fun {_ _} hij =>
          C.limitSeparated_of_nextValCompatible k Γ ho
            (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext) hij
      C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep)
    (hstage : C.succStageRestrictedBlockPrefixCompatible k Γ ho) :
    C.BlockProjectionComponents k Γ ho := by
  let hproj : C.succStageTopNextValProjectionCompatible k Γ ho :=
    C.projectionNextValCompatible_of_succStageNext k Γ ho hnext
  exact C.blockProjectionComponents_of_projection k Γ ho hproj hbot
    (by
      dsimp [hproj]
      exact hlimit)
    hstage

theorem PositiveIioCoherentChainAtBelow.blockProjectionComponents_of_botSourceEq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hnext : C.succStageTopNextValProjectionCompatible k Γ ho)
    {s₀ : valuationSubring k Γ}
    (hC : C.BotSourceEq k Γ s₀)
    (hbot :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀)
    (hlimit :
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
    C.BlockProjectionComponents k Γ ho :=
  C.blockProjectionComponents_of_projection k Γ ho hnext
    (C.succStageBotSourceProjectionCompatible_of_botSource k Γ ho
      (C.succStageBotSourceCompatible_of_botSourceEq k Γ ho hC hbot))
    hlimit hstage

theorem PositiveIioCoherentChainAtBelow.blockProjectionComponents_of_splitTop
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
    C.BlockProjectionComponents k Γ ho := by
  let hnext : C.succStageTopNextValProjectionCompatible k Γ ho :=
    C.succStageTopNextValProjectionCompatible_of_bot_positive k Γ ho
      (fun hij hi =>
        C.succStageTopNextValProjectionCompatible_bot k Γ ho
          hbotNext hlimitBotNext hij hi)
      hpositive
  exact C.blockProjectionComponents_of_botSourceEq k Γ ho hnext hC hbotSource
    (by
      dsimp [hnext] at hlimit ⊢
      exact hlimit)
    hstage

/-- A bundled version of the split-top data used to build block-projection components.

This is the proof-facing boundary for the current positive-limit route: the bottom block is
handled separately, while positive-index top projections and prefix compatibility provide the
remaining component data. -/
structure PositiveIioCoherentChainAtBelow.SplitTopComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Type _ where
  source : valuationSubring k Γ
  botValue : Γ
  botSource : C.BotSourceEq k Γ source
  limitBotSource :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
     (C.limitState k Γ ho ⊥).source) = source
  botNext : C.succStageBotBlockNextValEq k Γ ho botValue
  limitBotNext :
    ∀ i : Set.Iio o, (i : Ordinal) = 0 →
      (C.limitBlock k Γ ho i).next.val k Γ = botValue
  positiveProjection : C.succStageTopNextValProjectionCompatiblePositive k Γ ho
  limitPrefix :
    let hnext : C.succStageTopNextValProjectionCompatible k Γ ho :=
      C.succStageTopNextValProjectionCompatible_of_bot_positive k Γ ho
        (fun hij hi =>
          C.succStageTopNextValProjectionCompatible_bot k Γ ho
            botNext limitBotNext hij hi)
        positiveProjection
    let hnext' : C.succStageNextValCompatible k Γ ho :=
      fun {_ _} hij =>
        C.succStageNextValCompatible_of_prefixTop k Γ ho
          (C.prefixTopNextValCompatible_of_projection k Γ ho hnext) hij
    let hlimnext : C.limitNextValCompatible k Γ ho :=
      fun {_ _} hij =>
        C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext' hij
    let hsep : C.limitSeparated k Γ ho :=
      fun {_ _} hij => C.limitSeparated_of_nextValCompatible k Γ ho hlimnext hij
    C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep
  stagePrefix : C.succStageRestrictedBlockPrefixCompatible k Γ ho

theorem PositiveIioCoherentChainAtBelow.blockProjectionComponents_of_botSourceEq_compat
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hnext : C.succStageNextValCompatible k Γ ho)
    {s₀ : valuationSubring k Γ}
    (hC : C.BotSourceEq k Γ s₀)
    (hbot :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀)
    (hlimit :
      let hsep : C.limitSeparated k Γ ho :=
        fun {_ _} hij =>
          C.limitSeparated_of_nextValCompatible k Γ ho
            (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext) hij
      C.limitPrefixCompatibleWithSuccStage k Γ ho hsep)
    (hstage : C.succStageRestrictedPrefixCompatible k Γ ho) :
    C.BlockProjectionComponents k Γ ho := by
  let hsep : C.limitSeparated k Γ ho :=
    fun {_ _} hij =>
      C.limitSeparated_of_nextValCompatible k Γ ho
        (C.limitNextValCompatible_of_succStageNextValCompatible k Γ ho hnext) hij
  exact C.blockProjectionComponents_of_next_projection k Γ ho hnext
    (C.succStageBotSourceProjectionCompatible_of_botSource k Γ ho
      (C.succStageBotSourceCompatible_of_botSourceEq k Γ ho hC hbot))
    (by
      dsimp [hsep] at hlimit ⊢
      exact C.limitBlockPrefixCompatibleWithSuccStage_of_prefix k Γ ho hsep hlimit)
    (C.succStageRestrictedBlockPrefixCompatible_of_prefix k Γ ho hstage)

end HahnField

end

end HahnKaplanskyRealClosedness
