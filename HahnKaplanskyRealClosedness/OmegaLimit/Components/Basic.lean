/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Foundation.LimitExtend

/-!
# Basic positive limit-chain components
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
abbrev PositiveIioCoherentChainAtBelow
    (o : Ordinal) (F : Polynomial (valuationSubring k Γ)) : Type _ :=
  ∀ i : Set.Iio o, PositiveIioCoherentChainAt k Γ i.1 F

def PositiveIioCoherentChainAtBelow.succStageChain
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    PositiveIioCoherentChain k Γ (Order.succ i.1)
      (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) F :=
  C ⟨Order.succ i.1, ho.succ_lt i.2⟩
    (lt_of_le_of_lt bot_le (Order.lt_succ i.1))

@[simp]
theorem PositiveIioCoherentChainAtBelow.succStageChain_eq_apply_succ
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    C.succStageChain k Γ ho i =
      C ⟨Order.succ i.1, ho.succ_lt i.2⟩
        (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) :=
  rfl

def PositiveIioCoherentChainAtBelow.limitState
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    OneClusterState k Γ F :=
  (C.succStageChain k Γ ho i).succEndpointTopState k Γ

@[simp]
theorem PositiveIioCoherentChainAtBelow.limitState_eq_succStageChain_topState
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    C.limitState k Γ ho i =
      (C.succStageChain k Γ ho i).succEndpointTopState k Γ :=
  rfl

def PositiveIioCoherentChainAtBelow.limitBlock
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    OneClusterBlockSuccessor k Γ (C.limitState k Γ ho i) :=
  (C.succStageChain k Γ ho i).succEndpointTopBlock k Γ

@[simp]
theorem PositiveIioCoherentChainAtBelow.limitBlock_next_val_eq_succStageChain_topBlock
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    (C.limitBlock k Γ ho i).next.val k Γ =
      ((C.succStageChain k Γ ho i).succEndpointTopBlock k Γ).next.val k Γ :=
  rfl

def PositiveIioCoherentChainAtBelow.limitSeparated
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ {i j : Set.Iio o}, i < j →
    (C.limitBlock k Γ ho i).next.val k Γ ≤ (C.limitState k Γ ho j).val k Γ

def PositiveIioCoherentChainAtBelow.limitBlockChain
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho) :
    OneClusterBlockChain k Γ (Set.Iio o) F where
  state := C.limitState k Γ ho
  block := C.limitBlock k Γ ho
  separated := hsep

def PositiveIioCoherentChainAtBelow.limitNextValCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j),
    (C.limitBlock k Γ ho i).next.val k Γ =
      (((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ)

theorem PositiveIioCoherentChainAtBelow.limitSeparated_of_nextValCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.limitNextValCompatible k Γ ho) :
    C.limitSeparated k Γ ho := by
  intro i j hij
  let Cj := C.succStageChain k Γ ho j
  have hlt :
      ordinalIioSuccTopEmbOfLt hij < (ordinalIioSuccOrderTop j.1).top := by
    change (ordinalIioSuccTopEmbOfLt hij : Ordinal) < j.1
    rw [ordinalIioSuccTopEmbOfLt_val]
    exact hij
  have hsep := Cj.toOneClusterBlockChain.separated hlt
  rw [hcompat hij]
  exact hsep

def PositiveIioCoherentChainAtBelow.limitCoherent
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho) : Prop :=
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  let B := C.limitBlockChain k Γ ho hsep
  ∀ i : Set.Iio o,
    ofLex (((B.state i).source - (B.state ⊥).source : valuationSubring k Γ) :
      HahnField k Γ) =
      ((B.restrictLT k Γ i).diffHahnSeriesLimit k Γ)

def PositiveIioCoherentChainAtBelow.limitPrefixDiffHahnSeriesLimit
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho) (i : Set.Iio o) : HahnSeries Γ k :=
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  ((C.limitBlockChain k Γ ho hsep).restrictLT k Γ i).diffHahnSeriesLimit k Γ

theorem PositiveIioCoherentChainAtBelow.limitPrefixDiffHahnSeriesLimit_congr_sep
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep hsep' : C.limitSeparated k Γ ho) (i : Set.Iio o) :
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep' i := by
  change
    C.limitPrefixDiffHahnSeriesLimit k Γ ho
        (fun {i j : Set.Iio o} (hij : i < j) => hsep (i := i) (j := j) hij) i =
      C.limitPrefixDiffHahnSeriesLimit k Γ ho
        (fun {i j : Set.Iio o} (hij : i < j) => hsep' (i := i) (j := j) hij) i
  have h :
      (fun {i j : Set.Iio o} (hij : i < j) => hsep (i := i) (j := j) hij) =
        (fun {i j : Set.Iio o} (hij : i < j) => hsep' (i := i) (j := j) hij) :=
    Subsingleton.elim _ _
  rw [h]

theorem PositiveIioCoherentChainAtBelow.limitBlockChain_diffHahnSeriesLimit_congr_sep
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep hsep' : C.limitSeparated k Γ ho) :
    (C.limitBlockChain k Γ ho hsep).diffHahnSeriesLimit k Γ =
      (C.limitBlockChain k Γ ho hsep').diffHahnSeriesLimit k Γ := by
  change
    (C.limitBlockChain k Γ ho
      (fun {i j : Set.Iio o} (hij : i < j) =>
        hsep (i := i) (j := j) hij)).diffHahnSeriesLimit k Γ =
      (C.limitBlockChain k Γ ho
        (fun {i j : Set.Iio o} (hij : i < j) =>
          hsep' (i := i) (j := j) hij)).diffHahnSeriesLimit k Γ
  have h :
      (fun {i j : Set.Iio o} (hij : i < j) => hsep (i := i) (j := j) hij) =
        (fun {i j : Set.Iio o} (hij : i < j) => hsep' (i := i) (j := j) hij) :=
    Subsingleton.elim _ _
  rw [h]

@[simp]
theorem PositiveIioCoherentChainAtBelow.limitPrefixDiffHahnSeriesLimit_eq_zero
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho) (i : Set.Iio o) (hi : (i : Ordinal) = 0) :
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i = 0 := by
  unfold PositiveIioCoherentChainAtBelow.limitPrefixDiffHahnSeriesLimit
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  let _ : IsEmpty (Set.Iio i) :=
    ⟨fun l => by
      have hlt : (l.1.1 : Ordinal) < i.1 := l.2
      have hlt0 : (l.1.1 : Ordinal) < 0 := by
        rw [hi] at hlt
        exact hlt
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ l.1.1)) hlt0⟩
  exact OneClusterBlockChain.diffHahnSeriesLimit_eq_zero_of_isEmpty k Γ
    ((C.limitBlockChain k Γ ho hsep).restrictLT k Γ i)

def PositiveIioCoherentChainAtBelow.limitSourceDiffHahnSeries
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) : HahnSeries Γ k :=
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  ofLex (((C.limitState k Γ ho i).source - (C.limitState k Γ ho ⊥).source :
    valuationSubring k Γ) : HahnField k Γ)

def PositiveIioCoherentChainAtBelow.succStagePrefixDiffHahnSeriesLimit
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    HahnSeries Γ k :=
  let endpoint : Set.Iio (Order.succ i.1) := (ordinalIioSuccOrderTop i.1).top
  ((C.succStageChain k Γ ho i).toOneClusterBlockChain.restrictLT k Γ endpoint).diffHahnSeriesLimit
    k Γ

def PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) :
    HahnSeries Γ k :=
  let endpoint := ordinalIioSuccTopEmbOfLt hij
  ((C.succStageChain k Γ ho j).toOneClusterBlockChain.restrictLT k Γ endpoint)
    |>.diffHahnSeriesLimit k Γ

def PositiveIioCoherentChainAtBelow.limitPrefixCompatibleWithSuccStage
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j),
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij

def PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j),
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i

def PositiveIioCoherentChainAtBelow.succStageSourceDiffHahnSeries
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) : HahnSeries Γ k :=
  letI : OrderBot (Set.Iio (Order.succ i.1)) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ i.1))
  ofLex ((((C.succStageChain k Γ ho i).state (ordinalIioSuccOrderTop i.1).top).source -
    ((C.succStageChain k Γ ho i).state ⊥).source : valuationSubring k Γ) :
    HahnField k Γ)

def PositiveIioCoherentChainAtBelow.succStageRestrictedBotSource
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) :
    valuationSubring k Γ :=
  let endpoint := ordinalIioSuccEndpointEmbOfLt hij
  let hi : (0 : Ordinal) < endpoint.1 := by
    rw [ordinalIioSuccEndpointEmbOfLt_val]
    exact lt_of_le_of_lt bot_le (Order.lt_succ i.1)
  letI : OrderBot (Set.Iio endpoint.1) := ordinalIioOrderBotOfPos hi
  ((C.succStageChain k Γ ho j).toOneClusterBlockChain.restrictLT k Γ endpoint).state
    ((ordinalIioSubtypeIioEquiv endpoint).symm (⊥ : Set.Iio endpoint.1)) |>.source

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedBotSource_eq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) :
    C.succStageRestrictedBotSource k Γ ho hij =
      (letI : OrderBot (Set.Iio (Order.succ j.1)) :=
        ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ j.1))
       ((C.succStageChain k Γ ho j).state ⊥).source) := by
  unfold succStageRestrictedBotSource
  dsimp [OneClusterBlockChain.restrictLT]
  rw [ordinalIioSubtypeIioEquiv_symm_bot_succEndpointEmbOfLt hij]

def PositiveIioCoherentChainAtBelow.succStageBotSource
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    valuationSubring k Γ :=
  letI : OrderBot (Set.Iio (Order.succ i.1)) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ i.1))
  ((C.succStageChain k Γ ho i).state ⊥).source

def PositiveIioCoherentChainAtBelow.succStageBotSourceCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  ∀ i : Set.Iio o,
    C.succStageBotSource k Γ ho i = (C.limitState k Γ ho ⊥).source

def PositiveIioCoherentChainAtBelow.succStageRestrictedBotSourceCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  ∀ {i j : Set.Iio o} (hij : i < j),
    C.succStageRestrictedBotSource k Γ ho hij =
      (C.limitState k Γ ho ⊥).source

def PositiveIioCoherentChainAtBelow.succStageBotSourceProjectionCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  ∀ {i j : Set.Iio o} (_hij : i < j),
    (letI : OrderBot (Set.Iio (Order.succ j.1)) :=
      ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ j.1))
     ((C.succStageChain k Γ ho j).state ⊥).source) =
      (C.limitState k Γ ho ⊥).source

def PositiveIioCoherentChainAtBelow.BotSourceEq
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (s₀ : valuationSubring k Γ) : Prop :=
  ∀ i : Set.Iio o, ∀ hpos : (0 : Ordinal) < i.1,
    letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hpos
    OneClusterCoherentBlockChain.BotSourceEq k Γ (C i hpos) s₀

theorem PositiveIioCoherentChainAtBelow.restrictedBotSourceCompatible_of_projection
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageBotSourceProjectionCompatible k Γ ho) :
    C.succStageRestrictedBotSourceCompatible k Γ ho := by
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  intro i j hij
  rw [C.succStageRestrictedBotSource_eq k Γ ho hij]
  exact hcompat hij

theorem PositiveIioCoherentChainAtBelow.succStageBotSourceProjectionCompatible_of_botSource
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageBotSourceCompatible k Γ ho) :
    C.succStageBotSourceProjectionCompatible k Γ ho := by
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  intro i j hij
  exact hcompat j

theorem PositiveIioCoherentChainAtBelow.succStageBotSourceCompatible_of_botSourceEq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {s₀ : valuationSubring k Γ}
    (hC : C.BotSourceEq k Γ s₀)
    (hbot :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀) :
    C.succStageBotSourceCompatible k Γ ho := by
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  intro i
  unfold succStageBotSource
  have hpos : (0 : Ordinal) < Order.succ i.1 := lt_of_le_of_lt bot_le (Order.lt_succ i.1)
  have hsource :=
    hC ⟨Order.succ i.1, ho.succ_lt i.2⟩ hpos
  unfold OneClusterCoherentBlockChain.BotSourceEq at hsource
  exact hsource.trans hbot.symm

theorem PositiveIioCoherentChainAtBelow.succStageBotSourceCompatible_of_restrictedBot
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageRestrictedBotSourceCompatible k Γ ho) :
    C.succStageBotSourceCompatible k Γ ho := by
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  intro j
  by_cases hjzero : j.1 = (0 : Ordinal)
  · have hjbot : j = (⊥ : Set.Iio o) := by
      apply Subtype.ext
      rw [ordinalIio_bot_val_eq_zero ho.bot_lt]
      exact hjzero
    subst j
    unfold succStageBotSource limitState PositiveIioCoherentChain.succEndpointTopState
    have hidx :
        (⊥ : Set.Iio (Order.succ (⊥ : Set.Iio o).1)) =
          (ordinalIioSuccOrderTop (⊥ : Set.Iio o).1).top := by
      apply Subtype.ext
      rw [ordinalIio_bot_val_eq_zero
        (lt_of_le_of_lt bot_le (Order.lt_succ (⊥ : Set.Iio o).1))]
      exact (ordinalIio_bot_val_eq_zero ho.bot_lt).symm
    rw [hidx]
    rfl
  · let i : Set.Iio o := ⊥
    have hij : i < j := by
      change ((⊥ : Set.Iio o) : Ordinal) < j.1
      rw [ordinalIio_bot_val_eq_zero ho.bot_lt]
      exact lt_of_le_of_ne bot_le (fun h => hjzero h.symm)
    have hproj := C.succStageRestrictedBotSource_eq k Γ ho hij
    have hcompat_ij := hcompat hij
    rw [← hcompat_ij]
    rw [hproj]
    unfold succStageBotSource
    rfl

def PositiveIioCoherentChainAtBelow.limitCoherentSourceCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ i : Set.Iio o,
    C.limitSourceDiffHahnSeries k Γ ho i = C.succStageSourceDiffHahnSeries k Γ ho i

theorem PositiveIioCoherentChainAtBelow.limitCoherentSourceCompatible_of_succStageBot
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hbot : C.succStageBotSourceCompatible k Γ ho) :
    C.limitCoherentSourceCompatible k Γ ho := by
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  intro i
  unfold limitSourceDiffHahnSeries succStageSourceDiffHahnSeries limitState
  change
    ofLex ((((C.succStageChain k Γ ho i).succEndpointTopState k Γ).source -
      ((C.succStageChain k Γ ho ⊥).succEndpointTopState k Γ).source :
      valuationSubring k Γ) : HahnField k Γ) =
    ofLex ((((C.succStageChain k Γ ho i).state
      (ordinalIioSuccOrderTop i.1).top).source -
      C.succStageBotSource k Γ ho i : valuationSubring k Γ) : HahnField k Γ)
  rw [hbot i]
  rfl

def PositiveIioCoherentChainAtBelow.limitCoherentPrefixCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho) : Prop :=
  ∀ i : Set.Iio o,
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i

theorem PositiveIioCoherentChainAtBelow.limitCoherentPrefixCompatible_of_restricted
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (hlimit : C.limitPrefixCompatibleWithSuccStage k Γ ho hsep)
    (hstage : C.succStageRestrictedPrefixCompatible k Γ ho) :
    C.limitCoherentPrefixCompatible k Γ ho hsep := by
  intro i
  obtain ⟨j, hij⟩ := ordinalIio_forward_of_isSuccLimit ho i
  calc
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij := hlimit hij
    _ = C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := hstage hij

theorem PositiveIioCoherentChainAtBelow.limitCoherent_of_source_prefix_compatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (hsource : C.limitCoherentSourceCompatible k Γ ho)
    (hprefix : C.limitCoherentPrefixCompatible k Γ ho hsep) :
    C.limitCoherent k Γ ho hsep := by
  intro i
  have hstage := (C.succStageChain k Γ ho i).coherent_source (ordinalIioSuccOrderTop i.1).top
  have hsource_i := hsource i
  have hprefix_i := hprefix i
  change C.limitSourceDiffHahnSeries k Γ ho i =
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i
  rw [hsource_i]
  unfold succStageSourceDiffHahnSeries
  rw [hstage]
  unfold succStagePrefixDiffHahnSeriesLimit at hprefix_i
  rw [← hprefix_i]

end HahnField

end

end HahnKaplanskyRealClosedness
