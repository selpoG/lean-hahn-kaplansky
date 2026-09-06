/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaTail.CoreRoutes.BelowChain

/-!
# Conditional and closed limit extensions
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

universe u v

namespace HahnField

variable (k : Type u) (Γ : Type v)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

open PositiveIioCoherentChainAt

/-- Conditional limit extension of a final natural initial segment system.

The only remaining inputs are the two current block-prefix fields for the extracted below-chain.
All positive-projection and bottom inputs are supplied from the lower segment systems. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegment.limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1)
    (hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩)
    (hlimitBlock :
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      let hpositive : C.succStageTopNextValProjectionCompatiblePositive k Γ ho :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_positiveProjection
          (k := k) (Γ := Γ) ho Sbelow hSbelow
      let hbotNext : C.succStageBotBlockNextValEq k Γ ho
          ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succStageBotBlockNextValEq
          (k := k) (Γ := Γ) ho Sbelow
      let hlimitBotNext :
          ∀ i : Set.Iio o, (i : Ordinal) = 0 →
            (C.limitBlock k Γ ho i).next.val k Γ =
              (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
                (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_limitBlock_next_zero
          (k := k) (Γ := Γ) ho Sbelow hSbelow
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
    (hstageBlock :
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      C.succStageRestrictedBlockPrefixCompatible k Γ ho) :
    KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o := by
  classical
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let hnatTop : C.NaturalComponents k Γ ho :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_natural_of_blockPrefix
      (k := k) (Γ := Γ) ho Sbelow hSbelow hlimitBlock hstageBlock
  let top : PositiveIioCoherentChainAt k Γ o F :=
    C.limitStepOfNaturalComponents k Γ ho hnatTop
  let Rlimit : ∀ p : Set.Iic o, PositiveIioCoherentChainAt k Γ p.1 F := fun p =>
    if hp : p.1 < o then
      C ⟨p.1, hp⟩
    else
      have hp_eq : p.1 = o := le_antisymm p.2 (le_of_not_gt hp)
      hp_eq.symm ▸ top
  have Rlimit_lower :
      ∀ {p : Ordinal} (hp_lt : p < o) (hp_le : p ≤ o),
        Rlimit ⟨p, hp_le⟩ = C ⟨p, hp_lt⟩ := by
    intro p hp_lt hp_le
    simp [Rlimit, hp_lt]
  have Rlimit_top :
      Rlimit ⟨o, (show o ≤ o from le_rfl)⟩ = top := by
    simp [Rlimit]
  let hnatLimit :
      ∀ {p : Ordinal} (hp : p ≤ o) (hpLimit : Order.IsSuccLimit p),
        let Cp : PositiveIioCoherentChainAtBelow k Γ p F :=
          fun i => Rlimit ⟨i.1, le_trans (le_of_lt i.2) hp⟩
        Cp.NaturalComponents k Γ hpLimit := by
    intro p hp hpLimit
    by_cases hp_lt : p < o
    · let Cseg : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => Rlimit ⟨i.1, le_trans (le_of_lt i.2) hp⟩
      let Clower : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => C ⟨i.1, (show i.1 < o from i.2.trans hp_lt)⟩
      have hC : Cseg = Clower := by
        funext i
        exact Rlimit_lower (show i.1 < o from i.2.trans hp_lt)
          (le_trans (le_of_lt i.2) hp)
      change Cseg.NaturalComponents k Γ hpLimit
      rw [hC]
      exact
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
          (k := k) (Γ := Γ) Sbelow hSbelow ⟨p, hp_lt⟩ hpLimit
    · have hp_eq : p = o := le_antisymm hp (le_of_not_gt hp_lt)
      subst p
      let Cseg : PositiveIioCoherentChainAtBelow k Γ o F :=
        fun i => Rlimit ⟨i.1, le_trans (le_of_lt i.2) (show o ≤ o from le_rfl)⟩
      have hC : Cseg = C := by
        funext i
        exact Rlimit_lower i.2 (le_trans (le_of_lt i.2) (show o ≤ o from le_rfl))
      change Cseg.NaturalComponents k Γ ho
      rw [hC]
      exact hnatTop
  refine
    { R := Rlimit
      hsucc := ?_
      hnat := hnatLimit
      hlimit := ?_ }
  · intro p hp
    have hp_ne : Order.succ p ≠ o := by
      intro h
      subst o
      exact Order.not_isSuccLimit_succ p ho
    have hp_lt : Order.succ p < o := lt_of_le_of_ne hp hp_ne
    have hp_pred_le : p ≤ o := le_trans (le_of_lt (Order.lt_succ p)) hp
    rw [Rlimit_lower hp_lt hp]
    rw [Rlimit_lower ((Order.lt_succ p).trans hp_lt) hp_pred_le]
    exact KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
      (k := k) (Γ := Γ) Sbelow hSbelow hp_lt
  · intro p hp hpLimit
    by_cases hp_lt : p < o
    · let Cseg : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => Rlimit ⟨i.1, le_trans (le_of_lt i.2) hp⟩
      let Clower : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => C ⟨i.1, (show i.1 < o from i.2.trans hp_lt)⟩
      have hC : Cseg = Clower := by
        funext i
        exact Rlimit_lower (show i.1 < o from i.2.trans hp_lt)
          (le_trans (le_of_lt i.2) hp)
      let hnatLower : Clower.NaturalComponents k Γ hpLimit :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
          (k := k) (Γ := Γ) Sbelow hSbelow ⟨p, hp_lt⟩ hpLimit
      have hstep :
          Clower.limitStepOfNaturalComponents k Γ hpLimit hnatLower =
            Cseg.limitStepOfNaturalComponents k Γ hpLimit (hnatLimit hp hpLimit) := by
        exact (PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_congr
          (k := k) (Γ := Γ) hpLimit hC (hnatLimit hp hpLimit) hnatLower).symm
      calc
        Rlimit ⟨p, hp⟩ = C ⟨p, hp_lt⟩ := Rlimit_lower hp_lt hp
        _ = Clower.limitStepOfNaturalComponents k Γ hpLimit hnatLower := by
          exact
            KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimit
              (k := k) (Γ := Γ) Sbelow hSbelow ⟨p, hp_lt⟩ hpLimit
        _ = Cseg.limitStepOfNaturalComponents k Γ hpLimit
              (hnatLimit hp hpLimit) := hstep
    · have hp_eq : p = o := le_antisymm hp (le_of_not_gt hp_lt)
      subst p
      let Cseg : PositiveIioCoherentChainAtBelow k Γ o F :=
        fun i => Rlimit ⟨i.1, le_trans (le_of_lt i.2) (show o ≤ o from le_rfl)⟩
      have hC : Cseg = C := by
        funext i
        exact Rlimit_lower i.2 (le_trans (le_of_lt i.2) (show o ≤ o from le_rfl))
      have hstep :
          C.limitStepOfNaturalComponents k Γ ho hnatTop =
            Cseg.limitStepOfNaturalComponents k Γ ho
              (hnatLimit (show o ≤ o from le_rfl) ho) := by
        exact (PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_congr
          (k := k) (Γ := Γ) ho hC
          (hnatLimit (show o ≤ o from le_rfl) ho) hnatTop).symm
      calc
        Rlimit ⟨o, (show o ≤ o from le_rfl)⟩ = top := Rlimit_top
        _ = C.limitStepOfNaturalComponents k Γ ho hnatTop := rfl
        _ = Cseg.limitStepOfNaturalComponents k Γ ho
              (hnatLimit (show o ≤ o from le_rfl) ho) := hstep

/-- Lower points of the conditional limit segment are exactly the extracted below-chain. -/
@[simp] theorem KOneClusterPositiveFinalExternalNaturalSegment.limit_R_lower
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o p : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1)
    (hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩)
    (hlimitBlock :
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      let hpositive : C.succStageTopNextValProjectionCompatiblePositive k Γ ho :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_positiveProjection
          (k := k) (Γ := Γ) ho Sbelow hSbelow
      let hbotNext : C.succStageBotBlockNextValEq k Γ ho
          ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succStageBotBlockNextValEq
          (k := k) (Γ := Γ) ho Sbelow
      let hlimitBotNext :
          ∀ i : Set.Iio o, (i : Ordinal) = 0 →
            (C.limitBlock k Γ ho i).next.val k Γ =
              (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
                (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_limitBlock_next_zero
          (k := k) (Γ := Γ) ho Sbelow hSbelow
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
    (hstageBlock :
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      C.succStageRestrictedBlockPrefixCompatible k Γ ho)
    (hp_lt : p < o) (hp_le : p ≤ o) :
    (KOneClusterPositiveFinalExternalNaturalSegment.limit
        (k := k) (Γ := Γ) ho Sbelow hSbelow
        hlimitBlock hstageBlock).R ⟨p, hp_le⟩ =
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow) ⟨p, hp_lt⟩ := by
  classical
  unfold KOneClusterPositiveFinalExternalNaturalSegment.limit
  simp [hp_lt]

/-- Conditional limit extension of coherent final external natural-limit segment systems. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystem.limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1)
    (hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩)
    (hlimitBlock :
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      let hpositive : C.succStageTopNextValProjectionCompatiblePositive k Γ ho :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_positiveProjection
          (k := k) (Γ := Γ) ho Sbelow hSbelow
      let hbotNext : C.succStageBotBlockNextValEq k Γ ho
          ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succStageBotBlockNextValEq
          (k := k) (Γ := Γ) ho Sbelow
      let hlimitBotNext :
          ∀ i : Set.Iio o, (i : Ordinal) = 0 →
            (C.limitBlock k Γ ho i).next.val k Γ =
              (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
                (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_limitBlock_next_zero
          (k := k) (Γ := Γ) ho Sbelow hSbelow
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
    (hstageBlock :
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      C.succStageRestrictedBlockPrefixCompatible k Γ ho) :
    KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno o := by
  classical
  let topSegment : KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o :=
    KOneClusterPositiveFinalExternalNaturalSegment.limit
      (k := k) (Γ := Γ) ho Sbelow hSbelow hlimitBlock hstageBlock
  let segmentLimit :
      ∀ p : Set.Iic o,
        KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno p.1 := fun p =>
    if hp : p.1 < o then
      (Sbelow ⟨p.1, hp⟩).segment ⟨p.1, (show p.1 ≤ p.1 from le_rfl)⟩
    else
      have hp_eq : p.1 = o := le_antisymm p.2 (le_of_not_gt hp)
      hp_eq.symm ▸ topSegment
  have segment_lower :
      ∀ {p : Ordinal} (hp_le : p ≤ o) (hp_lt : p < o),
        segmentLimit ⟨p, hp_le⟩ =
          (Sbelow ⟨p, hp_lt⟩).segment ⟨p, (show p ≤ p from le_rfl)⟩ := by
    intro p hp_le hp_lt
    simp [segmentLimit, hp_lt]
  have segment_top :
      ∀ (hp : o ≤ o), segmentLimit ⟨o, hp⟩ = topSegment := by
    intro hp
    simp [segmentLimit]
  refine
    { segment := segmentLimit
      coherent := ?_ }
  intro p q hp hq
  by_cases hp_lt : p < o
  · have hq_lt : q < o := lt_of_le_of_lt hq hp_lt
    rw [segment_lower hp hp_lt, segment_lower (le_trans hq hp) hq_lt]
    calc
      (((Sbelow ⟨p, hp_lt⟩).segment ⟨p, (show p ≤ p from le_rfl)⟩).R ⟨q, hq⟩) =
          (((Sbelow ⟨p, hp_lt⟩).segment ⟨q, hq⟩).R
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        exact (Sbelow ⟨p, hp_lt⟩).coherent (show p ≤ p from le_rfl) hq
      _ = (((Sbelow ⟨q, hq_lt⟩).segment ⟨q, (show q ≤ q from le_rfl)⟩).R
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        rw [hSbelow hp_lt hq]
  · have hp_eq : p = o := le_antisymm hp (le_of_not_gt hp_lt)
    subst p
    by_cases hq_lt : q < o
    · rw [segment_top hp, segment_lower (le_trans hq hp) hq_lt]
      calc
        topSegment.R ⟨q, hq⟩ =
            (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
              (k := k) (Γ := Γ) Sbelow) ⟨q, hq_lt⟩ := by
          exact KOneClusterPositiveFinalExternalNaturalSegment.limit_R_lower
            (k := k) (Γ := Γ) ho Sbelow hSbelow
            hlimitBlock hstageBlock hq_lt hq
        _ = (((Sbelow ⟨q, hq_lt⟩).segment
              ⟨q, (show q ≤ q from le_rfl)⟩).R
              ⟨q, (show q ≤ q from le_rfl)⟩) := rfl
    · have hq_eq : q = o := le_antisymm hq (le_of_not_gt hq_lt)
      subst q
      rw [segment_top hp]

/-- Closed limit extension of a final natural initial segment system. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystem.limitClosed
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1)
    (hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩) :
    KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno o :=
  KOneClusterPositiveFinalExternalNaturalSegmentSystem.limit
    (k := k) (Γ := Γ) ho Sbelow hSbelow
    (by
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      let hpositive : C.succStageTopNextValProjectionCompatiblePositive k Γ ho :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_positiveProjection
          (k := k) (Γ := Γ) ho Sbelow hSbelow
      let hbotNext : C.succStageBotBlockNextValEq k Γ ho
          ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succStageBotBlockNextValEq
          (k := k) (Γ := Γ) ho Sbelow
      let hlimitBotNext :
          ∀ i : Set.Iio o, (i : Ordinal) = 0 →
            (C.limitBlock k Γ ho i).next.val k Γ =
              (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
                (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ :=
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_limitBlock_next_zero
          (k := k) (Γ := Γ) ho Sbelow hSbelow
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
      change C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep
      exact
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimitBlock
          (k := k) (Γ := Γ) ho Sbelow hSbelow hsep)
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hstageBlock
      (k := k) (Γ := Γ) ho Sbelow hSbelow)

@[simp] theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.limitClosed_segment_lower
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o p : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1)
    (hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩)
    (hp : p < o) :
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.limitClosed
      (k := k) (Γ := Γ) ho Sbelow hSbelow).segment
        ⟨p, le_of_lt hp⟩ =
      (Sbelow ⟨p, hp⟩).segment ⟨p, (show p ≤ p from le_rfl)⟩ := by
  unfold KOneClusterPositiveFinalExternalNaturalSegmentSystem.limitClosed
  unfold KOneClusterPositiveFinalExternalNaturalSegmentSystem.limit
  simp [hp]

end HahnField

end

end HahnKaplanskyRealClosedness
