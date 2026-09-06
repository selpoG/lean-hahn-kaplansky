/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaTail.CoreRoutes.Segment
import HahnKaplanskyRealClosedness.OmegaLimit.PositiveRecursion.Components

/-!
# Below-chain projections and compatibility fields
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

universe u v

namespace HahnField

variable (k : Type u) (Γ : Type v)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

open PositiveIioCoherentChainAt

/-- Limit-index restricted prefix from a natural-components limit step at the target index.

This is the non-circular form needed by the final segment recursion: the comparison uses the
actual natural limit value at `j`, not an arbitrary total `limitStep`. -/
theorem PositiveIioCoherentChainAtBelow.restrictedPrefix_of_limitIndex_of_naturalComponents
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩))
    {i j : Set.Iio o} (hij : i < j) (_hi : (0 : Ordinal) < i.1)
    (hj : Order.IsSuccLimit j.1)
    (hnatJ :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      Cj.NaturalComponents k Γ hj)
    (hsepJ :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      Cj.limitSeparated k Γ hj)
    (hlimitAt :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      C j = Cj.limitStepOfNaturalComponents k Γ hj hnatJ) :
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
      (let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
       (Cj.limitBlockChain k Γ hj hsepJ |>.restrictLT k Γ
        (⟨i.1, show i.1 < j.1 from hij⟩ : Set.Iio j.1)).diffHahnSeriesLimit k Γ) := by
  let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
  let ij : Set.Iio j.1 := ⟨i.1, show i.1 ∈ Set.Iio j.1 from hij⟩
  have hjpos : (0 : Ordinal) < j.1 := hj.bot_lt
  calc
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij
        =
      ((((C j) hjpos).succOfNoRoot k Γ hjpos hsmall hunit hno).toOneClusterBlockChain.restrictLT
        k Γ (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ := by
        unfold PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
        rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
          (k := k) (Γ := Γ) hsmall hunit hno ho C j
          (hsucc (ho.succ_lt j.2)) hjpos]
    _ =
      ((((C j) hjpos).succOfNoRoot k Γ hjpos hsmall hunit hno).toOneClusterBlockChain.restrictLT
        k Γ (ordinalIioSuccEmb j.1 ij)).diffHahnSeriesLimit k Γ := by
        rw [ordinalIioSuccTopEmbOfLt_eq_succEmb hij]
    _ =
      (letI : OrderBot (Set.Iio j.1) := ordinalIioOrderBotOfPos hjpos
       ((((C j) hjpos).toOneClusterBlockChain.restrictLT k Γ ij).diffHahnSeriesLimit k Γ)) := by
        exact PositiveIioCoherentChain.succOfNoRoot_restrictEmb_diffHahnSeriesLimit_of_limit
          k Γ hjpos hj hsmall hunit hno ((C j) hjpos) ij
    _ =
      (letI : OrderBot (Set.Iio j.1) := ordinalIioOrderBotOfPos hjpos
       (((Cj.limitStepOfNaturalComponents k Γ hj hnatJ) hjpos).toOneClusterBlockChain.restrictLT
          k Γ ij).diffHahnSeriesLimit k Γ) := by
        dsimp [Cj] at hlimitAt
        rw [hlimitAt]
    _ =
      (let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
       (Cj.limitBlockChain k Γ hj hsepJ |>.restrictLT k Γ ij)
        |>.diffHahnSeriesLimit k Γ) := by
        exact Cj.limitStepOfNaturalComponents_restrictLT_sep k Γ hj hnatJ hsepJ hjpos ij

/-- Successor-limit predecessor branch from a natural-components limit step at the predecessor.

This is the successor-index analogue of
`restrictedPrefix_of_limitIndex_of_naturalComponents`; it avoids introducing an arbitrary total
`limitStep` for the lower limit predecessor. -/
theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefix_pred_of_succLimitIndex_natural
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩))
    {p : Ordinal} {hp : Order.succ p < o} (hplim : Order.IsSuccLimit p)
    (hnatP :
      let Cp : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans ((Order.lt_succ p).trans hp))⟩
      Cp.NaturalComponents k Γ hplim)
    (hsepP :
      let Cp : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans ((Order.lt_succ p).trans hp))⟩
      Cp.limitSeparated k Γ hplim)
    (hlimitAt :
      let pidx : Set.Iio o := ⟨p, (Order.lt_succ p).trans hp⟩
      let Cp : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans pidx.2)⟩
      C pidx = Cp.limitStepOfNaturalComponents k Γ hplim hnatP)
    (hlimitPrefix :
      let Cp : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans ((Order.lt_succ p).trans hp))⟩
      Cp.limitPrefixCompatibleWithSuccStage k Γ hplim hsepP)
    (hstagePrefix :
      let Cp : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans ((Order.lt_succ p).trans hp))⟩
      Cp.succStageRestrictedPrefixCompatible k Γ hplim)
    {i : Set.Iio o} (hi : i.1 < p) :
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
        exact hi.trans (Order.lt_succ p)) =
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let pidx : Set.Iio o := ⟨p, (Order.lt_succ p).trans hp⟩
  let hij : i < (⟨Order.succ p, hp⟩ : Set.Iio o) := by
    change i.1 < Order.succ p
    exact hi.trans (Order.lt_succ p)
  let hip : i < pidx := by
    change i.1 < p
    exact hi
  by_cases hizero : (i : Ordinal) = 0
  · exact C.succStageRestrictedPrefixCompatible_bot k Γ ho hij hizero
  have hipos : (0 : Ordinal) < i.1 := lt_of_le_of_ne bot_le (Ne.symm hizero)
  let Cp : PositiveIioCoherentChainAtBelow k Γ p F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans pidx.2)⟩
  let ipSucc : Set.Iio (Order.succ p) := ⟨i.1, hi.trans (Order.lt_succ p)⟩
  let ip : Set.Iio p := ⟨i.1, hi⟩
  have hjpos : (0 : Ordinal) < (Order.succ p) := by
    exact (lt_of_le_of_lt bot_le hi).trans (Order.lt_succ p)
  unfold PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
  calc
    (((C.succStageChain k Γ ho (⟨Order.succ p, hp⟩ : Set.Iio o)).toOneClusterBlockChain.restrictLT
        k Γ (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ)
        =
      (((C.succStageChain k Γ ho (⟨Order.succ p, hp⟩ : Set.Iio o)).toOneClusterBlockChain.restrictLT
        k Γ (ordinalIioSuccEmb (Order.succ p) ipSucc)).diffHahnSeriesLimit k Γ) := by
        exact OneClusterBlockChain.restrictLT_diffHahnSeriesLimit_congr k Γ _
          (ordinalIioSuccTopEmbOfLt_eq_succEmb hij)
    _ =
      ((((C ⟨Order.succ p, hp⟩) hjpos).toOneClusterBlockChain.restrictLT k Γ ipSucc)
        |>.diffHahnSeriesLimit k Γ) := by
        rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
          (k := k) (Γ := Γ) hsmall hunit hno ho C
          (⟨Order.succ p, hp⟩ : Set.Iio o)
          (hsucc (ho.succ_lt hp)) hjpos]
        exact PositiveIioCoherentChain.succOfNoRoot_restrictEmb_diffHahnSeriesLimit_of_succ
          (k := k) (Γ := Γ) hsmall hunit hno ((C ⟨Order.succ p, hp⟩) hjpos) ipSucc
    _ =
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hip := by
        have hchain :
            (C ⟨Order.succ p, hp⟩) hjpos = C.succStageChain k Γ ho pidx := by
          calc
            (C ⟨Order.succ p, hp⟩) hjpos =
                (PositiveIioCoherentChainAt.succOfNoRoot
                  k Γ hsmall hunit hno (C pidx)) hjpos := by
                  exact congrFun (hsucc hp) hjpos
            _ = ((C pidx) hplim.bot_lt).succOfNoRoot
                  k Γ hplim.bot_lt hsmall hunit hno := by
                  exact PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
                    k Γ hsmall hunit hno (C pidx) hplim.bot_lt hjpos
            _ = C.succStageChain k Γ ho pidx := by
                  exact (PositiveIioCoherentChainAtBelow.succStageChain_of_pos
                    (k := k) (Γ := Γ) hsmall hunit hno ho C pidx
                    (hsucc hp) hplim.bot_lt).symm
        rw [hchain]
        unfold PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
        exact OneClusterBlockChain.restrictLT_diffHahnSeriesLimit_congr k Γ _
          (by rfl)
    _ =
      (Cp.limitBlockChain k Γ hplim hsepP |>.restrictLT k Γ ip).diffHahnSeriesLimit k Γ := by
        exact C.restrictedPrefix_of_limitIndex_of_naturalComponents
          k Γ hsmall hunit hno ho hsucc hip hipos hplim hnatP hsepP hlimitAt
    _ = C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
        exact C.stageLimit_of_prefixFields k Γ ho hip hipos hplim hsepP
          hlimitPrefix hstagePrefix

/-- Limit-predecessor branch of the successor-index stage comparison for the below-chain extracted
from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_pred_limit
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
    {p : Ordinal} {hp : Order.succ p < o} (hplim : Order.IsSuccLimit p)
    {i : Set.Iio o} (hi : i.1 < p) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
        exact hi.trans (Order.lt_succ p)) =
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let pidx : Set.Iio o := ⟨p, (Order.lt_succ p).trans hp⟩
  let Cp : PositiveIioCoherentChainAtBelow k Γ p F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans pidx.2)⟩
  let hnatP : Cp.NaturalComponents k Γ hplim :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
      (k := k) (Γ := Γ) Sbelow hSbelow pidx hplim
  let hsepP : Cp.limitSeparated k Γ hplim :=
    Cp.naturalComponentsSeparated k Γ hplim hnatP
  have hlimitAt : C pidx = Cp.limitStepOfNaturalComponents k Γ hplim hnatP :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimit
      (k := k) (Γ := Γ) Sbelow hSbelow pidx hplim
  change C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
        exact hi.trans (Order.lt_succ p)) =
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  exact C.succStageRestrictedPrefix_pred_of_succLimitIndex_natural
    k Γ hsmall hunit hno ho
    (fun {q} hq =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
        (k := k) (Γ := Γ) Sbelow hSbelow hq)
    hplim hnatP hsepP hlimitAt
    (Cp.limitPrefixCompatibleWithSuccStage_of_naturalComponents k Γ hplim hnatP)
    (Cp.succStageRestrictedPrefixCompatible_of_naturalComponents k Γ hplim hnatP)
    hi

/-- Pred branch of the successor-index stage comparison for the below-chain extracted from
coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_pred
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o} (hi : i.1 < p),
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
        (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
          exact hi.trans (Order.lt_succ p)) =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let P : Ordinal → Prop := fun p =>
    ∀ {hp : Order.succ p < o} {i : Set.Iio o} (hi : i.1 < p),
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
        (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
          exact hi.trans (Order.lt_succ p)) =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  dsimp only
  intro p
  change P p
  induction p using Ordinal.limitRecOn with
  | zero =>
      intro _hp i hi
      exact False.elim ((not_lt_of_ge (bot_le : (0 : Ordinal) ≤ i.1)) hi)
  | add_one q ih =>
      intro hp i hi
      rcases ordinal_lt_succ_eq_or_lt (show i.1 < Order.succ q from hi) with htop | hlt
      · exact C.succStageRestrictedPrefix_top_of_succSuccIndex
          k Γ hsmall hunit hno ho
          (fun {p} hp =>
            KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
              (k := k) (Γ := Γ) Sbelow hSbelow hp)
          (q := q) (hp := hp) htop
      · exact
          KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_pred_succ
            (k := k) (Γ := Γ) ho Sbelow hSbelow (q := q) (hp := hp)
            (fun {i} hiq =>
              ih (hp := (Order.lt_succ (Order.succ q)).trans hp) (i := i) hiq)
            hlt
  | limit p hplim _ih =>
      intro hp i hi
      exact
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_pred_limit
          (k := k) (Γ := Γ) ho Sbelow hSbelow
          (p := p) (hp := hp) hplim hi

/-- Successor-index stage branch for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hstageSucc
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
      j.1 ∈ Set.range Order.succ →
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
          C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
      j.1 ∈ Set.range Order.succ →
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
          C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  intro i j hij _hi hjsucc
  exact C.succStageRestrictedPrefixCompatible_of_succPositiveBranches k Γ ho
    (fun {p} {hp} {i} hi _hpos =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_top
        (k := k) (Γ := Γ) ho Sbelow hSbelow (p := p) (hp := hp) hi)
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_pred
      (k := k) (Γ := Γ) ho Sbelow hSbelow)
    hij hjsucc

/-- Limit-index stage branch for the below-chain extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hstageTarget
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
      Order.IsSuccLimit j.1 →
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
          C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
      Order.IsSuccLimit j.1 →
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
          C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  intro i j hij hi hjlim
  let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
  let hnatJ : Cj.NaturalComponents k Γ hjlim :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
      (k := k) (Γ := Γ) Sbelow hSbelow j hjlim
  let hsepJ : Cj.limitSeparated k Γ hjlim :=
    Cj.naturalComponentsSeparated k Γ hjlim hnatJ
  have hlimitAt :
      C j = Cj.limitStepOfNaturalComponents k Γ hjlim hnatJ :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimit
      (k := k) (Γ := Γ) Sbelow hSbelow j hjlim
  have hrestricted :
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
        (Cj.limitBlockChain k Γ hjlim hsepJ |>.restrictLT k Γ
          (⟨i.1, show i.1 < j.1 from hij⟩ : Set.Iio j.1)).diffHahnSeriesLimit k Γ := by
    exact C.restrictedPrefix_of_limitIndex_of_naturalComponents
      k Γ hsmall hunit hno ho
      (fun {q} hq =>
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
          (k := k) (Γ := Γ) Sbelow hSbelow hq)
      hij hi hjlim hnatJ hsepJ hlimitAt
  have hstageLimit :
      (Cj.limitBlockChain k Γ hjlim hsepJ |>.restrictLT k Γ
          (⟨i.1, show i.1 < j.1 from hij⟩ : Set.Iio j.1)).diffHahnSeriesLimit k Γ =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
    exact C.stageLimit_of_prefixFields k Γ ho hij hi hjlim hsepJ
      (Cj.limitPrefixCompatibleWithSuccStage_of_naturalComponents k Γ hjlim hnatJ)
      (Cj.succStageRestrictedPrefixCompatible_of_naturalComponents k Γ hjlim hnatJ)
  exact hrestricted.trans hstageLimit

/-- Stage prefix compatibility for the below-chain extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hstage
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.succStageRestrictedPrefixCompatible k Γ ho := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change C.succStageRestrictedPrefixCompatible k Γ ho
  exact C.succStageRestrictedPrefixCompatible_of_targetBranches k Γ ho
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hstageTarget
      (k := k) (Γ := Γ) ho Sbelow hSbelow)
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hstageSucc
      (k := k) (Γ := Γ) ho Sbelow hSbelow)

/-- Stage block-prefix compatibility for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hstageBlock
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.succStageRestrictedBlockPrefixCompatible k Γ ho := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change C.succStageRestrictedBlockPrefixCompatible k Γ ho
  exact C.succStageRestrictedBlockPrefixCompatible_of_prefix k Γ ho
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hstage
      (k := k) (Γ := Γ) ho Sbelow hSbelow)

/-- Nested limit blocks agree for the below-chain extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_nestedLimitBlockDiff
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
    {j : Set.Iio o} (hj : Order.IsSuccLimit j.1) (i : Set.Iio j.1) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
      fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
    (Cj.limitBlock k Γ hj i).diffHahnSeries k Γ =
      (C.limitBlock k Γ ho
        (⟨i.1, show i.1 < o from i.2.trans j.2⟩ : Set.Iio o)).diffHahnSeries k Γ := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
  let hsuccC :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩) :=
    fun {p} hp =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
        (k := k) (Γ := Γ) Sbelow hSbelow hp
  let hsuccJ :
      ∀ {p : Ordinal} (hp : Order.succ p < j.1),
        Cj ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (Cj ⟨p, (Order.lt_succ p).trans hp⟩) := by
    intro p hp
    exact hsuccC (show Order.succ p < o from hp.trans j.2)
  change
    (Cj.limitBlock k Γ hj i).diffHahnSeries k Γ =
      (C.limitBlock k Γ ho
        (⟨i.1, show i.1 < o from i.2.trans j.2⟩ : Set.Iio o)).diffHahnSeries k Γ
  rcases eq_or_lt_of_le (bot_le : (0 : Ordinal) ≤ i.1) with hizero | hpos
  · have hi0 : i = (⟨0, hj.bot_lt⟩ : Set.Iio j.1) := by
      apply Subtype.ext
      exact hizero.symm
    subst i
    calc
      (Cj.limitBlock k Γ hj (⟨0, hj.bot_lt⟩ : Set.Iio j.1)).diffHahnSeries k Γ =
          (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ := by
          exact Cj.limitBlock_bot_diffHahnSeries_of_succ k Γ hj hsuccJ
      _ = (C.limitBlock k Γ ho
          (⟨0, show (0 : Ordinal) < o from hj.bot_lt.trans j.2⟩ : Set.Iio o)
          ).diffHahnSeries k Γ := by
          exact (C.limitBlock_bot_diffHahnSeries_of_succ k Γ ho hsuccC).symm
  · calc
      (Cj.limitBlock k Γ hj i).diffHahnSeries k Γ =
          (((((Cj i) hpos).succOfNoRoot k Γ hpos hsmall hunit hno).succEndpointTopBlock
            k Γ).diffHahnSeries k Γ) := by
          exact Cj.limitBlock_diffHahnSeries_of_pos_of_succ k Γ hj hsuccJ i hpos
      _ = (((((C (⟨i.1, show i.1 < o from i.2.trans j.2⟩ : Set.Iio o)) hpos).succOfNoRoot
            k Γ hpos hsmall hunit hno).succEndpointTopBlock k Γ).diffHahnSeries k Γ) := by
          rfl
      _ = (C.limitBlock k Γ ho
          (⟨i.1, show i.1 < o from i.2.trans j.2⟩ : Set.Iio o)
          ).diffHahnSeries k Γ := by
          exact (C.limitBlock_diffHahnSeries_of_pos_of_succ k Γ ho hsuccC
            (⟨i.1, show i.1 < o from i.2.trans j.2⟩ : Set.Iio o) hpos).symm

/-- Limit-index limit-prefix branch for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimitTarget
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
    (hsep :
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow).limitSeparated k Γ ho) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {i j : Set.Iio o} (hij : i < j), Order.IsSuccLimit j.1 →
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change ∀ {i j : Set.Iio o} (hij : i < j), Order.IsSuccLimit j.1 →
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij
  intro i j hij hjlim
  let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
  let ij : Set.Iio j.1 := ⟨i.1, show i.1 < j.1 from hij⟩
  let hnatJ : Cj.NaturalComponents k Γ hjlim :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
      (k := k) (Γ := Γ) Sbelow hSbelow j hjlim
  let hsepJ : Cj.limitSeparated k Γ hjlim :=
    Cj.naturalComponentsSeparated k Γ hjlim hnatJ
  rcases eq_or_lt_of_le (bot_le : (0 : Ordinal) ≤ i.1) with hizero | hi
  · rw [C.limitPrefixDiffHahnSeriesLimit_eq_zero k Γ ho hsep i hizero.symm]
    exact (C.succStageRestrictedPrefixDiffHahnSeriesLimit_eq_zero
      k Γ ho hij hizero.symm).symm
  let B := C.limitBlockChain k Γ ho hsep
  let Bj := Cj.limitBlockChain k Γ hjlim hsepJ
  have hlimitAt :
      C j = Cj.limitStepOfNaturalComponents k Γ hjlim hnatJ :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimit
      (k := k) (Γ := Γ) Sbelow hSbelow j hjlim
  have houter :
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ := by
    change (B.restrictLT k Γ i).diffHahnSeriesLimit k Γ =
      (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ
    exact (B.restrictLTOrdinal_diffHahnSeriesLimit k Γ i).symm
  have hinner :
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
        (Bj.restrictLTOrdinal k Γ ij).diffHahnSeriesLimit k Γ := by
    calc
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
          (Bj.restrictLT k Γ ij).diffHahnSeriesLimit k Γ := by
          exact C.restrictedPrefix_of_limitIndex_of_naturalComponents
            k Γ hsmall hunit hno ho
            (fun {q} hq =>
              KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
                (k := k) (Γ := Γ) Sbelow hSbelow hq)
            hij hi hjlim hnatJ hsepJ hlimitAt
      _ = (Bj.restrictLTOrdinal k Γ ij).diffHahnSeriesLimit k Γ := by
          exact (Bj.restrictLTOrdinal_diffHahnSeriesLimit k Γ ij).symm
  have hblocks :
      (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ =
        (Bj.restrictLTOrdinal k Γ ij).diffHahnSeriesLimit k Γ := by
    apply OneClusterBlockChain.diffHahnSeriesLimit_congr
    intro l
    dsimp [B, Bj, OneClusterBlockChain.restrictLTOrdinal]
    exact
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_nestedLimitBlockDiff
        (k := k) (Γ := Γ) ho Sbelow hSbelow hjlim
        (((ordinalIioSubtypeIioEquiv ij).symm l).1)).symm
  calc
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ := houter
    _ = (Bj.restrictLTOrdinal k Γ ij).diffHahnSeriesLimit k Γ := hblocks
    _ = C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij := hinner.symm

/-- Successor-index stage prefix for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stagePrefix_succ
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
    {p : Ordinal} {hp : Order.succ p < o} :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho (⟨Order.succ p, hp⟩ : Set.Iio o) =
      (((C (⟨Order.succ p, hp⟩ : Set.Iio o))
        (lt_of_le_of_lt bot_le (Order.lt_succ p))).toOneClusterBlockChain
          |>.diffHahnSeriesLimit k Γ) := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let i : Set.Iio o := ⟨Order.succ p, hp⟩
  let hi : (0 : Ordinal) < i.1 := lt_of_le_of_lt bot_le (Order.lt_succ p)
  change C.succStagePrefixDiffHahnSeriesLimit k Γ ho i =
    ((C i hi).toOneClusterBlockChain.diffHahnSeriesLimit k Γ)
  unfold PositiveIioCoherentChainAtBelow.succStagePrefixDiffHahnSeriesLimit
  rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
    (k := k) (Γ := Γ) hsmall hunit hno ho C i
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
      (k := k) (Γ := Γ) Sbelow hSbelow (ho.succ_lt i.2))
    hi]
  exact PositiveIioCoherentChain.succOfNoRoot_restrictTop_diffHahnSeriesLimit_of_succ
    (k := k) (Γ := Γ) hsmall hunit hno (C i hi)

/-- Zero-predecessor branch of the successor-index stage-top comparison for the below-chain
extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_lprefixSucc_zero
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
    (hsep :
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow).limitSeparated k Γ ho) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep
        (⟨Order.succ (0 : Ordinal.{v}), ho.succ_lt ho.bot_lt⟩ : Set.Iio o) =
      (((C (⟨Order.succ (0 : Ordinal.{v}), ho.succ_lt ho.bot_lt⟩ : Set.Iio o))
        (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal.{v})))).toOneClusterBlockChain
          |>.diffHahnSeriesLimit k Γ) := by
  classical
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let B := C.limitBlockChain k Γ ho hsep
  let i : Set.Iio o := ⟨Order.succ (0 : Ordinal.{v}), ho.succ_lt ho.bot_lt⟩
  let hi : (0 : Ordinal.{v}) < i.1 :=
    lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal.{v}))
  let I0 : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (0 : Ordinal.{v}))) F :=
    OneClusterCoherentBlockChain.initialOfNoRoot.{v} (F := F) k Γ hsmall hunit hno
  have hsuccC :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩) :=
    fun {p} hp =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
        (k := k) (Γ := Γ) Sbelow hSbelow hp
  have hleft :
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ := by
    change (B.restrictLT k Γ i).diffHahnSeriesLimit k Γ =
      (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ
    exact (B.restrictLTOrdinal_diffHahnSeriesLimit k Γ i).symm
  have hblocks :
      (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ =
        I0.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
    have : Subsingleton (Set.Iio i.1) := by
      dsimp [i]
      exact ordinalIioSuccZero_subsingleton
    apply OneClusterBlockChain.diffHahnSeriesLimit_congr
    intro l
    have hl : l = (ordinalIioSuccOrderTop (0 : Ordinal.{v})).top := Subsingleton.elim _ _
    subst l
    dsimp [B, I0, OneClusterBlockChain.restrictLTOrdinal]
    calc
      (C.limitBlock k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o)).diffHahnSeries k Γ =
          (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
            (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ := by
          exact C.limitBlock_bot_diffHahnSeries_of_succ k Γ ho hsuccC
      _ =
          ((OneClusterCoherentBlockChain.initialOfNoRoot.{v} (F := F) k Γ hsmall hunit hno)
            |>.toOneClusterBlockChain.topBlock k Γ).diffHahnSeries k Γ := by
          unfold OneClusterCoherentBlockChain.initialOfNoRoot
          change
            (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
              (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ =
            (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
              (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ
          rfl
  have hright :
      (((C i hi).toOneClusterBlockChain).diffHahnSeriesLimit k Γ) =
        I0.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
    dsimp [i]
    have hchain :
        C ⟨Order.succ (0 : Ordinal.{v}), ho.succ_lt ho.bot_lt⟩ hi =
          (PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C (⟨0, ho.bot_lt⟩ : Set.Iio o))) hi := by
      exact congrArg (fun X : PositiveIioCoherentChainAt k Γ (Order.succ (0 : Ordinal.{v})) F =>
        X hi) (hsuccC (ho.succ_lt ho.bot_lt))
    calc
      ((C ⟨Order.succ (0 : Ordinal.{v}), ho.succ_lt ho.bot_lt⟩ hi)
          |>.toOneClusterBlockChain).diffHahnSeriesLimit k Γ =
        (((PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C (⟨0, ho.bot_lt⟩ : Set.Iio o))) hi)
          |>.toOneClusterBlockChain).diffHahnSeriesLimit k Γ := by
          rw [hchain]
      _ = I0.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
          exact congrArg
            (fun D : PositiveIioCoherentChain k Γ (Order.succ (0 : Ordinal.{v})) hi F =>
              D.toOneClusterBlockChain.diffHahnSeriesLimit k Γ)
            (PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
              (F := F) k Γ hsmall hunit hno
              (C (⟨0, ho.bot_lt⟩ : Set.Iio o)) hi)
  calc
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ := hleft
    _ = I0.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := hblocks
    _ = (((C i hi).toOneClusterBlockChain).diffHahnSeriesLimit k Γ) := hright.symm

/-- Successor-predecessor branch of the successor-index stage-top comparison for the below-chain
extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_lprefixSucc_stageTop
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
    (hsep :
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow).limitSeparated k Γ ho)
    {p : Ordinal.{v}} {hp : Order.succ p < o} (hposp : (0 : Ordinal.{v}) < p)
    (hstageTopPred :
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep
          (⟨p, (Order.lt_succ p).trans hp⟩ : Set.Iio o) =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho
          (⟨p, (Order.lt_succ p).trans hp⟩ : Set.Iio o)) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep (⟨Order.succ p, hp⟩ : Set.Iio o) =
      (((C (⟨Order.succ p, hp⟩ : Set.Iio o))
        (lt_of_le_of_lt bot_le (Order.lt_succ p))).toOneClusterBlockChain
          |>.diffHahnSeriesLimit k Γ) := by
  classical
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let B := C.limitBlockChain k Γ ho hsep
  let i : Set.Iio o := ⟨Order.succ p, hp⟩
  let pidx : Set.Iio o := ⟨p, (Order.lt_succ p).trans hp⟩
  let hi : (0 : Ordinal) < i.1 := lt_of_le_of_lt bot_le (Order.lt_succ p)
  let hpidx : (0 : Ordinal) < pidx.1 := hposp
  have hleft_decomp :
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep pidx +
          (C.limitBlock k Γ ho pidx).diffHahnSeries k Γ := by
    unfold PositiveIioCoherentChainAtBelow.limitPrefixDiffHahnSeriesLimit
    calc
      ((B.restrictLT k Γ i).diffHahnSeriesLimit k Γ)
          =
        ((B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ) := by
          exact (B.restrictLTOrdinal_diffHahnSeriesLimit k Γ i).symm
      _ =
        (((B.restrictLTOrdinal k Γ i).restrictLT k Γ
            (ordinalIioSuccOrderTop p).top).diffHahnSeriesLimit k Γ) +
          ((B.restrictLTOrdinal k Γ i).topBlock k Γ).diffHahnSeries k Γ := by
          exact OneClusterBlockChain.diffHahnSeriesLimit_eq_restrictTop_add_topBlock
            k Γ (B.restrictLTOrdinal k Γ i)
      _ =
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep pidx +
          (C.limitBlock k Γ ho pidx).diffHahnSeries k Γ := by
          congr 1
          · change (((B.restrictLTOrdinal k Γ i).restrictLT k Γ
                (ordinalIioSuccOrderTop p).top).diffHahnSeriesLimit k Γ) =
              ((B.restrictLT k Γ pidx).diffHahnSeriesLimit k Γ)
            let topi : Set.Iio i.1 := (ordinalIioSuccOrderTop p).top
            let R := (B.restrictLTOrdinal k Γ i).restrictLT k Γ topi
            let P := B.restrictLT k Γ pidx
            let E : Set.Iio pidx ≃ Set.Iio topi :=
              { toFun := fun l =>
                  ⟨⟨l.1.1, (show l.1.1 < p from l.2).trans (Order.lt_succ p)⟩,
                    show (⟨l.1.1,
                      (show l.1.1 < p from l.2).trans (Order.lt_succ p)⟩ :
                      Set.Iio (Order.succ p)) < topi from l.2⟩
                invFun := fun l =>
                  ⟨⟨l.1.1, (show l.1.1 < p from l.2).trans pidx.2⟩,
                    show (⟨l.1.1, (show l.1.1 < p from l.2).trans pidx.2⟩ :
                      Set.Iio o) < pidx from l.2⟩
                left_inv := by
                  intro l
                  rfl
                right_inv := by
                  intro l
                  rfl }
            let sR := R.diffSummableFamily k Γ
            let sP := P.diffSummableFamily k Γ
            have heq : sR = HahnSeries.SummableFamily.Equiv E sP := by
              ext l γ
              dsimp [HahnSeries.SummableFamily.Equiv, sR, sP, R, P, E,
                OneClusterBlockChain.diffSummableFamily,
                OneClusterBlockChain.restrictLTOrdinal]
              rfl
            change sR.hsum = sP.hsum
            rw [heq, HahnSeries.SummableFamily.hsum_equiv]
  have hright_decomp :
      (((C i hi).toOneClusterBlockChain).diffHahnSeriesLimit k Γ) =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho pidx +
          (C.limitBlock k Γ ho pidx).diffHahnSeries k Γ := by
    calc
      (((C i hi).toOneClusterBlockChain).diffHahnSeriesLimit k Γ)
          =
        ((C.succStageChain k Γ ho pidx).toOneClusterBlockChain.diffHahnSeriesLimit k Γ) := by
          rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
            (k := k) (Γ := Γ) hsmall hunit hno ho C pidx
            (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
              (k := k) (Γ := Γ) Sbelow hSbelow (ho.succ_lt pidx.2))
            hpidx]
          let hchain :
              C i hi =
                ((C pidx) hpidx).succOfNoRoot k Γ hpidx hsmall hunit hno := by
            calc
              C i hi =
                  (PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
                    (C pidx)) hi := by
                    exact congrArg
                      (fun X : PositiveIioCoherentChainAt k Γ (Order.succ p) F => X hi)
                      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
                        (k := k) (Γ := Γ) Sbelow hSbelow hp)
              _ = ((C pidx) hpidx).succOfNoRoot k Γ hpidx hsmall hunit hno := by
                    exact PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
                      k Γ hsmall hunit hno (C pidx) hpidx hi
          rw [hchain]
      _ =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho pidx +
          ((C.succStageChain k Γ ho pidx).succEndpointTopBlock k Γ).diffHahnSeries k Γ := by
          exact OneClusterBlockChain.diffHahnSeriesLimit_eq_restrictTop_add_topBlock
            k Γ (C.succStageChain k Γ ho pidx).toOneClusterBlockChain
      _ =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho pidx +
          (C.limitBlock k Γ ho pidx).diffHahnSeries k Γ := by
          rfl
  calc
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep pidx +
          (C.limitBlock k Γ ho pidx).diffHahnSeries k Γ := hleft_decomp
    _ = C.succStagePrefixDiffHahnSeriesLimit k Γ ho pidx +
          (C.limitBlock k Γ ho pidx).diffHahnSeries k Γ := by
          rw [hstageTopPred]
    _ = (((C i hi).toOneClusterBlockChain).diffHahnSeriesLimit k Γ) := hright_decomp.symm

/-- Limit-index stage-top equality for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageTopLimit
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
    (hsep :
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow).limitSeparated k Γ ho) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {i : Set.Iio o}, (0 : Ordinal) < i.1 → Order.IsSuccLimit i.1 →
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change ∀ {i : Set.Iio o}, (0 : Ordinal) < i.1 → Order.IsSuccLimit i.1 →
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  intro i hi hilim
  let Ci : PositiveIioCoherentChainAtBelow k Γ i.1 F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans i.2)⟩
  let hnatI : Ci.NaturalComponents k Γ hilim :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
      (k := k) (Γ := Γ) Sbelow hSbelow i hilim
  let hsepI : Ci.limitSeparated k Γ hilim :=
    Ci.naturalComponentsSeparated k Γ hilim hnatI
  let B := C.limitBlockChain k Γ ho hsep
  let Bi := Ci.limitBlockChain k Γ hilim hsepI
  have houter :
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ := by
    change (B.restrictLT k Γ i).diffHahnSeriesLimit k Γ =
      (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ
    exact (B.restrictLTOrdinal_diffHahnSeriesLimit k Γ i).symm
  have hblocks :
      (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ =
        Bi.diffHahnSeriesLimit k Γ := by
    apply OneClusterBlockChain.diffHahnSeriesLimit_congr
    intro l
    dsimp [B, Bi, OneClusterBlockChain.restrictLTOrdinal]
    exact
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_nestedLimitBlockDiff
        (k := k) (Γ := Γ) ho Sbelow hSbelow hilim l).symm
  have hinner :
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i =
        (letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
         ((C i) hi).toOneClusterBlockChain.diffHahnSeriesLimit k Γ) := by
    unfold PositiveIioCoherentChainAtBelow.succStagePrefixDiffHahnSeriesLimit
    rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
      (k := k) (Γ := Γ) hsmall hunit hno ho C
      i
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
        (k := k) (Γ := Γ) Sbelow hSbelow (ho.succ_lt i.2))
      hi]
    exact PositiveIioCoherentChain.succOfNoRoot_restrictTop_diffHahnSeriesLimit_of_limit
      k Γ hi hilim hsmall hunit hno (C i hi)
  have hfull :
      (letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
       ((C i) hi).toOneClusterBlockChain.diffHahnSeriesLimit k Γ) =
        Bi.diffHahnSeriesLimit k Γ := by
    have hlimitI :
        C i = Ci.limitStepOfNaturalComponents k Γ hilim hnatI :=
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimit
        (k := k) (Γ := Γ) Sbelow hSbelow i hilim
    calc
      (letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
       ((C i) hi).toOneClusterBlockChain.diffHahnSeriesLimit k Γ) =
          (letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
           ((Ci.limitStepOfNaturalComponents k Γ hilim hnatI) hi).toOneClusterBlockChain
              |>.diffHahnSeriesLimit k Γ) := by
            rw [hlimitI]
      _ = Bi.diffHahnSeriesLimit k Γ := by
          exact Ci.limitStepOfNaturalComponents_diffHahnSeriesLimit_sep
            k Γ hilim hnatI hsepI hi
  calc
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        (B.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ := houter
    _ = Bi.diffHahnSeriesLimit k Γ := hblocks
    _ =
        (letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
         ((C i) hi).toOneClusterBlockChain.diffHahnSeriesLimit k Γ) := hfull.symm
    _ = C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := hinner.symm

/-- Successor-index stage-top equality for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageTopSucc
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
    (hsep :
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow).limitSeparated k Γ ho) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {i : Set.Iio o}, (0 : Ordinal) < i.1 → i.1 ∈ Set.range Order.succ →
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  classical
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let P : Ordinal.{v} → Prop := fun p =>
    ∀ {hp : Order.succ p < o},
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep
          (⟨Order.succ p, hp⟩ : Set.Iio o) =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho (⟨Order.succ p, hp⟩ : Set.Iio o)
  have hP : ∀ p, P p := by
    intro p
    induction p using Ordinal.limitRecOn with
    | zero =>
        intro hp
        calc
          C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep
              (⟨Order.succ (0 : Ordinal.{v}), hp⟩ : Set.Iio o) =
            (((C (⟨Order.succ (0 : Ordinal.{v}), hp⟩ : Set.Iio o))
              (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal.{v})))).toOneClusterBlockChain
                |>.diffHahnSeriesLimit k Γ) := by
              have hhp : hp = ho.succ_lt ho.bot_lt := Subsingleton.elim _ _
              subst hhp
              exact belowChain_lprefixSucc_zero
                (k := k) (Γ := Γ) ho Sbelow hSbelow hsep
          _ = C.succStagePrefixDiffHahnSeriesLimit k Γ ho
              (⟨Order.succ (0 : Ordinal.{v}), hp⟩ : Set.Iio o) := by
              exact (belowChain_stagePrefix_succ
                (k := k) (Γ := Γ) ho Sbelow hSbelow (p := 0) (hp := hp)).symm
    | add_one q ih =>
        intro hp
        let hq : Order.succ q < o := (Order.lt_succ (Order.succ q)).trans hp
        have hstageTopPred : C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep
              (⟨Order.succ q, hq⟩ : Set.Iio o) =
            C.succStagePrefixDiffHahnSeriesLimit k Γ ho
              (⟨Order.succ q, hq⟩ : Set.Iio o) := ih (hp := hq)
        calc
          C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep
              (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o) =
            (((C (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o))
              (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ q)))).toOneClusterBlockChain
                |>.diffHahnSeriesLimit k Γ) := by
              exact belowChain_lprefixSucc_stageTop
                (k := k) (Γ := Γ) ho Sbelow hSbelow hsep
                (p := Order.succ q) (hp := hp)
                (lt_of_le_of_lt bot_le (Order.lt_succ q))
                hstageTopPred
          _ = C.succStagePrefixDiffHahnSeriesLimit k Γ ho
              (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o) := by
              exact (belowChain_stagePrefix_succ
                (k := k) (Γ := Γ) ho Sbelow hSbelow
                (p := Order.succ q) (hp := hp)).symm
    | limit p hplim _ih =>
        intro hp
        let pidx : Set.Iio o := ⟨p, (Order.lt_succ p).trans hp⟩
        have hstageTopPred :
            C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep pidx =
              C.succStagePrefixDiffHahnSeriesLimit k Γ ho pidx :=
          KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageTopLimit
            (k := k) (Γ := Γ) ho Sbelow hSbelow hsep hplim.bot_lt hplim
        calc
          C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep
              (⟨Order.succ p, hp⟩ : Set.Iio o) =
            (((C (⟨Order.succ p, hp⟩ : Set.Iio o))
              (lt_of_le_of_lt bot_le (Order.lt_succ p))).toOneClusterBlockChain
                |>.diffHahnSeriesLimit k Γ) := by
              exact belowChain_lprefixSucc_stageTop
                (k := k) (Γ := Γ) ho Sbelow hSbelow hsep
                (p := p) (hp := hp) hplim.bot_lt hstageTopPred
          _ = C.succStagePrefixDiffHahnSeriesLimit k Γ ho
              (⟨Order.succ p, hp⟩ : Set.Iio o) := by
              exact (belowChain_stagePrefix_succ
                (k := k) (Γ := Γ) ho Sbelow hSbelow (p := p) (hp := hp)).symm
  change ∀ {i : Set.Iio o}, (0 : Ordinal) < i.1 → i.1 ∈ Set.range Order.succ →
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  intro i _hi hisucc
  rcases hisucc with ⟨p, hp⟩
  let hp' : Order.succ p < o := by
    rw [hp]
    exact i.2
  have hidx : (⟨Order.succ p, hp'⟩ : Set.Iio o) = i := by
    ext
    exact hp
  rw [← hidx]
  exact hP p (hp := hp')

/-- Stage-top equality for the below-chain extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageTop
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
    (hsep :
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow).limitSeparated k Γ ho) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {i : Set.Iio o}, (0 : Ordinal) < i.1 →
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change ∀ {i : Set.Iio o}, (0 : Ordinal) < i.1 →
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  intro i hi
  rcases Ordinal.zero_or_succ_or_isSuccLimit i.1 with hizero | hisucc | hilim
  · rw [hizero] at hi
    exact False.elim ((lt_irrefl (0 : Ordinal)) hi)
  · exact
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageTopSucc
        (k := k) (Γ := Γ) ho Sbelow hSbelow hsep hi hisucc
  · exact
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageTopLimit
        (k := k) (Γ := Γ) ho Sbelow hSbelow hsep hi hilim

/-- Successor-index limit-prefix branch for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimitSucc
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
    (hsep :
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow).limitSeparated k Γ ho) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {i j : Set.Iio o} (hij : i < j), j.1 ∈ Set.range Order.succ →
      C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let hstageTop :
      ∀ {i : Set.Iio o} (_hpos : (0 : Ordinal) < i.1),
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
          C.succStagePrefixDiffHahnSeriesLimit k Γ ho i :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageTop
      (k := k) (Γ := Γ) ho Sbelow hSbelow hsep
  change ∀ {i j : Set.Iio o} (hij : i < j), j.1 ∈ Set.range Order.succ →
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij
  intro i j hij hjsucc
  rcases eq_or_lt_of_le (bot_le : (0 : Ordinal) ≤ i.1) with hizero | hi
  · rw [C.limitPrefixDiffHahnSeriesLimit_eq_zero k Γ ho hsep i hizero.symm]
    exact (C.succStageRestrictedPrefixDiffHahnSeriesLimit_eq_zero
      k Γ ho hij hizero.symm).symm
  · exact C.limitPrefixCompatibleWithSuccStage_of_succPositiveBranches k Γ ho hsep
      (fun {p} {hp} {i} hip hposi => by
        calc
          C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
              C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := hstageTop hposi
          _ = C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
                (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
                  change i.1 < Order.succ p
                  rw [hip]
                  exact Order.lt_succ p) := by
                exact
                  (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_top
                    (k := k) (Γ := Γ) ho Sbelow hSbelow (p := p) (hp := hp) hip).symm)
      (fun {p} {hp} {i} hip hposi => by
        calc
          C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
              C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := hstageTop hposi
          _ = C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
                (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
                  exact hip.trans (Order.lt_succ p)) := by
                exact
                  (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_pred
                    (k := k) (Γ := Γ) ho Sbelow hSbelow
                    (p := p) (hp := hp) (i := i) hip).symm)
      hij hi hjsucc

/-- Limit block-prefix compatibility for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimitBlock
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
    (hsep :
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow).limitSeparated k Γ ho) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep
  exact C.limitBlockPrefixCompatibleWithSuccStage_of_targetBranches k Γ ho hsep
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimitTarget
      (k := k) (Γ := Γ) ho Sbelow hSbelow hsep)
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimitSucc
      (k := k) (Γ := Γ) ho Sbelow hSbelow hsep)

/-- Limit-index positive-projection branch for the below-chain extracted from coherent lower
segment systems.

This is the natural-step version of the limit-index next-value comparison: the lower limit value
at `j` is supplied by the segment's `hlimit` field and
`limitStepOfNaturalComponents_block_next_val`, not by an arbitrary total `limitStep`. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_limitIndex
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
    {i j : Set.Iio o} (hij : i < j) (_hi : (0 : Ordinal) < i.1)
    (hj : Order.IsSuccLimit j.1) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
  let ij : Set.Iio j.1 := ⟨i.1, show i.1 ∈ Set.Iio j.1 from hij⟩
  have hjpos : (0 : Ordinal) < j.1 := hj.bot_lt
  have hnatJ : Cj.NaturalComponents k Γ hj :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
      (k := k) (Γ := Γ) Sbelow hSbelow j hj
  have hlimitAt : C j = Cj.limitStepOfNaturalComponents k Γ hj hnatJ :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimit
      (k := k) (Γ := Γ) Sbelow hSbelow j hj
  change
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
      (C.limitBlock k Γ ho i).next.val k Γ
  calc
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ
        =
      ((((C j) hjpos).succOfNoRoot k Γ hjpos hsmall hunit hno).block
        (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ := by
        rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
          (k := k) (Γ := Γ) hsmall hunit hno ho C j
          (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
            (k := k) (Γ := Γ) Sbelow hSbelow (ho.succ_lt j.2))
          hjpos]
    _ =
      ((((C j) hjpos).succOfNoRoot k Γ hjpos hsmall hunit hno).block
        (ordinalIioSuccEmb j.1 ij)).next.val k Γ := by
        rw [ordinalIioSuccTopEmbOfLt_eq_succEmb hij]
    _ =
      (letI : OrderBot (Set.Iio j.1) := ordinalIioOrderBotOfPos hjpos
       (((C j) hjpos).block ij).next.val k Γ) := by
        exact PositiveIioCoherentChain.succOfNoRoot_block_emb_next_val_of_limit
          k Γ hjpos hj hsmall hunit hno ((C j) hjpos) ij
    _ =
      (letI : OrderBot (Set.Iio j.1) := ordinalIioOrderBotOfPos hjpos
       (((Cj.limitStepOfNaturalComponents k Γ hj hnatJ) hjpos).block ij).next.val k Γ) := by
        rw [hlimitAt]
    _ =
      (Cj.limitBlock k Γ hj ij).next.val k Γ := by
        exact Cj.limitStepOfNaturalComponents_block_next_val k Γ hj hnatJ hjpos ij
    _ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
        simp [Cj, ij]

/-- Successor-of-successor top branch for positive projection on a local below-chain. -/
theorem PositiveIioCoherentChainAtBelow.topNextPositive_of_succSuccIndex
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩))
    {q : Ordinal} {hp : Order.succ (Order.succ q) < o}
    {i : Set.Iio o} (hi : i.1 = q) (hipos : (0 : Ordinal) < i.1) :
    ((C.succStageChain k Γ ho (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o)).block
        (ordinalIioSuccTopEmbOfLt
          (show i < (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o) from by
            change i.1 < Order.succ (Order.succ q)
            rw [hi]
            exact (Order.lt_succ q).trans (Order.lt_succ (Order.succ q))))).next.val k Γ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
  classical
  subst q
  let j : Set.Iio o := ⟨Order.succ (Order.succ i.1), hp⟩
  let jpred : Set.Iio o := ⟨Order.succ i.1, (Order.lt_succ (Order.succ i.1)).trans hp⟩
  let hij : i < j := by
    change i.1 < Order.succ (Order.succ i.1)
    exact (Order.lt_succ i.1).trans (Order.lt_succ (Order.succ i.1))
  let hijpred : i < jpred := by
    change i.1 < Order.succ i.1
    exact Order.lt_succ i.1
  have hjpos : (0 : Ordinal) < j.1 := lt_trans hipos hij
  have hjpredpos : (0 : Ordinal) < jpred.1 := lt_trans hipos hijpred
  dsimp only
  calc
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ
        =
      ((C.succStageChain k Γ ho j).block
        (ordinalIioSuccEmb (Order.succ (Order.succ i.1))
          (ordinalIioSuccTopEmbOfLt hijpred))).next.val k Γ := by
        exact congrArg
          (fun e => ((C.succStageChain k Γ ho j).block e).next.val k Γ)
          (by
            rw [ordinalIioSuccTopEmbOfLt_eq_succEmb hij]
            ext
            rfl)
    _ =
      ((((C j) hjpos).succOfNoRoot k Γ hjpos hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ (Order.succ i.1))
          (ordinalIioSuccTopEmbOfLt hijpred))).next.val k Γ := by
        rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
          (k := k) (Γ := Γ) hsmall hunit hno ho C j
          (hsucc (ho.succ_lt j.2)) hjpos]
    _ =
      ((C j hjpos).block (ordinalIioSuccTopEmbOfLt hijpred)).next.val k Γ := by
        exact PositiveIioCoherentChain.succOfNoRoot_block_emb_next_val_of_succ
          (k := k) (Γ := Γ) hsmall hunit hno (C j hjpos)
          (ordinalIioSuccTopEmbOfLt hijpred)
    _ =
      ((((C jpred) hjpredpos).succOfNoRoot k Γ hjpredpos hsmall hunit hno).block
        (ordinalIioSuccTopEmbOfLt hijpred)).next.val k Γ := by
        have hchain :
            C j hjpos =
              (C jpred hjpredpos).succOfNoRoot k Γ hjpredpos hsmall hunit hno := by
          calc
            C j hjpos =
                (PositiveIioCoherentChainAt.succOfNoRoot
                  k Γ hsmall hunit hno (C jpred)) hjpos := by
                  exact congrFun (hsucc j.2) hjpos
            _ =
                (C jpred hjpredpos).succOfNoRoot k Γ hjpredpos hsmall hunit hno := by
                  exact PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
                    k Γ hsmall hunit hno (C jpred) hjpredpos hjpos
        rw [hchain]
    _ =
      (((C jpred hjpredpos).succEndpointTopBlock k Γ).next.val k Γ) := by
        calc
          ((((C jpred hjpredpos).succOfNoRoot k Γ hjpredpos hsmall hunit hno).block
            (ordinalIioSuccTopEmbOfLt hijpred)).next.val k Γ)
              =
            ((((C jpred hjpredpos).succOfNoRoot k Γ hjpredpos hsmall hunit hno).block
              (ordinalIioSuccEmb (Order.succ i.1)
                (ordinalIioSuccOrderTop i.1).top)).next.val k Γ) := by
              rw [ordinalIioSuccTopEmbOfLt_eq_succEmb_top hijpred rfl]
          _ =
            (((C jpred hjpredpos).succEndpointTopBlock k Γ).next.val k Γ) := by
              exact PositiveIioCoherentChain.succOfNoRoot_block_emb_top_next_val_of_succ
                (k := k) (Γ := Γ) hsmall hunit hno (C jpred hjpredpos)
    _ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
        rw [PositiveIioCoherentChainAtBelow.limitBlock_next_val_eq_succStageChain_topBlock
          (k := k) (Γ := Γ) ho C i]
        have hchain :
            C jpred hjpredpos = C.succStageChain k Γ ho i := by
          calc
            C jpred hjpredpos =
                (PositiveIioCoherentChainAt.succOfNoRoot
                  k Γ hsmall hunit hno (C i)) hjpredpos := by
                  exact congrFun (hsucc jpred.2) hjpredpos
            _ =
                (C i hipos).succOfNoRoot k Γ hipos hsmall hunit hno := by
                  exact PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
                    k Γ hsmall hunit hno (C i) hipos hjpredpos
            _ = C.succStageChain k Γ ho i := by
                  exact (PositiveIioCoherentChainAtBelow.succStageChain_of_pos
                    (k := k) (Γ := Γ) hsmall hunit hno ho C i
                    (hsucc (ho.succ_lt i.2)) hipos).symm
        rw [hchain]

/-- Successor-of-successor predecessor branch for positive projection on a local below-chain. -/
theorem PositiveIioCoherentChainAtBelow.topNextPositive_pred_of_succSuccIndex
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩))
    {q : Ordinal} {hp : Order.succ (Order.succ q) < o}
    (hpred :
      ∀ {i : Set.Iio o} (hi : i.1 < q) (_hpos : (0 : Ordinal) < i.1),
        ((C.succStageChain k Γ ho
            (⟨Order.succ q, (Order.lt_succ (Order.succ q)).trans hp⟩ : Set.Iio o)).block
            (ordinalIioSuccTopEmbOfLt
              (show i < (⟨Order.succ q,
                  (Order.lt_succ (Order.succ q)).trans hp⟩ : Set.Iio o) from by
                exact hi.trans (Order.lt_succ q)))).next.val k Γ =
          (C.limitBlock k Γ ho i).next.val k Γ)
    {i : Set.Iio o} (hi : i.1 < q) (hipos : (0 : Ordinal) < i.1) :
    ((C.succStageChain k Γ ho (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o)).block
        (ordinalIioSuccTopEmbOfLt
          (show i < (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o) from by
            exact (hi.trans (Order.lt_succ q)).trans (Order.lt_succ (Order.succ q))))).next.val
          k Γ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
  classical
  let j : Set.Iio o := ⟨Order.succ (Order.succ q), hp⟩
  let jpred : Set.Iio o :=
    ⟨Order.succ q, (Order.lt_succ (Order.succ q)).trans hp⟩
  let hij : i < j := by
    change i.1 < Order.succ (Order.succ q)
    exact (hi.trans (Order.lt_succ q)).trans (Order.lt_succ (Order.succ q))
  let hijpred : i < jpred := by
    change i.1 < Order.succ q
    exact hi.trans (Order.lt_succ q)
  have hjpos : (0 : Ordinal) < j.1 := lt_trans hipos hij
  dsimp only
  calc
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ
        =
      ((C.succStageChain k Γ ho j).block
        (ordinalIioSuccEmb (Order.succ (Order.succ q))
          (ordinalIioSuccTopEmbOfLt hijpred))).next.val k Γ := by
        exact congrArg
          (fun e => ((C.succStageChain k Γ ho j).block e).next.val k Γ)
          (by
            rw [ordinalIioSuccTopEmbOfLt_eq_succEmb hij]
            ext
            rfl)
    _ =
      ((((C j) hjpos).succOfNoRoot k Γ hjpos hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ (Order.succ q))
          (ordinalIioSuccTopEmbOfLt hijpred))).next.val k Γ := by
        rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
          (k := k) (Γ := Γ) hsmall hunit hno ho C j
          (hsucc (ho.succ_lt j.2)) hjpos]
    _ =
      ((C j hjpos).block (ordinalIioSuccTopEmbOfLt hijpred)).next.val k Γ := by
        exact PositiveIioCoherentChain.succOfNoRoot_block_emb_next_val_of_succ
          (k := k) (Γ := Γ) hsmall hunit hno (C j hjpos)
          (ordinalIioSuccTopEmbOfLt hijpred)
    _ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
        have hchain :
            C j hjpos = C.succStageChain k Γ ho jpred := by
          calc
            C j hjpos =
                (PositiveIioCoherentChainAt.succOfNoRoot
                  k Γ hsmall hunit hno (C jpred)) hjpos := by
                  exact congrFun (hsucc j.2) hjpos
            _ =
                (C jpred (lt_trans hipos hijpred)).succOfNoRoot
                  k Γ (lt_trans hipos hijpred) hsmall hunit hno := by
                  exact PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
                    k Γ hsmall hunit hno (C jpred) (lt_trans hipos hijpred) hjpos
            _ = C.succStageChain k Γ ho jpred := by
                  exact (PositiveIioCoherentChainAtBelow.succStageChain_of_pos
                    (k := k) (Γ := Γ) hsmall hunit hno ho C jpred
                    (hsucc (ho.succ_lt jpred.2))
                    (lt_trans hipos hijpred)).symm
        rw [hchain]
        exact hpred hi hipos

/-- Successor-of-limit predecessor branch for positive projection on the final segment
below-chain. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_succLimit
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
    {p : Ordinal} {hp : Order.succ p < o} (hplim : Order.IsSuccLimit p)
    {i : Set.Iio o} (hi : i.1 < p) (hipos : (0 : Ordinal) < i.1) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ((C.succStageChain k Γ ho (⟨Order.succ p, hp⟩ : Set.Iio o)).block
        (ordinalIioSuccTopEmbOfLt
          (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
            exact hi.trans (Order.lt_succ p)))).next.val k Γ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
  classical
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let j : Set.Iio o := ⟨Order.succ p, hp⟩
  let pidx : Set.Iio o := ⟨p, (Order.lt_succ p).trans hp⟩
  let hij : i < j := by
    change i.1 < Order.succ p
    exact hi.trans (Order.lt_succ p)
  let hip : i < pidx := by
    change i.1 < p
    exact hi
  let ip : Set.Iio (Order.succ p) := ⟨i.1, hi.trans (Order.lt_succ p)⟩
  have hjpos : (0 : Ordinal) < j.1 := lt_trans hipos hij
  dsimp only
  calc
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ
        =
      ((C.succStageChain k Γ ho j).block
        (ordinalIioSuccEmb (Order.succ p) ip)).next.val k Γ := by
        exact congrArg
          (fun e => ((C.succStageChain k Γ ho j).block e).next.val k Γ)
          (by
            rw [ordinalIioSuccTopEmbOfLt_eq_succEmb hij])
    _ =
      ((((C j) hjpos).succOfNoRoot k Γ hjpos hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ p) ip)).next.val k Γ := by
        rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
          (k := k) (Γ := Γ) hsmall hunit hno ho C j
          (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
            (k := k) (Γ := Γ) Sbelow hSbelow (ho.succ_lt j.2))
          hjpos]
    _ =
      ((C j hjpos).block ip).next.val k Γ := by
        exact PositiveIioCoherentChain.succOfNoRoot_block_emb_next_val_of_succ
          (k := k) (Γ := Γ) hsmall hunit hno (C j hjpos) ip
    _ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
        have hchain :
            C j hjpos = C.succStageChain k Γ ho pidx := by
          calc
            C j hjpos =
                (PositiveIioCoherentChainAt.succOfNoRoot
                  k Γ hsmall hunit hno (C pidx)) hjpos := by
                  exact congrFun
                    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
                      (k := k) (Γ := Γ) Sbelow hSbelow hp)
                    hjpos
            _ =
                (C pidx hplim.bot_lt).succOfNoRoot k Γ hplim.bot_lt hsmall hunit hno := by
                  exact PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
                    k Γ hsmall hunit hno (C pidx) hplim.bot_lt hjpos
            _ = C.succStageChain k Γ ho pidx := by
                  exact (PositiveIioCoherentChainAtBelow.succStageChain_of_pos
                    (k := k) (Γ := Γ) hsmall hunit hno ho C pidx
                    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
                      (k := k) (Γ := Γ) Sbelow hSbelow (ho.succ_lt pidx.2))
                    hplim.bot_lt).symm
        rw [hchain]
        change
          ((C.succStageChain k Γ ho pidx).block
            (ordinalIioSuccTopEmbOfLt hip)).next.val k Γ =
            (C.limitBlock k Γ ho i).next.val k Γ
        exact
          KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_limitIndex
            (k := k) (Γ := Γ) ho Sbelow hSbelow hip hipos hplim

/-- Successor-index predecessor branch for positive projection on the final segment below-chain. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_pred
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
      (hi : i.1 < p) (_hpos : (0 : Ordinal) < i.1),
        ((C.succStageChain k Γ ho (⟨Order.succ p, hp⟩ : Set.Iio o)).block
            (ordinalIioSuccTopEmbOfLt
              (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
                exact hi.trans (Order.lt_succ p)))).next.val k Γ =
          (C.limitBlock k Γ ho i).next.val k Γ := by
  classical
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let P : Ordinal → Prop := fun p =>
    ∀ {hp : Order.succ p < o} {i : Set.Iio o}
      (hi : i.1 < p) (_hpos : (0 : Ordinal) < i.1),
      ((C.succStageChain k Γ ho (⟨Order.succ p, hp⟩ : Set.Iio o)).block
          (ordinalIioSuccTopEmbOfLt
            (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
              exact hi.trans (Order.lt_succ p)))).next.val k Γ =
        (C.limitBlock k Γ ho i).next.val k Γ
  dsimp only
  intro p
  change P p
  induction p using Ordinal.limitRecOn with
  | zero =>
      intro _hp i hi _hipos
      exact False.elim ((not_lt_of_ge (bot_le : (0 : Ordinal) ≤ i.1)) hi)
  | add_one q ih =>
      intro hp i hi hipos
      rcases ordinal_lt_succ_eq_or_lt (show i.1 < Order.succ q from hi) with htop | hlt
      · exact C.topNextPositive_of_succSuccIndex
          k Γ hsmall hunit hno ho
          (fun {p} hp =>
            KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
              (k := k) (Γ := Γ) Sbelow hSbelow hp)
          (q := q) (hp := hp) htop hipos
      · exact C.topNextPositive_pred_of_succSuccIndex
          k Γ hsmall hunit hno ho
          (fun {p} hp =>
            KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
              (k := k) (Γ := Γ) Sbelow hSbelow hp)
          (q := q) (hp := hp)
          (fun {i} hiq hipos =>
            ih (hp := (Order.lt_succ (Order.succ q)).trans hp) (i := i) hiq hipos)
          hlt hipos
  | limit p hplim _ih =>
      intro hp i hi hipos
      exact
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_succLimit
          (k := k) (Γ := Γ) ho Sbelow hSbelow
          (p := p) (hp := hp) hplim hi hipos

/-- Successor-index positive-projection branch for the final segment below-chain. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_succ
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
      j.1 ∈ Set.range Order.succ →
        ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
          (C.limitBlock k Γ ho i).next.val k Γ := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let hpred :
      ∀ {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
        (hi : i.1 < p) (_hpos : (0 : Ordinal) < i.1),
          ((C.succStageChain k Γ ho (⟨Order.succ p, hp⟩ : Set.Iio o)).block
              (ordinalIioSuccTopEmbOfLt
                (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
                  exact hi.trans (Order.lt_succ p)))).next.val k Γ =
            (C.limitBlock k Γ ho i).next.val k Γ :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_pred
      (k := k) (Γ := Γ) ho Sbelow hSbelow
  change ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
      j.1 ∈ Set.range Order.succ →
        ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
          (C.limitBlock k Γ ho i).next.val k Γ
  intro i j hij hi hsucc
  rcases hsucc with ⟨p, hpj⟩
  cases j with
  | mk j hj =>
      dsimp at hpj
      subst j
      rcases ordinal_lt_succ_eq_or_lt (show i.1 < Order.succ p from hij) with htop | hlt
      · subst p
        let j' : Set.Iio o := ⟨Order.succ i.1, hj⟩
        let hij' : i < j' := by
          change i.1 < Order.succ i.1
          exact Order.lt_succ i.1
        have hjpos : (0 : Ordinal) < j'.1 := lt_trans hi hij'
        calc
          ((C.succStageChain k Γ ho j').block
              (ordinalIioSuccTopEmbOfLt hij')).next.val k Γ
              =
            ((C.succStageChain k Γ ho j').block
              (ordinalIioSuccEmb (Order.succ i.1)
                (ordinalIioSuccOrderTop i.1).top)).next.val k Γ := by
              rw [ordinalIioSuccTopEmbOfLt_eq_succEmb_top hij' rfl]
          _ =
            ((((C j') hjpos).succOfNoRoot k Γ hjpos hsmall hunit hno).block
              (ordinalIioSuccEmb (Order.succ i.1)
                (ordinalIioSuccOrderTop i.1).top)).next.val k Γ := by
              rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
                (k := k) (Γ := Γ) hsmall hunit hno ho C j'
                (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
                  (k := k) (Γ := Γ) Sbelow hSbelow (ho.succ_lt j'.2))
                hjpos]
          _ =
            ((C j' hjpos).succEndpointTopBlock k Γ).next.val k Γ := by
              exact PositiveIioCoherentChain.succOfNoRoot_block_emb_top_next_val_of_succ
                (k := k) (Γ := Γ) hsmall hunit hno (C j' hjpos)
          _ =
            (C.limitBlock k Γ ho i).next.val k Γ := by
              rw [PositiveIioCoherentChainAtBelow.limitBlock_next_val_eq_succStageChain_topBlock
                (k := k) (Γ := Γ) ho C i]
              have hchain : C j' hjpos = C.succStageChain k Γ ho i := by
                calc
                  C j' hjpos =
                      (PositiveIioCoherentChainAt.succOfNoRoot
                        k Γ hsmall hunit hno (C i)) hjpos := by
                        exact congrFun
                          (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
                            (k := k) (Γ := Γ) Sbelow hSbelow j'.2)
                          hjpos
                  _ =
                      (C i hi).succOfNoRoot k Γ hi hsmall hunit hno := by
                        exact PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
                          k Γ hsmall hunit hno (C i) hi hjpos
                  _ = C.succStageChain k Γ ho i := by
                        exact (PositiveIioCoherentChainAtBelow.succStageChain_of_pos
                          (k := k) (Γ := Γ) hsmall hunit hno ho C i
                          (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
                            (k := k) (Γ := Γ) Sbelow hSbelow (ho.succ_lt i.2))
                          hi).symm
              rw [hchain]
      · exact hpred hlt hi

/-- Positive projection for the below-chain extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_positiveProjection
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.succStageTopNextValProjectionCompatiblePositive k Γ ho := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change C.succStageTopNextValProjectionCompatiblePositive k Γ ho
  exact C.succStageTopNextValProjectionPositive_of_targetBranches k Γ ho
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_limitIndex
      (k := k) (Γ := Γ) ho Sbelow hSbelow)
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_topNextPos_succ
      (k := k) (Γ := Γ) ho Sbelow hSbelow)

/-- Bottom limit-state source for the below-chain extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_limitState_bot_source
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
     (C.limitState k Γ ho ⊥).source) =
      (oneClusterInitialStateOfNoRoot k Γ hno).source := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  change (C.limitState k Γ ho (⊥ : Set.Iio o)).source =
    (oneClusterInitialStateOfNoRoot k Γ hno).source
  exact C.limitState_bot_source_of_succ
    (k := k) (Γ := Γ) ho
    (fun {p} hp =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
        (k := k) (Γ := Γ) Sbelow hSbelow hp)

/-- Zero-index limit-block next value for the below-chain extracted from coherent lower segment
systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_limitBlock_next_zero
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    ∀ i : Set.Iio o, (i : Ordinal) = 0 →
      (C.limitBlock k Γ ho i).next.val k Γ =
        (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
          (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change ∀ i : Set.Iio o, (i : Ordinal) = 0 →
    (C.limitBlock k Γ ho i).next.val k Γ =
      (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ
  intro i hi
  have hbot : i = (⟨0, ho.bot_lt⟩ : Set.Iio o) := by
    apply Subtype.ext
    exact hi
  rw [hbot]
  exact C.limitBlock_bot_next_val_of_succ
    (k := k) (Γ := Γ) ho
    (fun {p} hp =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
        (k := k) (Γ := Γ) Sbelow hSbelow hp)

/-- Canonical bottom source for the below-chain extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_botSourceEq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.BotSourceEq k Γ (oneClusterInitialStateOfNoRoot k Γ hno).source := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change C.BotSourceEq k Γ (oneClusterInitialStateOfNoRoot k Γ hno).source
  intro i hpos
  let Si := Sbelow i
  let topSeg := Si.segment ⟨i.1, (show i.1 ≤ i.1 from le_rfl)⟩
  let _ : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hpos
  change OneClusterCoherentBlockChain.BotSourceEq k Γ
    (topSeg.R ⟨i.1, (show i.1 ≤ i.1 from le_rfl)⟩ hpos)
    (oneClusterInitialStateOfNoRoot k Γ hno).source
  exact
    (KOneClusterPositiveFinalExternalNaturalSegment.botInvariants
      (k := k) (Γ := Γ) topSeg (show i.1 ≤ i.1 from le_rfl)).1 hpos

/-- Canonical bottom next value for successor stages in the below-chain extracted from coherent
lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succStageBotBlockNextValEq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.succStageBotBlockNextValEq k Γ ho
      ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change C.succStageBotBlockNextValEq k Γ ho
    ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
      (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ)
  intro i
  let Ssucc := Sbelow ⟨Order.succ i.1, ho.succ_lt i.2⟩
  let topSeg := Ssucc.segment
    ⟨Order.succ i.1, (show Order.succ i.1 ≤ Order.succ i.1 from le_rfl)⟩
  let _ : OrderBot (Set.Iio (Order.succ i.1)) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ i.1))
  change OneClusterCoherentBlockChain.BotBlockNextValEq k Γ
    (topSeg.R
      ⟨Order.succ i.1, (show Order.succ i.1 ≤ Order.succ i.1 from le_rfl)⟩
      (lt_of_le_of_lt bot_le (Order.lt_succ i.1)))
    ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
      (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ)
  exact
    (KOneClusterPositiveFinalExternalNaturalSegment.botInvariants
      (k := k) (Γ := Γ) topSeg
      (show Order.succ i.1 ≤ Order.succ i.1 from le_rfl)).2
      (lt_of_le_of_lt bot_le (Order.lt_succ i.1))

/-- Current natural components for the below-chain extracted from coherent lower segment systems,
once the two current block-prefix fields have been supplied. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_natural_of_blockPrefix
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
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.NaturalComponents k Γ ho := by
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
  change C.NaturalComponents k Γ ho
  exact C.naturalComponents_of_blockPrefix k Γ ho hpositive
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_botSourceEq
      (k := k) (Γ := Γ) Sbelow)
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_limitState_bot_source
      (k := k) (Γ := Γ) ho Sbelow hSbelow)
    hbotNext hlimitBotNext
    (by
      dsimp [C, hpositive, hbotNext, hlimitBotNext] at hlimitBlock ⊢
      exact hlimitBlock)
    (by
      dsimp [C] at hstageBlock ⊢
      exact hstageBlock)

end HahnField

end

end HahnKaplanskyRealClosedness
