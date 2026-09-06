/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Components.Basic

/-!
# Compatible positive limit-chain components
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

structure PositiveIioCoherentChainAtBelow.LimitCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop where
  nextVal : C.limitNextValCompatible k Γ ho
  coherent : C.limitCoherent k Γ ho (C.limitSeparated_of_nextValCompatible k Γ ho nextVal)

noncomputable def PositiveIioCoherentChainAtBelow.limitCoherentChain
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (hcoh : C.limitCoherent k Γ ho hsep) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
     OneClusterCoherentBlockChain k Γ (Set.Iio o) F) := by
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  exact
    { toOneClusterBlockChain := C.limitBlockChain k Γ ho hsep
      coherent_source := hcoh }

noncomputable def PositiveIioCoherentChainAtBelow.limitPositiveChain
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (hcoh : C.limitCoherent k Γ ho hsep) :
    PositiveIioCoherentChain k Γ o ho.bot_lt F := by
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  exact C.limitCoherentChain k Γ ho hsep hcoh

noncomputable def PositiveIioCoherentChainAtBelow.limitPositiveChainOfCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho) :
    PositiveIioCoherentChain k Γ o ho.bot_lt F :=
  C.limitPositiveChain k Γ ho
    (C.limitSeparated_of_nextValCompatible k Γ ho hcompat.nextVal)
    hcompat.coherent

noncomputable def PositiveIioCoherentChainAtBelow.limitStepOfCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho) :
    PositiveIioCoherentChainAt k Γ o F := by
  intro hpos
  have hproof : hpos = ho.bot_lt := Subsingleton.elim hpos ho.bot_lt
  cases hproof
  exact C.limitPositiveChainOfCompatible k Γ ho hcompat

theorem PositiveIioCoherentChainAtBelow.limitStepOfCompatible_botSourceEq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho)
    {s₀ : valuationSubring k Γ}
    (hbot :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀) :
    (C.limitStepOfCompatible k Γ ho hcompat).BotSourceEq k Γ s₀ := by
  intro hpos
  unfold OneClusterCoherentBlockChain.BotSourceEq
  unfold PositiveIioCoherentChainAtBelow.limitStepOfCompatible
  have hproof : hpos = ho.bot_lt := Subsingleton.elim hpos ho.bot_lt
  cases hproof
  change
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
     ((C.limitPositiveChainOfCompatible k Γ ho hcompat).state
        (⊥ : Set.Iio o)).source) = s₀
  unfold PositiveIioCoherentChainAtBelow.limitPositiveChainOfCompatible
  unfold PositiveIioCoherentChainAtBelow.limitPositiveChain
  unfold PositiveIioCoherentChainAtBelow.limitCoherentChain
  exact hbot

theorem PositiveIioCoherentChainAtBelow.limitStepOfCompatible_botBlockNextValEq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho)
    {v₀ : Γ}
    (hbot :
      ∀ i : Set.Iio o, (i : Ordinal) = 0 →
        (C.limitBlock k Γ ho i).next.val k Γ = v₀) :
    (C.limitStepOfCompatible k Γ ho hcompat).BotBlockNextValEq k Γ v₀ := by
  intro hpos
  unfold OneClusterCoherentBlockChain.BotBlockNextValEq
  unfold PositiveIioCoherentChainAtBelow.limitStepOfCompatible
  have hproof : hpos = ho.bot_lt := Subsingleton.elim hpos ho.bot_lt
  cases hproof
  change
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
     ((C.limitPositiveChainOfCompatible k Γ ho hcompat).block
        (⊥ : Set.Iio o)).next.val k Γ) = v₀
  unfold PositiveIioCoherentChainAtBelow.limitPositiveChainOfCompatible
  unfold PositiveIioCoherentChainAtBelow.limitPositiveChain
  unfold PositiveIioCoherentChainAtBelow.limitCoherentChain
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
  exact hbot (⊥ : Set.Iio o) rfl

@[simp]
theorem PositiveIioCoherentChainAtBelow.limitStepOfCompatible_block_next_val
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho)
    (hpos : (0 : Ordinal) < o) (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (((C.limitStepOfCompatible k Γ ho hcompat hpos).block i).next.val k Γ)) =
      (C.limitBlock k Γ ho i).next.val k Γ := by
  unfold PositiveIioCoherentChainAtBelow.limitStepOfCompatible
  have hproof : hpos = ho.bot_lt := Subsingleton.elim hpos ho.bot_lt
  cases hproof
  rfl

@[simp]
theorem PositiveIioCoherentChainAtBelow.limitStepOfCompatible_block_diffHahnSeries
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho)
    (hpos : (0 : Ordinal) < o) (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (((C.limitStepOfCompatible k Γ ho hcompat hpos).block i).diffHahnSeries k Γ)) =
      (C.limitBlock k Γ ho i).diffHahnSeries k Γ := by
  unfold PositiveIioCoherentChainAtBelow.limitStepOfCompatible
  have hproof : hpos = ho.bot_lt := Subsingleton.elim hpos ho.bot_lt
  cases hproof
  rfl

theorem PositiveIioCoherentChainAtBelow.limitStepOfCompatible_restrictLT_diffHahnSeriesLimit
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho)
    (hpos : (0 : Ordinal) < o) (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (((C.limitStepOfCompatible k Γ ho hcompat hpos).toOneClusterBlockChain.restrictLT
        k Γ i).diffHahnSeriesLimit k Γ)) =
      ((C.limitBlockChain k Γ ho
        (C.limitSeparated_of_nextValCompatible k Γ ho hcompat.nextVal)
        |>.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
  unfold PositiveIioCoherentChainAtBelow.limitStepOfCompatible
  have hproof : hpos = ho.bot_lt := Subsingleton.elim hpos ho.bot_lt
  cases hproof
  rfl

theorem PositiveIioCoherentChainAtBelow.limitStepOfCompatible_diffHahnSeriesLimit
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho)
    (hpos : (0 : Ordinal) < o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (C.limitStepOfCompatible k Γ ho hcompat hpos).toOneClusterBlockChain.diffHahnSeriesLimit
        k Γ) =
      (C.limitBlockChain k Γ ho
        (C.limitSeparated_of_nextValCompatible k Γ ho hcompat.nextVal)
        |>.diffHahnSeriesLimit k Γ) := by
  classical
  apply OneClusterBlockChain.diffHahnSeriesLimit_congr
  intro i
  exact C.limitStepOfCompatible_block_diffHahnSeries k Γ ho hcompat hpos i

theorem PositiveIioCoherentChainAtBelow.limitStepOfCompatible_restrictLT_diffHahnSeriesLimit_sep
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho)
    (hsep : C.limitSeparated k Γ ho)
    (hpos : (0 : Ordinal) < o) (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (((C.limitStepOfCompatible k Γ ho hcompat hpos).toOneClusterBlockChain.restrictLT
        k Γ i).diffHahnSeriesLimit k Γ)) =
      ((C.limitBlockChain k Γ ho hsep |>.restrictLT k Γ i)
        |>.diffHahnSeriesLimit k Γ) := by
  let hsepCompat : C.limitSeparated k Γ ho :=
    C.limitSeparated_of_nextValCompatible k Γ ho hcompat.nextVal
  calc
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (((C.limitStepOfCompatible k Γ ho hcompat hpos).toOneClusterBlockChain.restrictLT
        k Γ i).diffHahnSeriesLimit k Γ)) =
        ((C.limitBlockChain k Γ ho hsepCompat |>.restrictLT k Γ i)
          |>.diffHahnSeriesLimit k Γ) := by
          exact C.limitStepOfCompatible_restrictLT_diffHahnSeriesLimit
            k Γ ho hcompat hpos i
    _ = ((C.limitBlockChain k Γ ho hsep |>.restrictLT k Γ i)
          |>.diffHahnSeriesLimit k Γ) := by
          change C.limitPrefixDiffHahnSeriesLimit k Γ ho hsepCompat i =
            C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i
          exact C.limitPrefixDiffHahnSeriesLimit_congr_sep k Γ ho hsepCompat hsep i

theorem PositiveIioCoherentChainAtBelow.limitStepOfCompatible_diffHahnSeriesLimit_sep
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.LimitCompatible k Γ ho)
    (hsep : C.limitSeparated k Γ ho)
    (hpos : (0 : Ordinal) < o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (C.limitStepOfCompatible k Γ ho hcompat hpos).toOneClusterBlockChain
        |>.diffHahnSeriesLimit k Γ) =
      (C.limitBlockChain k Γ ho hsep |>.diffHahnSeriesLimit k Γ) := by
  let hsepCompat : C.limitSeparated k Γ ho :=
    C.limitSeparated_of_nextValCompatible k Γ ho hcompat.nextVal
  calc
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (C.limitStepOfCompatible k Γ ho hcompat hpos).toOneClusterBlockChain
        |>.diffHahnSeriesLimit k Γ) =
        (C.limitBlockChain k Γ ho hsepCompat |>.diffHahnSeriesLimit k Γ) := by
          exact C.limitStepOfCompatible_diffHahnSeriesLimit k Γ ho hcompat hpos
    _ = (C.limitBlockChain k Γ ho hsep |>.diffHahnSeriesLimit k Γ) := by
          exact C.limitBlockChain_diffHahnSeriesLimit_congr_sep k Γ ho hsepCompat hsep

def PositiveIioCoherentChain.restrictLTBlockChain
    {o : Ordinal} {hpos : (0 : Ordinal) < o}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (i : Set.Iio o) :
    OneClusterBlockChain k Γ (Set.Iio i.1) F := by
  classical
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  let E := ordinalIioSubtypeIioEquiv i
  refine
    { state := fun j => C.state ((E.symm j).1)
      block := fun j => C.block ((E.symm j).1)
      separated := ?_ }
  intro j l hjl
  exact C.separated (show ((E.symm j).1 : Set.Iio o) < (E.symm l).1 from hjl)

theorem PositiveIioCoherentChain.restrictLTBlockChain_diffHahnSeriesLimit
    {o : Ordinal} {hpos : (0 : Ordinal) < o}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (i : Set.Iio o) :
    (C.restrictLTBlockChain k Γ i).diffHahnSeriesLimit k Γ =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ)) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  let R := C.restrictLTBlockChain k Γ i
  let P := C.toOneClusterBlockChain.restrictLT k Γ i
  let E := ordinalIioSubtypeIioEquiv i
  let sR := R.diffSummableFamily k Γ
  let sP := P.diffSummableFamily k Γ
  have heq : sR = HahnSeries.SummableFamily.Equiv E sP := by
    ext j
    dsimp [HahnSeries.SummableFamily.Equiv, sR, sP, R, P,
      OneClusterBlockChain.diffSummableFamily]
    rfl
  change sR.hsum = sP.hsum
  rw [heq, HahnSeries.SummableFamily.hsum_equiv]

theorem PositiveIioCoherentChainAtBelow.restrictedPrefix_eq_restrictLTBlockChain
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) :
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
      (let Cj : PositiveIioCoherentChain k Γ (Order.succ j.1)
          (lt_of_le_of_lt bot_le (Order.lt_succ j.1)) F :=
        C.succStageChain k Γ ho j
       (Cj.restrictLTBlockChain k Γ
        (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ) := by
  let Cj : PositiveIioCoherentChain k Γ (Order.succ j.1)
      (lt_of_le_of_lt bot_le (Order.lt_succ j.1)) F :=
    C.succStageChain k Γ ho j
  unfold PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
  change
    ((Cj.toOneClusterBlockChain.restrictLT k Γ (ordinalIioSuccTopEmbOfLt hij))
      |>.diffHahnSeriesLimit k Γ) =
      ((Cj.restrictLTBlockChain k Γ
        (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ)
  rw [Cj.restrictLTBlockChain_diffHahnSeriesLimit k Γ (ordinalIioSuccTopEmbOfLt hij)]

theorem PositiveIioCoherentChainAtBelow.stagePrefix_eq_restrictLTBlockChain
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o) :
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i =
      (let Ci : PositiveIioCoherentChain k Γ (Order.succ i.1)
          (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) F :=
        C.succStageChain k Γ ho i
       (Ci.restrictLTBlockChain k Γ
        (ordinalIioSuccOrderTop i.1).top).diffHahnSeriesLimit k Γ) := by
  let Ci : PositiveIioCoherentChain k Γ (Order.succ i.1)
      (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) F :=
    C.succStageChain k Γ ho i
  unfold PositiveIioCoherentChainAtBelow.succStagePrefixDiffHahnSeriesLimit
  change
    ((Ci.toOneClusterBlockChain.restrictLT k Γ (ordinalIioSuccOrderTop i.1).top)
      |>.diffHahnSeriesLimit k Γ) =
      ((Ci.restrictLTBlockChain k Γ
        (ordinalIioSuccOrderTop i.1).top).diffHahnSeriesLimit k Γ)
  rw [Ci.restrictLTBlockChain_diffHahnSeriesLimit k Γ (ordinalIioSuccOrderTop i.1).top]

@[simp]
theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit_eq_zero
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) (hi : (i : Ordinal) = 0) :
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij = 0 := by
  unfold PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
  let endpoint := ordinalIioSuccTopEmbOfLt hij
  let _ : IsEmpty (Set.Iio endpoint) :=
    ⟨fun l => by
      have hlt : (l.1.1 : Ordinal) < endpoint.1 := l.2
      have hlt0 : (l.1.1 : Ordinal) < 0 := by
        simp [endpoint, ordinalIioSuccTopEmbOfLt_val, hi] at hlt
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ l.1.1)) hlt0⟩
  exact OneClusterBlockChain.diffHahnSeriesLimit_eq_zero_of_isEmpty k Γ
    ((C.succStageChain k Γ ho j).toOneClusterBlockChain.restrictLT k Γ
      endpoint)

@[simp]
theorem PositiveIioCoherentChainAtBelow.succStagePrefixDiffHahnSeriesLimit_eq_zero
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (i : Set.Iio o) (hi : (i : Ordinal) = 0) :
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i = 0 := by
  unfold PositiveIioCoherentChainAtBelow.succStagePrefixDiffHahnSeriesLimit
  let endpoint := (ordinalIioSuccOrderTop i.1).top
  let _ : IsEmpty (Set.Iio endpoint) :=
    ⟨fun l => by
      have hlt : (l.1.1 : Ordinal) < endpoint.1 := l.2
      have hlt0 : (l.1.1 : Ordinal) < 0 := by
        simp [endpoint, hi] at hlt
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ l.1.1)) hlt0⟩
  exact OneClusterBlockChain.diffHahnSeriesLimit_eq_zero_of_isEmpty k Γ
    ((C.succStageChain k Γ ho i).toOneClusterBlockChain.restrictLT k Γ
      endpoint)

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixCompatible_bot
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) (hi : (i : Ordinal) = 0) :
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  rw [C.succStageRestrictedPrefixDiffHahnSeriesLimit_eq_zero k Γ ho hij hi]
  rw [C.succStagePrefixDiffHahnSeriesLimit_eq_zero k Γ ho i hi]

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixCompatible_of_succPositiveBranches
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (htop :
      ∀ {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
        (hi : i.1 = p) (_hpos : (0 : Ordinal) < i.1),
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
            (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
              change i.1 < Order.succ p
              rw [hi]
              exact Order.lt_succ p) =
          C.succStagePrefixDiffHahnSeriesLimit k Γ ho i)
    (hpred :
      ∀ {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
        (hi : i.1 < p),
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
            (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
              exact hi.trans (Order.lt_succ p)) =
          C.succStagePrefixDiffHahnSeriesLimit k Γ ho i) :
    ∀ {i j : Set.Iio o} (hij : i < j), j.1 ∈ Set.range Order.succ →
      C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  intro i j hij hjsucc
  rcases hjsucc with ⟨p, hpj⟩
  cases j with
  | mk j hj =>
      dsimp at hpj
      subst j
      rcases ordinal_lt_succ_eq_or_lt (show i.1 < Order.succ p from hij) with hi | hi
      · by_cases hzero : (i.1 : Ordinal) = 0
        · exact C.succStageRestrictedPrefixCompatible_bot k Γ ho hij hzero
        · exact htop (hp := hj) hi (lt_of_le_of_ne bot_le (Ne.symm hzero))
      · exact hpred (hp := hj) hi

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixCompatible_of_targetBranches
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hlimit :
      ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
        Order.IsSuccLimit j.1 →
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
            C.succStagePrefixDiffHahnSeriesLimit k Γ ho i)
    (hsucc :
      ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
        j.1 ∈ Set.range Order.succ →
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij =
            C.succStagePrefixDiffHahnSeriesLimit k Γ ho i) :
    C.succStageRestrictedPrefixCompatible k Γ ho := by
  intro i j hij
  rcases eq_or_lt_of_le (bot_le : (0 : Ordinal) ≤ i.1) with hizero | hi
  · exact C.succStageRestrictedPrefixCompatible_bot k Γ ho hij hizero.symm
  · rcases Ordinal.zero_or_succ_or_isSuccLimit j.1 with hzero | hsucc' | hjlim
    · have hjpos : (0 : Ordinal) < j.1 := lt_trans hi hij
      rw [hzero] at hjpos
      exact False.elim ((lt_irrefl (0 : Ordinal)) hjpos)
    · exact hsucc hij hi hsucc'
    · exact hlimit hij hi hjlim

theorem PositiveIioCoherentChainAtBelow.limitPrefixCompatibleWithSuccStage_of_succPositiveBranches
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (htop :
      ∀ {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
        (hi : i.1 = p) (_hpos : (0 : Ordinal) < i.1),
          C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
            C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
              (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
                change i.1 < Order.succ p
                rw [hi]
                exact Order.lt_succ p))
    (hpred :
      ∀ {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
        (hi : i.1 < p) (_hpos : (0 : Ordinal) < i.1),
          C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
            C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
              (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
                exact hi.trans (Order.lt_succ p))) :
    ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
      j.1 ∈ Set.range Order.succ →
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij := by
  intro i j hij hi hjsucc
  rcases hjsucc with ⟨p, hpj⟩
  cases j with
  | mk j hj =>
      dsimp at hpj
      subst j
      rcases ordinal_lt_succ_eq_or_lt (show i.1 < Order.succ p from hij) with hip | hip
      · exact htop (hp := hj) hip hi
      · exact hpred (hp := hj) hip hi

def PositiveIioCoherentChainAtBelow.succStageRestrictedBlockPrefixCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j),
    (let Cj : PositiveIioCoherentChain k Γ (Order.succ j.1)
          (lt_of_le_of_lt bot_le (Order.lt_succ j.1)) F :=
        C.succStageChain k Γ ho j
     (Cj.restrictLTBlockChain k Γ
        (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ) =
    (let Ci : PositiveIioCoherentChain k Γ (Order.succ i.1)
          (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) F :=
        C.succStageChain k Γ ho i
     (Ci.restrictLTBlockChain k Γ
        (ordinalIioSuccOrderTop i.1).top).diffHahnSeriesLimit k Γ)

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixCompatible_of_blockPrefix
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageRestrictedBlockPrefixCompatible k Γ ho) :
    C.succStageRestrictedPrefixCompatible k Γ ho := by
  intro i j hij
  rw [C.restrictedPrefix_eq_restrictLTBlockChain k Γ ho hij]
  rw [C.stagePrefix_eq_restrictLTBlockChain k Γ ho i]
  exact hcompat hij

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedBlockPrefixCompatible_of_prefix
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageRestrictedPrefixCompatible k Γ ho) :
    C.succStageRestrictedBlockPrefixCompatible k Γ ho := by
  intro i j hij
  rw [← C.restrictedPrefix_eq_restrictLTBlockChain k Γ ho hij]
  rw [← C.stagePrefix_eq_restrictLTBlockChain k Γ ho i]
  exact hcompat hij

def PositiveIioCoherentChainAtBelow.limitBlockPrefixCompatibleWithSuccStage
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j),
    C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
      (let Cj : PositiveIioCoherentChain k Γ (Order.succ j.1)
          (lt_of_le_of_lt bot_le (Order.lt_succ j.1)) F :=
        C.succStageChain k Γ ho j
       (Cj.restrictLTBlockChain k Γ
        (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ)

theorem PositiveIioCoherentChainAtBelow.limitPrefixCompatibleWithSuccStage_of_blockPrefix
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (hcompat : C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep) :
    C.limitPrefixCompatibleWithSuccStage k Γ ho hsep := by
  intro i j hij
  rw [C.restrictedPrefix_eq_restrictLTBlockChain k Γ ho hij]
  exact hcompat hij

theorem PositiveIioCoherentChainAtBelow.limitPrefixCompatibleWithSuccStage_of_targetBranches
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (hlimit :
      ∀ {i j : Set.Iio o} (hij : i < j), Order.IsSuccLimit j.1 →
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij)
    (hsucc :
      ∀ {i j : Set.Iio o} (hij : i < j), j.1 ∈ Set.range Order.succ →
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij) :
    C.limitPrefixCompatibleWithSuccStage k Γ ho hsep := by
  intro i j hij
  rcases Ordinal.zero_or_succ_or_isSuccLimit j.1 with hzero | hsucc' | hjlim
  · have hjpos : (0 : Ordinal) < j.1 :=
      lt_of_le_of_lt bot_le (show i.1 < j.1 from hij)
    rw [hzero] at hjpos
    exact False.elim ((lt_irrefl (0 : Ordinal)) hjpos)
  · exact hsucc hij hsucc'
  · exact hlimit hij hjlim

theorem PositiveIioCoherentChainAtBelow.limitBlockPrefixCompatibleWithSuccStage_of_prefix
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (hcompat : C.limitPrefixCompatibleWithSuccStage k Γ ho hsep) :
    C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep := by
  intro i j hij
  rw [← C.restrictedPrefix_eq_restrictLTBlockChain k Γ ho hij]
  exact hcompat hij

theorem PositiveIioCoherentChainAtBelow.limitBlockPrefixCompatibleWithSuccStage_of_targetBranches
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsep : C.limitSeparated k Γ ho)
    (hlimit :
      ∀ {i j : Set.Iio o} (hij : i < j), Order.IsSuccLimit j.1 →
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij)
    (hsucc :
      ∀ {i j : Set.Iio o} (hij : i < j), j.1 ∈ Set.range Order.succ →
        C.limitPrefixDiffHahnSeriesLimit k Γ ho hsep i =
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hij) :
    C.limitBlockPrefixCompatibleWithSuccStage k Γ ho hsep := by
  exact C.limitBlockPrefixCompatibleWithSuccStage_of_prefix k Γ ho hsep
    (C.limitPrefixCompatibleWithSuccStage_of_targetBranches k Γ ho hsep hlimit hsucc)

end HahnField

end

end HahnKaplanskyRealClosedness
