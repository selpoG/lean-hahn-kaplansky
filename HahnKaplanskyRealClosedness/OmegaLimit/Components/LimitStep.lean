/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Components.Natural

/-!
# Positive component limit-step constructors
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Build the positive limit step directly from natural recursive component data. -/
noncomputable def PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho) :
    PositiveIioCoherentChainAt k Γ o F :=
  C.limitStepOfCompatible k Γ ho
    (C.limitCompatible_of_natural k Γ ho hcompat)

theorem PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_botSourceEq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho)
    {s₀ : valuationSubring k Γ}
    (hbot :
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBot ho
       (C.limitState k Γ ho ⊥).source) = s₀) :
    (C.limitStepOfNaturalComponents k Γ ho hcompat).BotSourceEq k Γ s₀ := by
  unfold PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents
  exact C.limitStepOfCompatible_botSourceEq k Γ ho
    (C.limitCompatible_of_natural k Γ ho hcompat) hbot

theorem PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_botBlockNextValEq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho)
    {v₀ : Γ}
    (hbot :
      ∀ i : Set.Iio o, (i : Ordinal) = 0 →
        (C.limitBlock k Γ ho i).next.val k Γ = v₀) :
    (C.limitStepOfNaturalComponents k Γ ho hcompat).BotBlockNextValEq k Γ v₀ := by
  unfold PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents
  exact C.limitStepOfCompatible_botBlockNextValEq k Γ ho
    (C.limitCompatible_of_natural k Γ ho hcompat) hbot

@[simp]
theorem PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_block_next_val
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho)
    (hpos : (0 : Ordinal) < o) (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (((C.limitStepOfNaturalComponents k Γ ho hcompat hpos).block i).next.val k Γ)) =
      (C.limitBlock k Γ ho i).next.val k Γ := by
  unfold PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents
  exact C.limitStepOfCompatible_block_next_val k Γ ho
    (C.limitCompatible_of_natural k Γ ho hcompat) hpos i

theorem PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_restrictLT_sep
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho)
    (hsep : C.limitSeparated k Γ ho)
    (hpos : (0 : Ordinal) < o) (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (((C.limitStepOfNaturalComponents k Γ ho hcompat hpos).toOneClusterBlockChain.restrictLT
        k Γ i).diffHahnSeriesLimit k Γ)) =
      ((C.limitBlockChain k Γ ho hsep |>.restrictLT k Γ i)
        |>.diffHahnSeriesLimit k Γ) := by
  unfold PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents
  exact C.limitStepOfCompatible_restrictLT_diffHahnSeriesLimit_sep k Γ ho
    (C.limitCompatible_of_natural k Γ ho hcompat) hsep hpos i

theorem PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_diffHahnSeriesLimit_sep
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.NaturalComponents k Γ ho)
    (hsep : C.limitSeparated k Γ ho)
    (hpos : (0 : Ordinal) < o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     (C.limitStepOfNaturalComponents k Γ ho hcompat hpos).toOneClusterBlockChain
        |>.diffHahnSeriesLimit k Γ) =
      (C.limitBlockChain k Γ ho hsep |>.diffHahnSeriesLimit k Γ) := by
  unfold PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents
  exact C.limitStepOfCompatible_diffHahnSeriesLimit_sep k Γ ho
    (C.limitCompatible_of_natural k Γ ho hcompat) hsep hpos

/-- Natural-component limit steps are invariant under equality of the below-chain and proof
irrelevance of the component proof. -/
theorem PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_congr
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    {C D : PositiveIioCoherentChainAtBelow k Γ o F}
    (hCD : C = D)
    (hC : C.NaturalComponents k Γ ho)
    (hD : D.NaturalComponents k Γ ho) :
    C.limitStepOfNaturalComponents k Γ ho hC =
      D.limitStepOfNaturalComponents k Γ ho hD := by
  cases hCD
  have hproof : hC = hD := Subsingleton.elim _ _
  cases hproof
  rfl

noncomputable def PositiveIioCoherentChain.succOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} (hpos : (0 : Ordinal) < o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ o hpos F) :
    PositiveIioCoherentChain k Γ (Order.succ o)
      (lt_of_le_of_lt bot_le (Order.lt_succ o)) F := by
  classical
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  letI : OrderBot (Set.Iio (Order.succ o)) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
  by_cases hsucc : o ∈ Set.range Order.succ
  · let p : Ordinal := Ordinal.pred o
    have hp : Order.succ p = o := by
      dsimp [p]
      rcases hsucc with ⟨q, hq⟩
      rw [← hq]
      have hpred : (Order.succ q).pred = q := by
        change Ordinal.pred (q + 1) = q
        exact Ordinal.pred_add_one q
      rw [hpred]
    let hp_pos : (0 : Ordinal) < Order.succ p := lt_of_le_of_lt bot_le (Order.lt_succ p)
    let C' : PositiveIioCoherentChain k Γ (Order.succ p) hp_pos F := by
      simpa [← hp] using C
    have hresult :
        PositiveIioCoherentChain k Γ (Order.succ (Order.succ p))
      (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ p))) F :=
      C'.succExtend k Γ hsmall hunit hno
    simpa [← hp] using hresult
  · have hlim : Order.IsSuccLimit o := by
      exact ordinal_isSuccLimit_of_pos_not_succ hpos hsucc
    exact C.limitExtend k Γ hlim hsmall hunit hno

end HahnField

end

end HahnKaplanskyRealClosedness
