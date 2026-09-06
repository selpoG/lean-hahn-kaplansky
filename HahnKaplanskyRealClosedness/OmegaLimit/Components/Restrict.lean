/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Components.Compatible

/-!
# Restricted positive chain components
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

noncomputable def PositiveIioCoherentChain.restrictLT
    {o : Ordinal} {hpos : (0 : Ordinal) < o}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (i : Set.Iio o) (hi : (0 : Ordinal) < i.1) :
    PositiveIioCoherentChain k Γ i.1 hi F := by
  classical
  letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
  refine
    { toOneClusterBlockChain := C.restrictLTBlockChain k Γ i
      coherent_source := ?_ }
  intro j
  let E := ordinalIioSubtypeIioEquiv i
  let jO : Set.Iio o := ((E.symm j).1)
  have hbotO :
      ((E.symm (⊥ : Set.Iio i.1)).1 : Set.Iio o) = (⊥ : Set.Iio o) := by
    apply Subtype.ext
    rw [ordinalIioSubtypeIioEquiv_symm_apply_val]
    rw [ordinalIio_bot_val_eq_zero hi, ordinalIio_bot_val_eq_zero hpos]
  have hsource :
      (C.restrictLTBlockChain k Γ i).state j = C.state jO := by
    rfl
  have hbot_source :
      (C.restrictLTBlockChain k Γ i).state (⊥ : Set.Iio i.1) = C.state ⊥ := by
    change C.state ((E.symm (⊥ : Set.Iio i.1)).1) = C.state ⊥
    rw [hbotO]
  rw [hsource, hbot_source]
  have hprefix :
      (((C.restrictLTBlockChain k Γ i).restrictLT k Γ j).diffHahnSeriesLimit k Γ) =
        ((C.toOneClusterBlockChain.restrictLT k Γ jO).diffHahnSeriesLimit k Γ) := by
    let R := (C.restrictLTBlockChain k Γ i).restrictLT k Γ j
    let P := C.toOneClusterBlockChain.restrictLT k Γ jO
    let Ej : Set.Iio jO ≃ Set.Iio j :=
      {
      toFun l :=
        let hljO : (l.1 : Set.Iio o) < jO := l.2
        let hlj : l.1.1 < j.1 := by
          change l.1.1 < jO.1 at hljO
          simpa [jO, E] using hljO
        ⟨⟨l.1.1, hlj.trans j.2⟩, hlj⟩
      invFun l :=
        let hlj : l.1.1 < j.1 := l.2
        let hlo : l.1.1 < o := l.1.2.trans i.2
        ⟨⟨l.1.1, show l.1.1 ∈ Set.Iio o from hlo⟩,
          by
            change l.1.1 < jO.1
            simpa [jO, E] using hlj⟩
      left_inv _ := Subtype.ext (Subtype.ext rfl)
      right_inv _ := Subtype.ext rfl
      }
    let sR := R.diffSummableFamily k Γ
    let sP := P.diffSummableFamily k Γ
    have heq : sR = HahnSeries.SummableFamily.Equiv Ej sP := by
      ext l
      dsimp [HahnSeries.SummableFamily.Equiv, sR, sP, R, P,
        OneClusterBlockChain.diffSummableFamily, restrictLTBlockChain]
      rfl
    change sR.hsum = sP.hsum
    rw [heq, HahnSeries.SummableFamily.hsum_equiv]
  rw [hprefix]
  exact C.coherent_source jO

@[simp]
theorem PositiveIioCoherentChain.restrictLT_state
    {o : Ordinal} {hpos : (0 : Ordinal) < o}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (i : Set.Iio o) (hi : (0 : Ordinal) < i.1) (j : Set.Iio i.1) :
    (letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
     (C.restrictLT k Γ i hi).state j) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       C.state (((ordinalIioSubtypeIioEquiv i).symm j).1)) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  let _ : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
  rfl

theorem PositiveIioCoherentChain.restrictLT_block_next_val
    {o : Ordinal} {hpos : (0 : Ordinal) < o}
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (i : Set.Iio o) (hi : (0 : Ordinal) < i.1) (j : Set.Iio i.1) :
    (letI : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
     ((C.restrictLT k Γ i hi).block j).next.val k Γ) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       (C.block (((ordinalIioSubtypeIioEquiv i).symm j).1)).next.val k Γ) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  let _ : OrderBot (Set.Iio i.1) := ordinalIioOrderBotOfPos hi
  rfl

theorem PositiveIioCoherentChain.succExtend_restrictTop_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos : (0 : Ordinal) < Order.succ o}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ o) hpos F) :
    (letI : OrderBot (Set.Iio (Order.succ (Order.succ o))) :=
      ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ o)))
     (((C.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccOrderTop (Order.succ o)).top).diffHahnSeriesLimit k Γ)) =
      (letI : OrderBot (Set.Iio (Order.succ o)) := ordinalIioOrderBotOfPos hpos
       C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ) := by
  classical
  let _ : OrderBot (Set.Iio (Order.succ o)) := ordinalIioOrderBotOfPos hpos
  let _ : OrderBot (Set.Iio (Order.succ (Order.succ o))) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ o)))
  exact OneClusterCoherentBlockChain.succExtend_restrictTop_diffHahnSeriesLimit
    (k := k) (Γ := Γ) hsmall hunit hno C

theorem PositiveIioCoherentChain.succExtend_restrictEmb_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos : (0 : Ordinal) < Order.succ o}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ o) hpos F)
    (i : Set.Iio (Order.succ o)) :
    (letI : OrderBot (Set.Iio (Order.succ (Order.succ o))) :=
      ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ o)))
     (((C.succExtend k Γ hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ o) i)).diffHahnSeriesLimit k Γ)) =
      (letI : OrderBot (Set.Iio (Order.succ o)) := ordinalIioOrderBotOfPos hpos
       ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ)) := by
  classical
  let _ : OrderBot (Set.Iio (Order.succ o)) := ordinalIioOrderBotOfPos hpos
  let _ : OrderBot (Set.Iio (Order.succ (Order.succ o))) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ (Order.succ o)))
  exact OneClusterCoherentBlockChain.succExtend_restrictEmb_diffHahnSeriesLimit
    (k := k) (Γ := Γ) hsmall hunit hno C i

theorem PositiveIioCoherentChain.limitExtend_restrictTop_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos : (0 : Ordinal) < o}
    (hlim : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ o hpos F) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     letI : OrderBot (Set.Iio (Order.succ o)) :=
      ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
     (((C.limitExtend k Γ hlim hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccOrderTop o).top).diffHahnSeriesLimit k Γ)) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  let _ : OrderBot (Set.Iio (Order.succ o)) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
  exact OneClusterCoherentBlockChain.limitExtend_toBlockChain_restrictTop_diffHahnSeriesLimit
    (k := k) (Γ := Γ) hlim hsmall hunit hno C

theorem PositiveIioCoherentChain.limitExtend_restrictEmb_diffHahnSeriesLimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} {hpos : (0 : Ordinal) < o}
    (hlim : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (i : Set.Iio o) :
    (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
     letI : OrderBot (Set.Iio (Order.succ o)) :=
      ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
     (((C.limitExtend k Γ hlim hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb o i)).diffHahnSeriesLimit k Γ)) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ)) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  let _ : OrderBot (Set.Iio (Order.succ o)) :=
    ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
  exact OneClusterCoherentBlockChain.limitExtend_toBlockChain_restrictEmb_diffHahnSeriesLimit
    (k := k) (Γ := Γ) hlim hsmall hunit hno C i

def PositiveIioCoherentChainAtBelow.succStageRestrictedTopNextVal
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) : Γ :=
  let endpoint := ordinalIioSuccEndpointEmbOfLt hij
  let hi : (0 : Ordinal) < endpoint.1 := by
    rw [ordinalIioSuccEndpointEmbOfLt_val]
    exact lt_of_le_of_lt bot_le (Order.lt_succ i.1)
  letI : OrderBot (Set.Iio endpoint.1) := ordinalIioOrderBotOfPos hi
  (((C.succStageChain k Γ ho j).restrictLT k Γ endpoint hi).block
    (ordinalIioSuccOrderTop i.1).top).next.val k Γ

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedTopNextVal_eq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) :
    C.succStageRestrictedTopNextVal k Γ ho hij =
      ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ := by
  let endpoint := ordinalIioSuccEndpointEmbOfLt hij
  let hi : (0 : Ordinal) < endpoint.1 := by
    rw [ordinalIioSuccEndpointEmbOfLt_val]
    exact lt_of_le_of_lt bot_le (Order.lt_succ i.1)
  let _ : OrderBot (Set.Iio endpoint.1) := ordinalIioOrderBotOfPos hi
  have hproj :=
    (C.succStageChain k Γ ho j).restrictLT_block_next_val k Γ endpoint
      hi (ordinalIioSuccOrderTop i.1).top
  unfold succStageRestrictedTopNextVal
  simp only
  rw [hproj]
  have hidx :
      (((ordinalIioSubtypeIioEquiv endpoint).symm
          (ordinalIioSuccOrderTop i.1).top : Set.Iio endpoint) :
          Set.Iio (Order.succ j.1)) =
        ordinalIioSuccTopEmbOfLt hij := by
    exact ordinalIioSubtypeIioEquiv_symm_top_succEndpointEmbOfLt hij
  rw [hidx]

def PositiveIioCoherentChainAtBelow.succStageNextValCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j),
    (C.limitBlock k Γ ho i).next.val k Γ =
      C.succStageRestrictedTopNextVal k Γ ho hij

def PositiveIioCoherentChainAtBelow.succStagePrefixTopNextValCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j),
    C.succStageRestrictedTopNextVal k Γ ho hij =
      (C.limitBlock k Γ ho i).next.val k Γ

def PositiveIioCoherentChainAtBelow.succStageTopNextValProjectionCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j),
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
      (C.limitBlock k Γ ho i).next.val k Γ

def PositiveIioCoherentChainAtBelow.succStageBotBlockNextValEq
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (v₀ : Γ) : Prop :=
  ∀ i : Set.Iio o,
    (letI : OrderBot (Set.Iio (Order.succ i.1)) :=
      ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ i.1))
     ((C.succStageChain k Γ ho i).block
        (⊥ : Set.Iio (Order.succ i.1))).next.val k Γ) = v₀

theorem PositiveIioCoherentChainAtBelow.succStageTopNextValProjectionCompatible_bot
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {v₀ : Γ}
    (hstage : C.succStageBotBlockNextValEq k Γ ho v₀)
    (hlimit :
      ∀ i : Set.Iio o, (i : Ordinal) = 0 →
        (C.limitBlock k Γ ho i).next.val k Γ = v₀)
    {i j : Set.Iio o} (hij : i < j) (hi : (i : Ordinal) = 0) :
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
      (C.limitBlock k Γ ho i).next.val k Γ := by
  rw [ordinalIioSuccTopEmbOfLt_eq_bot_of_val_eq_zero hij hi]
  rw [hstage j, hlimit i hi]

def PositiveIioCoherentChainAtBelow.succStageTopNextValProjectionCompatiblePositive
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F) : Prop :=
  ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
    ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
      (C.limitBlock k Γ ho i).next.val k Γ

theorem PositiveIioCoherentChainAtBelow.succStageTopNextValProjectionPositive_of_targetBranches
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hlimit :
      ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
        Order.IsSuccLimit j.1 →
          ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
            (C.limitBlock k Γ ho i).next.val k Γ)
    (hsucc :
      ∀ {i j : Set.Iio o} (hij : i < j), (0 : Ordinal) < i.1 →
        j.1 ∈ Set.range Order.succ →
          ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
            (C.limitBlock k Γ ho i).next.val k Γ) :
    C.succStageTopNextValProjectionCompatiblePositive k Γ ho := by
  intro i j hij hi
  rcases Ordinal.zero_or_succ_or_isSuccLimit j.1 with hzero | hsucc' | hjlim
  · have hjpos : (0 : Ordinal) < j.1 := lt_trans hi hij
    rw [hzero] at hjpos
    exact False.elim ((lt_irrefl (0 : Ordinal)) hjpos)
  · exact hsucc hij hi hsucc'
  · exact hlimit hij hi hjlim

theorem PositiveIioCoherentChainAtBelow.succStageTopNextValProjectionCompatible_of_bot_positive
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hbot :
      ∀ {i j : Set.Iio o} (hij : i < j), (i : Ordinal) = 0 →
        ((C.succStageChain k Γ ho j).block (ordinalIioSuccTopEmbOfLt hij)).next.val k Γ =
          (C.limitBlock k Γ ho i).next.val k Γ)
    (hpos : C.succStageTopNextValProjectionCompatiblePositive k Γ ho) :
    C.succStageTopNextValProjectionCompatible k Γ ho := by
  intro i j hij
  rcases eq_or_lt_of_le (bot_le : (0 : Ordinal) ≤ i.1) with hi | hi
  · exact hbot hij hi.symm
  · exact hpos hij hi

theorem PositiveIioCoherentChainAtBelow.prefixTopNextValCompatible_of_projection
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageTopNextValProjectionCompatible k Γ ho) :
    C.succStagePrefixTopNextValCompatible k Γ ho := by
  intro i j hij
  rw [C.succStageRestrictedTopNextVal_eq k Γ ho hij]
  exact hcompat hij

theorem PositiveIioCoherentChainAtBelow.projectionNextValCompatible_of_prefixTop
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStagePrefixTopNextValCompatible k Γ ho) :
    C.succStageTopNextValProjectionCompatible k Γ ho := by
  intro i j hij
  rw [← C.succStageRestrictedTopNextVal_eq k Γ ho hij]
  exact hcompat hij

theorem PositiveIioCoherentChainAtBelow.succStageNextValCompatible_of_prefixTop
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStagePrefixTopNextValCompatible k Γ ho) :
    C.succStageNextValCompatible k Γ ho := by
  intro i j hij
  exact (hcompat hij).symm

theorem PositiveIioCoherentChainAtBelow.prefixTopNextValCompatible_of_succStageNext
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageNextValCompatible k Γ ho) :
    C.succStagePrefixTopNextValCompatible k Γ ho := by
  intro i j hij
  exact (hcompat hij).symm

theorem PositiveIioCoherentChainAtBelow.projectionNextValCompatible_of_succStageNext
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageNextValCompatible k Γ ho) :
    C.succStageTopNextValProjectionCompatible k Γ ho :=
  C.projectionNextValCompatible_of_prefixTop k Γ ho
    (C.prefixTopNextValCompatible_of_succStageNext k Γ ho hcompat)

theorem PositiveIioCoherentChainAtBelow.limitNextValCompatible_of_succStageNextValCompatible
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hcompat : C.succStageNextValCompatible k Γ ho) :
    C.limitNextValCompatible k Γ ho := by
  intro i j hij
  rw [hcompat hij]
  exact C.succStageRestrictedTopNextVal_eq k Γ ho hij

end HahnField

end

end HahnKaplanskyRealClosedness
