/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Components.LimitStep

/-!
# Recursion endpoints for positive limit chains
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

theorem PositiveIioCoherentChain.succOfNoRoot_apply_limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} (hpos : (0 : Ordinal) < o) (hlim : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ o hpos F) :
    C.succOfNoRoot k Γ hpos hsmall hunit hno =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       C.limitExtend k Γ hlim hsmall hunit hno) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  unfold PositiveIioCoherentChain.succOfNoRoot
  have hnot : ¬ o ∈ Set.range Order.succ := by
    rintro ⟨p, hp⟩
    exact hlim.succ_ne p hp
  rw [dif_neg hnot]

@[simp]
theorem PositiveIioCoherentChain.succOfNoRoot_apply_limit_state_bot_source
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} (hpos : (0 : Ordinal) < o) (hlim : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ o hpos F) :
    (letI : OrderBot (Set.Iio (Order.succ o)) :=
      ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
     ((C.succOfNoRoot k Γ hpos hsmall hunit hno).state
        (⊥ : Set.Iio (Order.succ o))).source) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       (C.state (⊥ : Set.Iio o)).source) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  rw [PositiveIioCoherentChain.succOfNoRoot_apply_limit
    k Γ hpos hlim hsmall hunit hno C]
  exact C.limitExtend_state_bot_source k Γ hlim hsmall hunit hno

theorem PositiveIioCoherentChain.succOfNoRoot_apply_succ_state_bot_source
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F) :
    ((C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p))
        hsmall hunit hno).state
        (⊥ : Set.Iio (Order.succ (Order.succ p)))).source =
      (C.state (⊥ : Set.Iio (Order.succ p))).source := by
  classical
  unfold PositiveIioCoherentChain.succOfNoRoot
  have hsucc : Order.succ p ∈ Set.range Order.succ := ⟨p, rfl⟩
  rw [dif_pos hsucc]
  simp [OneClusterCoherentBlockChain.succExtend_state_bot_source,
    PositiveIioCoherentChain.cast_state_bot_source']

theorem PositiveIioCoherentChain.succOfNoRoot_block_emb_next_val_of_limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} (hpos : (0 : Ordinal) < o) (hlim : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (i : Set.Iio o) :
    (((C.succOfNoRoot k Γ hpos hsmall hunit hno).block
        (ordinalIioSuccEmb o i)).next.val k Γ) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       (C.block i).next.val k Γ) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  rw [PositiveIioCoherentChain.succOfNoRoot_apply_limit
    k Γ hpos hlim hsmall hunit hno C]
  exact C.limitExtend_block_emb_next_val k Γ hlim hsmall hunit hno i

theorem PositiveIioCoherentChain.succOfNoRoot_restrictTop_diffHahnSeriesLimit_of_limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} (hpos : (0 : Ordinal) < o) (hlim : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ o hpos F) :
    (((C.succOfNoRoot k Γ hpos hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccOrderTop o).top).diffHahnSeriesLimit k Γ) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  rw [PositiveIioCoherentChain.succOfNoRoot_apply_limit
    k Γ hpos hlim hsmall hunit hno C]
  exact C.limitExtend_restrictTop_diffHahnSeriesLimit k Γ hlim hsmall hunit hno

theorem PositiveIioCoherentChain.succOfNoRoot_restrictEmb_diffHahnSeriesLimit_of_limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal} (hpos : (0 : Ordinal) < o) (hlim : Order.IsSuccLimit o)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ o hpos F)
    (i : Set.Iio o) :
    (((C.succOfNoRoot k Γ hpos hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb o i)).diffHahnSeriesLimit k Γ) =
      (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
       ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ)) := by
  classical
  let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
  rw [PositiveIioCoherentChain.succOfNoRoot_apply_limit
    k Γ hpos hlim hsmall hunit hno C]
  exact C.limitExtend_restrictEmb_diffHahnSeriesLimit k Γ hlim hsmall hunit hno i

theorem PositiveIioCoherentChain.succOfNoRoot_restrictEmb_diffHahnSeriesLimit_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F)
    (i : Set.Iio (Order.succ p)) :
    (((C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p))
        hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ p) i)).diffHahnSeriesLimit k Γ) =
      (letI : OrderBot (Set.Iio (Order.succ p)) :=
        ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ p))
       ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ)) := by
  classical
  unfold PositiveIioCoherentChain.succOfNoRoot
  have hsucc : Order.succ p ∈ Set.range Order.succ := ⟨p, rfl⟩
  rw [dif_pos hsucc]
  dsimp only
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  exact PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_restrictEmb_diffHahnSeriesLimit
    (k := k) (Γ := Γ)
    (p := p) (q := (Order.succ p).pred) (r := (Order.succ p).pred + 1 + 1)
    (hp := lt_of_le_of_lt bot_le (Order.lt_succ p))
    (hq := h8) (hr := h4)
    (hqp := by
      change Ordinal.pred (p + 1) = p
      exact Ordinal.pred_add_one p)
    (hrp := by
      change Ordinal.pred (p + 1) + 1 + 1 = Order.succ (Order.succ p)
      rw [Ordinal.pred_add_one]
      rfl)
    hsmall hunit hno C h13 h11 h7 h5 i

theorem PositiveIioCoherentChain.succOfNoRoot_restrictEmb_top_diffHahnSeriesLimit_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F) :
    (((C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p))
        hsmall hunit hno).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ p) (ordinalIioSuccOrderTop p).top)).diffHahnSeriesLimit
          k Γ) =
      (letI : OrderBot (Set.Iio (Order.succ p)) :=
        ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ p))
       ((C.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccOrderTop p).top).diffHahnSeriesLimit k Γ)) := by
  exact PositiveIioCoherentChain.succOfNoRoot_restrictEmb_diffHahnSeriesLimit_of_succ
    (k := k) (Γ := Γ) hsmall hunit hno C (ordinalIioSuccOrderTop p).top

theorem PositiveIioCoherentChain.succOfNoRoot_block_emb_top_next_val_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F) :
    (((C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p))
        hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ p) (ordinalIioSuccOrderTop p).top)).next.val k Γ) =
      (C.succEndpointTopBlock k Γ).next.val k Γ := by
  classical
  unfold PositiveIioCoherentChain.succOfNoRoot
  have hsucc : Order.succ p ∈ Set.range Order.succ := ⟨p, rfl⟩
  rw [dif_pos hsucc]
  dsimp only
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  exact PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_block_emb_top_next_val
    (k := k) (Γ := Γ)
    (p := p) (q := (Order.succ p).pred) (r := (Order.succ p).pred + 1 + 1)
    (hp := h11) (hq := h8) (hr := h3)
    (hqp := by
      change Ordinal.pred (p + 1) = p
      exact Ordinal.pred_add_one p)
    (hrp := by
      change Ordinal.pred (p + 1) + 1 + 1 = Order.succ (Order.succ p)
      rw [Ordinal.pred_add_one]
      rfl)
    hsmall hunit hno C h12 h10 h6 h4

theorem PositiveIioCoherentChain.succOfNoRoot_block_emb_bot_next_val_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F) :
    (((C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p))
        hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ p) (⊥ : Set.Iio (Order.succ p)))).next.val k Γ) =
      (C.block (⊥ : Set.Iio (Order.succ p))).next.val k Γ := by
  classical
  unfold PositiveIioCoherentChain.succOfNoRoot
  have hsucc : Order.succ p ∈ Set.range Order.succ := ⟨p, rfl⟩
  rw [dif_pos hsucc]
  dsimp only
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  exact PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_block_emb_next_val
    (k := k) (Γ := Γ)
    (p := p) (q := (Order.succ p).pred) (r := (Order.succ p).pred + 1 + 1)
    (hp := h11) (hq := h8) (hr := h3)
    (hqp := by
      change Ordinal.pred (p + 1) = p
      exact Ordinal.pred_add_one p)
    (hrp := by
      change Ordinal.pred (p + 1) + 1 + 1 = Order.succ (Order.succ p)
      rw [Ordinal.pred_add_one]
      rfl)
    hsmall hunit hno C h12 h10 h6 h4 (⊥ : Set.Iio (Order.succ p))

theorem PositiveIioCoherentChain.succOfNoRoot_block_emb_next_val_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F)
    (i : Set.Iio (Order.succ p)) :
    (((C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p))
        hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ p) i)).next.val k Γ) =
      (C.block i).next.val k Γ := by
  classical
  unfold PositiveIioCoherentChain.succOfNoRoot
  have hsucc : Order.succ p ∈ Set.range Order.succ := ⟨p, rfl⟩
  rw [dif_pos hsucc]
  dsimp only
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  exact PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_block_emb_next_val
    (k := k) (Γ := Γ)
    (p := p) (q := (Order.succ p).pred) (r := (Order.succ p).pred + 1 + 1)
    (hp := h11) (hq := h8) (hr := h3)
    (hqp := by
      change Ordinal.pred (p + 1) = p
      exact Ordinal.pred_add_one p)
    (hrp := by
      change Ordinal.pred (p + 1) + 1 + 1 = Order.succ (Order.succ p)
      rw [Ordinal.pred_add_one]
      rfl)
    hsmall hunit hno C h12 h10 h6 h4 i

theorem PositiveIioCoherentChain.succOfNoRoot_block_emb_diffHahnSeries_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F)
    (i : Set.Iio (Order.succ p)) :
    (((C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p))
        hsmall hunit hno).block
        (ordinalIioSuccEmb (Order.succ p) i)).diffHahnSeries k Γ) =
      (C.block i).diffHahnSeries k Γ := by
  classical
  unfold PositiveIioCoherentChain.succOfNoRoot
  have hsucc : Order.succ p ∈ Set.range Order.succ := ⟨p, rfl⟩
  rw [dif_pos hsucc]
  dsimp only
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  exact PositiveIioCoherentChain.mpr_mp_succExtend_mpr_mp_block_emb_diffHahnSeries
    (k := k) (Γ := Γ)
    (p := p) (q := (Order.succ p).pred) (r := (Order.succ p).pred + 1 + 1)
    (hp := h11) (hq := h8) (hr := h3)
    (hqp := by
      change Ordinal.pred (p + 1) = p
      exact Ordinal.pred_add_one p)
    (hrp := by
      change Ordinal.pred (p + 1) + 1 + 1 = Order.succ (Order.succ p)
      rw [Ordinal.pred_add_one]
      rfl)
    hsmall hunit hno C h12 h10 h6 h4 i

theorem PositiveIioCoherentChain.succOfNoRoot_restrictTop_diffHahnSeriesLimit_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {p : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChain k Γ (Order.succ p)
      (lt_of_le_of_lt bot_le (Order.lt_succ p)) F) :
    (((C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p)) hsmall hunit hno)
      |>.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccOrderTop (Order.succ p)).top).diffHahnSeriesLimit k Γ) =
      C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
  let D := C.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ p)) hsmall hunit hno
  let top : Set.Iio (Order.succ (Order.succ p)) :=
    (ordinalIioSuccOrderTop (Order.succ p)).top
  rw [← D.restrictLTBlockChain_diffHahnSeriesLimit k Γ top]
  let R := D.restrictLTBlockChain k Γ top
  let P := C.toOneClusterBlockChain
  let E : Set.Iio top.1 ≃ Set.Iio (Order.succ p) := by
    dsimp [top]
    exact Equiv.refl _
  let sR := R.diffSummableFamily k Γ
  let sP := P.diffSummableFamily k Γ
  have heq : sR = HahnSeries.SummableFamily.Equiv E sP := by
    ext i
    dsimp [HahnSeries.SummableFamily.Equiv, sR, sP, R, P, D, top,
      PositiveIioCoherentChain.restrictLTBlockChain,
      OneClusterBlockChain.diffSummableFamily]
    dsimp [E]
    exact congrArg (fun s : HahnSeries Γ k => s.coeff _)
      (PositiveIioCoherentChain.succOfNoRoot_block_emb_diffHahnSeries_of_succ
        (k := k) (Γ := Γ) hsmall hunit hno C i)
  change sR.hsum = sP.hsum
  rw [heq, HahnSeries.SummableFamily.hsum_equiv]

universe u

noncomputable def OneClusterCoherentBlockChain.initialOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) :
    OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ (0 : Ordinal.{u}))) F := by
  classical
  letI : OrderBot (Set.Iio (Order.succ (0 : Ordinal.{u}))) :=
    ordinalIioSuccOrderBot (0 : Ordinal.{u})
  letI : Subsingleton (Set.Iio (Order.succ (0 : Ordinal.{u}))) :=
    ordinalIioSuccZero_subsingleton
  let S₀ : OneClusterState k Γ F :=
    oneClusterInitialStateOfNoRoot k Γ hno
  let B₀ : OneClusterBlockSuccessor k Γ S₀ :=
    oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno S₀
  let Cblock : OneClusterBlockChain k Γ (Set.Iio (Order.succ (0 : Ordinal.{u}))) F :=
    { state := fun _ => S₀
      block := fun _ => B₀
      separated := by
        intro i j hij
        have hji : i = j := Subsingleton.elim i j
        have hlt : i < i := by
          rwa [← hji] at hij
        exact False.elim ((lt_irrefl i) hlt) }
  refine
    { toOneClusterBlockChain := Cblock
      coherent_source := ?_ }
  intro i
  have hi : i = (⊥ : Set.Iio (Order.succ (0 : Ordinal.{u}))) := Subsingleton.elim i ⊥
  rw [hi]
  let _ : IsEmpty (Set.Iio (⊥ : Set.Iio (Order.succ (0 : Ordinal.{u})))) :=
    ⟨fun j => (not_lt_bot (show (j : Set.Iio (Order.succ (0 : Ordinal.{u}))) < ⊥ from j.2)).elim⟩
  have hright :
      ((Cblock.restrictLT k Γ (⊥ : Set.Iio (Order.succ (0 : Ordinal.{u})))).diffHahnSeriesLimit
          k Γ) = 0 :=
    OneClusterBlockChain.diffHahnSeriesLimit_eq_zero_of_isEmpty k Γ
      (Cblock.restrictLT k Γ (⊥ : Set.Iio (Order.succ (0 : Ordinal.{u}))))
  simp [Cblock, hright]

@[simp]
theorem OneClusterCoherentBlockChain.initialOfNoRoot_topState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) :
    ((OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno)
      |>.toOneClusterBlockChain.topState k Γ) =
      oneClusterInitialStateOfNoRoot k Γ hno := by
  unfold OneClusterCoherentBlockChain.initialOfNoRoot
  simp [OneClusterBlockChain.topState]

theorem OneClusterCoherentBlockChain.initialOfNoRoot_botSourceEq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) :
    OneClusterCoherentBlockChain.BotSourceEq k Γ
      (OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno)
      (oneClusterInitialStateOfNoRoot k Γ hno).source := by
  unfold OneClusterCoherentBlockChain.BotSourceEq
  unfold OneClusterCoherentBlockChain.initialOfNoRoot
  simp

@[simp]
theorem OneClusterCoherentBlockChain.initialOfNoRoot_topBlock_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) :
    ((((OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno)
      |>.toOneClusterBlockChain.topBlock k Γ).next.val k Γ)) =
      (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ := by
  unfold OneClusterCoherentBlockChain.initialOfNoRoot
  simp [OneClusterBlockChain.topBlock]

@[simp]
theorem OneClusterCoherentBlockChain.initialOfNoRoot_topBlock_diffHahnSeries
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) :
    (((OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno)
      |>.toOneClusterBlockChain.topBlock k Γ).diffHahnSeries k Γ) =
      (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ := by
  unfold OneClusterCoherentBlockChain.initialOfNoRoot
  change
    (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
      (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ =
    (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
      (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ
  rfl

theorem OneClusterCoherentBlockChain.initialOfNoRoot_botBlockNextValEq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) :
    OneClusterCoherentBlockChain.BotBlockNextValEq k Γ
      (OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno)
      ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) := by
  unfold OneClusterCoherentBlockChain.BotBlockNextValEq
  unfold OneClusterCoherentBlockChain.initialOfNoRoot
  simp

noncomputable def PositiveIioCoherentChainAt.succOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChainAt k Γ o F) :
    PositiveIioCoherentChainAt k Γ (Order.succ o) F := by
  classical
  intro _hsuccPos
  by_cases hpos : (0 : Ordinal) < o
  · exact (C hpos).succOfNoRoot k Γ hpos hsmall hunit hno
  · have hzero : o = 0 := le_antisymm (le_of_not_gt hpos) bot_le
    subst o
    exact OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno

@[simp]
theorem PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChainAt k Γ o F)
    (hpos : (0 : Ordinal) < o) (hsucc : (0 : Ordinal) < Order.succ o) :
    PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno C hsucc =
      (C hpos).succOfNoRoot k Γ hpos hsmall hunit hno := by
  unfold PositiveIioCoherentChainAt.succOfNoRoot
  simp [hpos]

@[simp]
theorem PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChainAt k Γ 0 F)
    (hsucc : (0 : Ordinal) < Order.succ (0 : Ordinal)) :
    PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno C hsucc =
      OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno := by
  unfold PositiveIioCoherentChainAt.succOfNoRoot
  simp

theorem PositiveIioCoherentChainAt.succOfNoRoot_botSourceEq_of_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChainAt k Γ o F)
    (hpos : (0 : Ordinal) < o)
    {s₀ : valuationSubring k Γ}
    (hC : C.BotSourceEq k Γ s₀) :
    (C.succOfNoRoot k Γ hsmall hunit hno).BotSourceEq k Γ s₀ := by
  intro hsucc
  rw [PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
    k Γ hsmall hunit hno C hpos hsucc]
  rcases Ordinal.zero_or_succ_or_isSuccLimit o with hzero | hsucc' | hlim
  · rw [hzero] at hpos
    exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
  · rcases hsucc' with ⟨p, hp⟩
    subst o
    unfold OneClusterCoherentBlockChain.BotSourceEq
    have hcanon : (0 : Ordinal) < Order.succ p :=
      lt_of_le_of_lt bot_le (Order.lt_succ p)
    have hsource :
        (((C hcanon).succOfNoRoot k Γ hcanon hsmall hunit hno).state
            (⊥ : Set.Iio (Order.succ (Order.succ p)))).source =
          (letI : OrderBot (Set.Iio (Order.succ p)) :=
            ordinalIioOrderBotOfPos hcanon
           ((C hcanon).state (⊥ : Set.Iio (Order.succ p))).source) := by
      exact PositiveIioCoherentChain.succOfNoRoot_apply_succ_state_bot_source
        k Γ hsmall hunit hno (C hcanon)
    rw [hsource]
    exact hC hcanon
  · unfold OneClusterCoherentBlockChain.BotSourceEq
    have hsource :
        (letI : OrderBot (Set.Iio (Order.succ o)) :=
          ordinalIioOrderBotOfPos (lt_of_le_of_lt bot_le (Order.lt_succ o))
         (((C hpos).succOfNoRoot k Γ hpos hsmall hunit hno).state
            (⊥ : Set.Iio (Order.succ o))).source) =
          (letI : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
           ((C hpos).state (⊥ : Set.Iio o)).source) := by
      exact PositiveIioCoherentChain.succOfNoRoot_apply_limit_state_bot_source
        k Γ hpos hlim hsmall hunit hno (C hpos)
    rw [hsource]
    exact hC hpos

theorem PositiveIioCoherentChainAt.succOfNoRoot_botBlockNextValEq_of_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : PositiveIioCoherentChainAt k Γ o F)
    (hpos : (0 : Ordinal) < o)
    {v₀ : Γ}
    (hC : C.BotBlockNextValEq k Γ v₀) :
    (C.succOfNoRoot k Γ hsmall hunit hno).BotBlockNextValEq k Γ v₀ := by
  intro hsucc
  rw [PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
    k Γ hsmall hunit hno C hpos hsucc]
  rcases Ordinal.zero_or_succ_or_isSuccLimit o with hzero | hsucc' | hlim
  · rw [hzero] at hpos
    exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
  · rcases hsucc' with ⟨p, hp⟩
    subst o
    have hcanon : (0 : Ordinal) < Order.succ p :=
      lt_of_le_of_lt bot_le (Order.lt_succ p)
    have hpos_eq : hpos = hcanon := Subsingleton.elim hpos hcanon
    cases hpos_eq
    unfold OneClusterCoherentBlockChain.BotBlockNextValEq
    calc
      (((C hpos).succOfNoRoot k Γ hpos hsmall hunit hno).block
          (⊥ : Set.Iio (Order.succ (Order.succ p)))).next.val k Γ
          =
        (((C hpos).succOfNoRoot k Γ hpos hsmall hunit hno).block
            (ordinalIioSuccEmb (Order.succ p)
              (⊥ : Set.Iio (Order.succ p)))).next.val k Γ := by
          rfl
      _ = ((C hpos).block (⊥ : Set.Iio (Order.succ p))).next.val k Γ := by
          exact PositiveIioCoherentChain.succOfNoRoot_block_emb_bot_next_val_of_succ
            (k := k) (Γ := Γ) hsmall hunit hno (C hpos)
      _ = v₀ := hC hpos
  · rw [PositiveIioCoherentChain.succOfNoRoot_apply_limit
      k Γ hpos hlim hsmall hunit hno (C hpos)]
    let _ : OrderBot (Set.Iio o) := ordinalIioOrderBotOfPos hpos
    exact OneClusterCoherentBlockChain.BotBlockNextValEq.limitExtend
      k Γ hlim hsmall hunit hno (C hpos) (hC hpos)

noncomputable def PositiveIioCoherentChainAt.recOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (limitStep :
      ∀ {o : Ordinal}, Order.IsSuccLimit o →
        PositiveIioCoherentChainAtBelow k Γ o F →
        PositiveIioCoherentChainAt k Γ o F)
    (o : Ordinal) :
    PositiveIioCoherentChainAt k Γ o F :=
  Ordinal.limitRecOn o
    (fun hpos => False.elim ((lt_irrefl (0 : Ordinal)) hpos))
    (fun o C => by
      simpa only [Order.succ_eq_add_one] using
        PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno C)
    (fun _ ho IH => limitStep ho (fun i => IH i.1 i.2))

noncomputable def PositiveIioCoherentChainAt.recBelowOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (limitStep :
      ∀ {o : Ordinal}, Order.IsSuccLimit o →
        PositiveIioCoherentChainAtBelow k Γ o F →
        PositiveIioCoherentChainAt k Γ o F)
    {o : Ordinal} (_ho : Order.IsSuccLimit o) :
    PositiveIioCoherentChainAtBelow k Γ o F :=
  fun i => PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep i.1

@[simp]
theorem PositiveIioCoherentChainAt.recOfNoRoot_add_one
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (limitStep :
      ∀ {o : Ordinal}, Order.IsSuccLimit o →
        PositiveIioCoherentChainAtBelow k Γ o F →
        PositiveIioCoherentChainAt k Γ o F)
    (o : Ordinal) :
  PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep (o + 1) =
      PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
        (PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep o) := by
  unfold PositiveIioCoherentChainAt.recOfNoRoot
  rw [Ordinal.limitRecOn_add_one]
  rfl

@[simp]
theorem PositiveIioCoherentChainAt.recOfNoRoot_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (limitStep :
      ∀ {o : Ordinal}, Order.IsSuccLimit o →
        PositiveIioCoherentChainAtBelow k Γ o F →
        PositiveIioCoherentChainAt k Γ o F)
    (o : Ordinal) :
  PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep (Order.succ o) =
      PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
        (PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep o) := by
  change
    PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep (o + 1) =
      PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
        (PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep o)
  exact PositiveIioCoherentChainAt.recOfNoRoot_add_one k Γ hsmall hunit hno limitStep o

@[simp]
theorem PositiveIioCoherentChainAt.recBelowOfNoRoot_succStageChain
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (limitStep :
      ∀ {o : Ordinal}, Order.IsSuccLimit o →
        PositiveIioCoherentChainAtBelow k Γ o F →
        PositiveIioCoherentChainAt k Γ o F)
    {o : Ordinal} (ho : Order.IsSuccLimit o) (i : Set.Iio o) :
    (PositiveIioCoherentChainAt.recBelowOfNoRoot k Γ hsmall hunit hno limitStep ho
      |>.succStageChain k Γ ho i) =
      (PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
        (PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep i.1))
        (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) := by
  unfold PositiveIioCoherentChainAtBelow.succStageChain
  simp [PositiveIioCoherentChainAt.recBelowOfNoRoot]

@[simp]
theorem PositiveIioCoherentChainAtBelow.succStageChain_of_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F) (i : Set.Iio o)
    (hsucc :
      C ⟨Order.succ i.1, ho.succ_lt i.2⟩ =
        PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (C i))
    (hi : (0 : Ordinal) < i.1) :
    C.succStageChain k Γ ho i =
      ((C i) hi).succOfNoRoot k Γ hi hsmall hunit hno := by
  unfold PositiveIioCoherentChainAtBelow.succStageChain
  rw [hsucc]
  exact PositiveIioCoherentChainAt.succOfNoRoot_apply_of_pos
    k Γ hsmall hunit hno (C i) hi (lt_of_le_of_lt bot_le (Order.lt_succ i.1))

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefix_top_of_succIndex
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
    {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
    (hi : i.1 = p) :
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
        change i.1 < Order.succ p
        rw [hi]
        exact Order.lt_succ p) =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  classical
  subst p
  let hij : i < (⟨Order.succ i.1, hp⟩ : Set.Iio o) := by
    change i.1 < Order.succ i.1
    exact Order.lt_succ i.1
  unfold PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
  unfold PositiveIioCoherentChainAtBelow.succStagePrefixDiffHahnSeriesLimit
  rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
    (k := k) (Γ := Γ) hsmall hunit hno ho C
    (⟨Order.succ i.1, hp⟩ : Set.Iio o)
    (hsucc (ho.succ_lt hp))
    (lt_of_le_of_lt bot_le (Order.lt_succ i.1))]
  change
    (((C ⟨Order.succ i.1, hp⟩ (lt_of_le_of_lt bot_le (Order.lt_succ i.1)))
      |>.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) hsmall hunit hno)
      |>.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ =
      (let endpoint := (ordinalIioSuccOrderTop i.1).top
       ((PositiveIioCoherentChainAtBelow.succStageChain k Γ ho C i).toOneClusterBlockChain
        |>.restrictLT k Γ endpoint).diffHahnSeriesLimit k Γ)
  calc
    (((C ⟨Order.succ i.1, hp⟩ (lt_of_le_of_lt bot_le (Order.lt_succ i.1)))
      |>.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) hsmall hunit hno)
      |>.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ
        =
      (((C ⟨Order.succ i.1, hp⟩ (lt_of_le_of_lt bot_le (Order.lt_succ i.1)))
      |>.succOfNoRoot k Γ (lt_of_le_of_lt bot_le (Order.lt_succ i.1)) hsmall hunit hno)
      |>.toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ i.1) (ordinalIioSuccOrderTop i.1).top)).diffHahnSeriesLimit
        k Γ := by
        exact OneClusterBlockChain.restrictLT_diffHahnSeriesLimit_congr k Γ _
          (ordinalIioSuccTopEmbOfLt_eq_succEmb_top hij rfl)
    _ =
      (((C ⟨Order.succ i.1, hp⟩ (lt_of_le_of_lt bot_le (Order.lt_succ i.1)))
        |>.toOneClusterBlockChain.restrictLT k Γ (ordinalIioSuccOrderTop i.1).top)
        |>.diffHahnSeriesLimit k Γ) := by
        exact PositiveIioCoherentChain.succOfNoRoot_restrictEmb_top_diffHahnSeriesLimit_of_succ
          (k := k) (Γ := Γ) hsmall hunit hno
          (C ⟨Order.succ i.1, hp⟩ (lt_of_le_of_lt bot_le (Order.lt_succ i.1)))
    _ =
      (let endpoint := (ordinalIioSuccOrderTop i.1).top
       ((PositiveIioCoherentChainAtBelow.succStageChain k Γ ho C i).toOneClusterBlockChain
        |>.restrictLT k Γ endpoint).diffHahnSeriesLimit k Γ) := by
        rfl

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefix_pred_of_succSuccIndex
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
      ∀ {i : Set.Iio o} (hi : i.1 < q),
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
          (show i < (⟨Order.succ q,
              (Order.lt_succ (Order.succ q)).trans hp⟩ : Set.Iio o) from by
            exact hi.trans (Order.lt_succ q)) =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho i)
    {i : Set.Iio o} (hi : i.1 < q) :
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o) from by
        exact (hi.trans (Order.lt_succ q)).trans (Order.lt_succ (Order.succ q))) =
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
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
  have hjpos : (0 : Ordinal) < j.1 := by
    change (0 : Ordinal) < Order.succ (Order.succ q)
    exact ((lt_of_le_of_lt bot_le hi).trans (Order.lt_succ q)).trans
      (Order.lt_succ (Order.succ q))
  unfold PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
  calc
    (((C.succStageChain k Γ ho j).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ)
        =
      (((C.succStageChain k Γ ho j).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ (Order.succ q))
          (ordinalIioSuccTopEmbOfLt hijpred))).diffHahnSeriesLimit k Γ) := by
        exact OneClusterBlockChain.restrictLT_diffHahnSeriesLimit_congr k Γ _
          (ordinalIioSuccTopEmbOfLt_eq_succEmb hij)
    _ =
      (((C j hjpos).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccTopEmbOfLt hijpred)).diffHahnSeriesLimit k Γ) := by
        rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
          (k := k) (Γ := Γ) hsmall hunit hno ho C j
          (hsucc (ho.succ_lt j.2)) hjpos]
        exact PositiveIioCoherentChain.succOfNoRoot_restrictEmb_diffHahnSeriesLimit_of_succ
          (k := k) (Γ := Γ) hsmall hunit hno (C j hjpos)
          (ordinalIioSuccTopEmbOfLt hijpred)
    _ =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
        change
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hijpred =
            C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
        exact hpred hi

theorem PositiveIioCoherentChainAtBelow.succStageRestrictedPrefix_top_of_succSuccIndex
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
    {i : Set.Iio o} (hi : i.1 = q) :
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o) from by
        change i.1 < Order.succ (Order.succ q)
        rw [hi]
        exact (Order.lt_succ q).trans (Order.lt_succ (Order.succ q))) =
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  classical
  let j : Set.Iio o := ⟨Order.succ (Order.succ q), hp⟩
  let jpred : Set.Iio o :=
    ⟨Order.succ q, (Order.lt_succ (Order.succ q)).trans hp⟩
  let hij : i < j := by
    change i.1 < Order.succ (Order.succ q)
    rw [hi]
    exact (Order.lt_succ q).trans (Order.lt_succ (Order.succ q))
  let hijpred : i < jpred := by
    change i.1 < Order.succ q
    rw [hi]
    exact Order.lt_succ q
  have hjpos : (0 : Ordinal) < j.1 := by
    change (0 : Ordinal) < Order.succ (Order.succ q)
    exact lt_of_le_of_lt bot_le ((Order.lt_succ q).trans (Order.lt_succ (Order.succ q)))
  unfold PositiveIioCoherentChainAtBelow.succStageRestrictedPrefixDiffHahnSeriesLimit
  calc
    (((C.succStageChain k Γ ho j).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccTopEmbOfLt hij)).diffHahnSeriesLimit k Γ)
        =
      (((C.succStageChain k Γ ho j).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccEmb (Order.succ (Order.succ q))
          (ordinalIioSuccTopEmbOfLt hijpred))).diffHahnSeriesLimit k Γ) := by
        exact OneClusterBlockChain.restrictLT_diffHahnSeriesLimit_congr k Γ _
          (ordinalIioSuccTopEmbOfLt_eq_succEmb hij)
    _ =
      (((C j hjpos).toOneClusterBlockChain.restrictLT k Γ
        (ordinalIioSuccTopEmbOfLt hijpred)).diffHahnSeriesLimit k Γ) := by
        rw [PositiveIioCoherentChainAtBelow.succStageChain_of_pos
          (k := k) (Γ := Γ) hsmall hunit hno ho C j
          (hsucc (ho.succ_lt hp)) hjpos]
        exact PositiveIioCoherentChain.succOfNoRoot_restrictEmb_diffHahnSeriesLimit_of_succ
          (k := k) (Γ := Γ) hsmall hunit hno (C j hjpos)
          (ordinalIioSuccTopEmbOfLt hijpred)
    _ =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
        change
          C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho hijpred =
            C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
        exact C.succStageRestrictedPrefix_top_of_succIndex
          k Γ hsmall hunit hno ho hsucc hi

theorem PositiveIioCoherentChainAtBelow.restrictedPrefix_of_limitIndex_of_limitStepAt
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (limitStep :
      ∀ {o : Ordinal}, Order.IsSuccLimit o →
        PositiveIioCoherentChainAtBelow k Γ o F →
        PositiveIioCoherentChainAt k Γ o F)
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩))
    {i j : Set.Iio o} (hij : i < j) (_hi : (0 : Ordinal) < i.1)
    (hj : Order.IsSuccLimit j.1)
    (hsepJ :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      Cj.limitSeparated k Γ hj)
    (hlimitAt :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      C j = limitStep hj Cj)
    (hlimitStepAt :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      ∀ (hpos : (0 : Ordinal) < j.1) (r : Set.Iio j.1),
        (letI : OrderBot (Set.Iio j.1) := ordinalIioOrderBotOfPos hpos
         (((limitStep hj Cj) hpos).toOneClusterBlockChain.restrictLT
            k Γ r).diffHahnSeriesLimit k Γ) =
          ((Cj.limitBlockChain k Γ hj hsepJ |>.restrictLT k Γ r)
            |>.diffHahnSeriesLimit k Γ)) :
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
       (((limitStep hj Cj) hjpos).toOneClusterBlockChain.restrictLT k Γ ij)
        |>.diffHahnSeriesLimit k Γ) := by
        dsimp [Cj] at hlimitAt
        rw [hlimitAt]
    _ =
      (let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
       (Cj.limitBlockChain k Γ hj hsepJ |>.restrictLT k Γ ij)
        |>.diffHahnSeriesLimit k Γ) := by
        exact hlimitStepAt hjpos ij

theorem PositiveIioCoherentChainAtBelow.stageLimit_of_prefixFields
    {F : Polynomial (valuationSubring k Γ)}
    {o : Ordinal} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    {i j : Set.Iio o} (hij : i < j) (_hi : (0 : Ordinal) < i.1)
    (hj : Order.IsSuccLimit j.1)
    (hsepJ :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      Cj.limitSeparated k Γ hj)
    (hlimitPrefix :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      Cj.limitPrefixCompatibleWithSuccStage k Γ hj hsepJ)
    (hstagePrefix :
      let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
      Cj.succStageRestrictedPrefixCompatible k Γ hj) :
      (let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
        fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
       (Cj.limitBlockChain k Γ hj hsepJ |>.restrictLT k Γ
        (⟨i.1, show i.1 < j.1 from hij⟩ : Set.Iio j.1)).diffHahnSeriesLimit k Γ) =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
  let ij : Set.Iio j.1 := ⟨i.1, show i.1 < j.1 from hij⟩
  let l : Set.Iio j.1 := ⟨Order.succ i.1, hj.succ_lt (show i.1 < j.1 from hij)⟩
  have hil : ij < l := by
    change i.1 < Order.succ i.1
    exact Order.lt_succ i.1
  have hlimitPrefix' :
      Cj.limitPrefixDiffHahnSeriesLimit k Γ hj hsepJ ij =
        Cj.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ hj hil := by
    exact hlimitPrefix hil
  have hstagePrefix' :
      Cj.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ hj hil =
        Cj.succStagePrefixDiffHahnSeriesLimit k Γ hj ij := by
    exact hstagePrefix hil
  calc
    (let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
      fun r => C ⟨r.1, (show r.1 < o from r.2.trans j.2)⟩
     (Cj.limitBlockChain k Γ hj hsepJ |>.restrictLT k Γ ij)
        |>.diffHahnSeriesLimit k Γ)
        = Cj.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ hj hil := by
        exact hlimitPrefix'
    _ = Cj.succStagePrefixDiffHahnSeriesLimit k Γ hj ij := hstagePrefix'
    _ = C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
        dsimp [PositiveIioCoherentChainAtBelow.succStagePrefixDiffHahnSeriesLimit, Cj, ij]

@[simp]
theorem PositiveIioCoherentChainAt.recBelowOfNoRoot_succStageChain_bot
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
    (PositiveIioCoherentChainAt.recBelowOfNoRoot k Γ hsmall hunit hno limitStep ho
      |>.succStageChain k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o)) =
      OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno := by
  rw [PositiveIioCoherentChainAt.recBelowOfNoRoot_succStageChain]
  exact PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
    k Γ hsmall hunit hno
    (PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep 0)
    (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal)))

@[simp]
theorem PositiveIioCoherentChainAt.externalRecursion_succStageChain_bot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    {o : Ordinal} (ho : Order.IsSuccLimit o) :
    PositiveIioCoherentChainAtBelow.succStageChain k Γ ho
      (fun i : Set.Iio o => R i.1 : PositiveIioCoherentChainAtBelow k Γ o F)
      (⟨0, ho.bot_lt⟩ : Set.Iio o) =
      OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno := by
  change R (Order.succ 0)
      (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal))) =
    OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno
  rw [hsucc 0]
  exact PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
    k Γ hsmall hunit hno (R 0)
    (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal)))

@[simp]
theorem PositiveIioCoherentChainAt.recBelowOfNoRoot_limitState_bot
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
    (PositiveIioCoherentChainAt.recBelowOfNoRoot k Γ hsmall hunit hno limitStep ho
      |>.limitState k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o)) =
      oneClusterInitialStateOfNoRoot k Γ hno := by
  unfold PositiveIioCoherentChainAtBelow.limitState
  rw [PositiveIioCoherentChainAt.recBelowOfNoRoot_succStageChain_bot
    k Γ hsmall hunit hno limitStep ho]
  exact OneClusterCoherentBlockChain.initialOfNoRoot_topState k Γ hsmall hunit hno

@[simp]
theorem PositiveIioCoherentChainAt.externalRecursion_limitBlock_bot_next_val
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    {o : Ordinal} (ho : Order.IsSuccLimit o) :
    ((PositiveIioCoherentChainAtBelow.limitBlock k Γ ho
      (fun i : Set.Iio o => R i.1 : PositiveIioCoherentChainAtBelow k Γ o F)
      (⟨0, ho.bot_lt⟩ : Set.Iio o)).next.val k Γ) =
      (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ := by
  calc
    ((PositiveIioCoherentChainAtBelow.limitBlock k Γ ho
      (fun i : Set.Iio o => R i.1 : PositiveIioCoherentChainAtBelow k Γ o F)
      (⟨0, ho.bot_lt⟩ : Set.Iio o)).next.val k Γ)
        =
      ((OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno
        |>.toOneClusterBlockChain.topBlock k Γ).next.val k Γ) := by
        unfold PositiveIioCoherentChainAtBelow.limitBlock
        exact PositiveIioCoherentChain.succEndpointTopBlock_next_val_eq_of_eq k Γ
          (PositiveIioCoherentChainAt.externalRecursion_succStageChain_bot
            k Γ hsmall hunit hno R hsucc ho)
    _ = (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ := by
        exact OneClusterCoherentBlockChain.initialOfNoRoot_topBlock_next_val
          k Γ hsmall hunit hno

theorem PositiveIioCoherentChainAt.externalRecursion_limitBlock_next_val_of_val_eq_zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F)
    (hsucc :
      ∀ o : Ordinal,
        R (Order.succ o) =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o))
    {o : Ordinal} (ho : Order.IsSuccLimit o) (i : Set.Iio o)
    (hi : (i : Ordinal) = 0) :
    ((PositiveIioCoherentChainAtBelow.limitBlock k Γ ho
      (fun i : Set.Iio o => R i.1 : PositiveIioCoherentChainAtBelow k Γ o F)
      i).next.val k Γ) =
      (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ := by
  have hbot : i = (⟨0, ho.bot_lt⟩ : Set.Iio o) := by
    apply Subtype.ext
    exact hi
  rw [hbot]
  exact PositiveIioCoherentChainAt.externalRecursion_limitBlock_bot_next_val
    k Γ hsmall hunit hno R hsucc ho

end HahnField

end

end HahnKaplanskyRealClosedness
