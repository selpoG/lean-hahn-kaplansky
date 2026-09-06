/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.SimpleCluster.Omega
import Mathlib.Order.Fin.Basic
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Omega-limit bookkeeping for simple-cluster block chains

This file contains the omega-chain limit-stage bookkeeping that is not needed by the core
simple-cluster construction in `SimpleCluster`.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

def hartogsOrdinal (α : Type*) : Ordinal :=
  (Order.succ (Cardinal.mk α)).ord

theorem hartogsOrdinal_pos (α : Type*) : (0 : Ordinal) < hartogsOrdinal α := by
  by_contra hnot
  have hzero : hartogsOrdinal α = 0 := le_antisymm (le_of_not_gt hnot) bot_le
  have hcard : Order.succ (Cardinal.mk α) = 0 :=
    Cardinal.ord_eq_zero.mp hzero
  have hlt : Cardinal.mk α < 0 := by
    simpa [hcard] using Order.lt_succ (Cardinal.mk α)
  exact (not_lt_of_ge (show (0 : Cardinal) ≤ Cardinal.mk α from zero_le)) hlt

@[reducible]
noncomputable def ordinalIioOrderBotOfPos {o : Ordinal} (h0 : (0 : Ordinal) < o) :
    OrderBot (Set.Iio o) where
  bot := ⟨⊥, h0⟩
  bot_le := fun i => show (⊥ : Ordinal) ≤ i.1 from bot_le

@[reducible]
noncomputable def ordinalIioOrderBot {o : Ordinal} (ho : Order.IsSuccLimit o) :
    OrderBot (Set.Iio o) :=
  ordinalIioOrderBotOfPos ho.bot_lt

theorem ordinalIio_forward_of_isSuccLimit {o : Ordinal}
    (ho : Order.IsSuccLimit o) :
    ∀ i : Set.Iio o, ∃ j : Set.Iio o, i < j := by
  intro i
  exact ⟨⟨Order.succ i.1, ho.succ_lt i.2⟩, Order.lt_succ i.1⟩

theorem ordinal_isSuccLimit_of_pos_not_succ {o : Ordinal}
    (hpos : (0 : Ordinal) < o) (hnot : ¬ o ∈ Set.range Order.succ) :
    Order.IsSuccLimit o := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit o with hzero | hsucc | hlim
  · rw [hzero] at hpos
    exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
  · exact False.elim (hnot hsucc)
  · exact hlim

@[reducible]
noncomputable def ordinalIioSuccOrderBot (o : Ordinal) :
    OrderBot (Set.Iio (Order.succ o)) where
  bot := ⟨⊥, lt_of_le_of_lt bot_le (Order.lt_succ o)⟩
  bot_le := fun i => show (⊥ : Ordinal) ≤ i.1 from bot_le

instance ordinalIioSuccInstOrderBot (o : Ordinal) :
    OrderBot (Set.Iio (Order.succ o)) :=
  ordinalIioSuccOrderBot o

@[reducible]
noncomputable def ordinalIioSuccOrderTop (o : Ordinal) :
    OrderTop (Set.Iio (Order.succ o)) where
  top := ⟨o, Order.lt_succ o⟩
  le_top := fun i => show i.1 ≤ o from by
    by_contra hle
    have hlt : o < i.1 := lt_of_not_ge hle
    have hs : Order.succ o ≤ i.1 := Order.succ_le_iff.mpr hlt
    exact (not_lt_of_ge hs) i.2

@[simp]
theorem ordinalIioSuccOrderTop_top_val (o : Ordinal) :
    ((ordinalIioSuccOrderTop o).top : Ordinal) = o := rfl

def ordinalIioSuccEmb (o : Ordinal) :
    Set.Iio o ↪ Set.Iio (Order.succ o) where
  toFun i := ⟨i.1, i.2.trans (Order.lt_succ o)⟩
  inj' := fun _ _ h => Subtype.ext (Subtype.mk.inj h)

@[simp]
theorem ordinalIioSuccEmb_apply_val (o : Ordinal) (i : Set.Iio o) :
    ((ordinalIioSuccEmb o i : Set.Iio (Order.succ o)) : Ordinal) = i.1 := rfl

theorem ordinalIioSuccEmb_lt_top (o : Ordinal) (i : Set.Iio o) :
    ((ordinalIioSuccEmb o i : Set.Iio (Order.succ o)) : Ordinal) <
      ((ordinalIioSuccOrderTop o).top : Ordinal) :=
  i.2

def ordinalIioSuccEmbIioEquiv (o : Ordinal) (i : Set.Iio o) :
    Set.Iio (ordinalIioSuccEmb o i) ≃ Set.Iio i where
  toFun j := ⟨⟨j.1.1, show j.1.1 < o from j.2.trans i.2⟩, j.2⟩
  invFun j := ⟨ordinalIioSuccEmb o j.1, j.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

@[simp]
theorem ordinalIioSuccEmbIioEquiv_apply_val (o : Ordinal) (i : Set.Iio o)
    (j : Set.Iio (ordinalIioSuccEmb o i)) :
    (((ordinalIioSuccEmbIioEquiv o i) j : Set.Iio i) : Set.Iio o) =
      ⟨j.1.1, show j.1.1 < o from j.2.trans i.2⟩ :=
  Subtype.ext rfl

@[simp]
theorem ordinalIioSuccEmbIioEquiv_symm_apply_val (o : Ordinal) (i : Set.Iio o)
    (j : Set.Iio i) :
    (((ordinalIioSuccEmbIioEquiv o i).symm j :
      Set.Iio (ordinalIioSuccEmb o i)) : Set.Iio (Order.succ o)) =
      ordinalIioSuccEmb o j.1 :=
  Subtype.ext rfl

def ordinalIioSubtypeIioEquiv {o : Ordinal} (i : Set.Iio o) :
    Set.Iio i ≃ Set.Iio i.1 where
  toFun j := ⟨j.1.1, show j.1.1 < i.1 from j.2⟩
  invFun j :=
    ⟨⟨j.1, show j.1 < o from j.2.trans i.2⟩,
      show (⟨j.1, show j.1 < o from j.2.trans i.2⟩ : Set.Iio o) < i from j.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

@[simp]
theorem ordinalIioSubtypeIioEquiv_apply_val {o : Ordinal} (i : Set.Iio o)
    (j : Set.Iio i) :
    ((ordinalIioSubtypeIioEquiv i j : Set.Iio i.1) : Ordinal) = j.1.1 :=
  by rfl

@[simp]
theorem ordinalIioSubtypeIioEquiv_symm_apply_val {o : Ordinal} (i : Set.Iio o)
    (j : Set.Iio i.1) :
    (((ordinalIioSubtypeIioEquiv i).symm j : Set.Iio i) : Set.Iio o) =
      ⟨j.1, show j.1 < o from j.2.trans i.2⟩ :=
  Subtype.ext rfl

def ordinalIioSuccTopIioEquiv (o : Ordinal) :
    Set.Iio ((ordinalIioSuccOrderTop o).top) ≃ Set.Iio o where
  toFun i := ⟨i.1.1, i.2⟩
  invFun i := ⟨ordinalIioSuccEmb o i, ordinalIioSuccEmb_lt_top o i⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

@[simp]
theorem ordinalIioSuccTopIioEquiv_apply_val (o : Ordinal)
    (i : Set.Iio ((ordinalIioSuccOrderTop o).top)) :
    ((ordinalIioSuccTopIioEquiv o i : Set.Iio o) : Ordinal) = i.1.1 :=
  rfl

@[simp]
theorem ordinalIioSuccTopIioEquiv_symm_apply_val (o : Ordinal)
    (i : Set.Iio o) :
    (((ordinalIioSuccTopIioEquiv o).symm i :
      Set.Iio ((ordinalIioSuccOrderTop o).top)) : Set.Iio (Order.succ o)) =
      ordinalIioSuccEmb o i :=
  rfl

theorem exists_ordinalIioSuccEmb_eq_of_val_lt {o : Ordinal}
    (j : Set.Iio (Order.succ o)) (hj : j.1 < o) :
    ∃ i : Set.Iio o, ordinalIioSuccEmb o i = j := by
  exact ⟨⟨j.1, hj⟩, Subtype.ext rfl⟩

theorem ordinalIioSucc_ne_top_iff_val_lt (o : Ordinal)
    (j : Set.Iio (Order.succ o)) :
    j ≠ (ordinalIioSuccOrderTop o).top ↔ j.1 < o := by
  constructor
  · intro hne
    by_contra hnot
    have hle_top : j.1 ≤ o :=
      (ordinalIioSuccOrderTop o).le_top j
    have htop : j = (ordinalIioSuccOrderTop o).top := by
      apply Subtype.ext
      exact le_antisymm hle_top (le_of_not_gt hnot)
    exact hne htop
  · intro hlt htop
    have hval : j.1 = o := by
      simpa using congrArg Subtype.val htop
    rw [hval] at hlt
    exact (lt_irrefl o) hlt

theorem ordinalIioSuccEmb_range_iff_ne_top (o : Ordinal)
    (j : Set.Iio (Order.succ o)) :
    j ∈ Set.range (ordinalIioSuccEmb o) ↔
      j ≠ (ordinalIioSuccOrderTop o).top := by
  constructor
  · rintro ⟨i, rfl⟩ htop
    have hval :
        ((ordinalIioSuccEmb o i : Set.Iio (Order.succ o)) : Ordinal) = o := by
      simpa using congrArg Subtype.val htop
    have hlt : ((ordinalIioSuccEmb o i : Set.Iio (Order.succ o)) : Ordinal) < o :=
      i.2
    rw [hval] at hlt
    exact (lt_irrefl o) hlt
  · intro hne
    exact Set.mem_range.mpr
      (exists_ordinalIioSuccEmb_eq_of_val_lt j
        ((ordinalIioSucc_ne_top_iff_val_lt o j).mp hne))

theorem ordinalIioSucc_univ_eq_insert_top_range (o : Ordinal) :
    (Set.univ : Set (Set.Iio (Order.succ o))) =
      insert (ordinalIioSuccOrderTop o).top (Set.range (ordinalIioSuccEmb o)) := by
  ext j
  constructor
  · intro _
    by_cases htop : j = (ordinalIioSuccOrderTop o).top
    · exact Or.inl htop
    · exact Or.inr ((ordinalIioSuccEmb_range_iff_ne_top o j).mpr htop)
  · intro _
    trivial

theorem ordinalIioSuccEmb_ne_top (o : Ordinal) (i : Set.Iio o) :
    ordinalIioSuccEmb o i ≠ (ordinalIioSuccOrderTop o).top :=
  (ordinalIioSuccEmb_range_iff_ne_top o (ordinalIioSuccEmb o i)).mp
    (Set.mem_range_self i)

theorem ordinalIio_bot_val_eq_zero {o : Ordinal} [OrderBot (Set.Iio o)]
    (h0 : (0 : Ordinal) < o) :
    ((⊥ : Set.Iio o) : Ordinal) = 0 := by
  have hle : ((⊥ : Set.Iio o) : Ordinal) ≤ 0 :=
    show (⊥ : Set.Iio o) ≤ ⟨0, h0⟩ from bot_le
  exact le_antisymm hle bot_le

theorem ordinalIioSuccEmb_bot_eq_bot {o : Ordinal} [OrderBot (Set.Iio o)]
    (h0 : (0 : Ordinal) < o) :
    ordinalIioSuccEmb o (⊥ : Set.Iio o) =
      (⊥ : Set.Iio (Order.succ o)) := by
  apply Subtype.ext
  exact ordinalIio_bot_val_eq_zero h0

noncomputable def ordinalIioSuccPred (o : Ordinal)
    (j : Set.Iio (Order.succ o))
    (hj : j ≠ (ordinalIioSuccOrderTop o).top) : Set.Iio o :=
  Classical.choose (Set.mem_range.mp ((ordinalIioSuccEmb_range_iff_ne_top o j).mpr hj))

theorem ordinalIioSuccEmb_pred (o : Ordinal)
    (j : Set.Iio (Order.succ o))
    (hj : j ≠ (ordinalIioSuccOrderTop o).top) :
    ordinalIioSuccEmb o (ordinalIioSuccPred o j hj) = j :=
  Classical.choose_spec (Set.mem_range.mp ((ordinalIioSuccEmb_range_iff_ne_top o j).mpr hj))

theorem ordinalIioSuccPred_emb (o : Ordinal) (i : Set.Iio o) :
    ordinalIioSuccPred o (ordinalIioSuccEmb o i)
      (ordinalIioSuccEmb_ne_top o i) = i :=
  (ordinalIioSuccEmb o).injective
    (ordinalIioSuccEmb_pred o (ordinalIioSuccEmb o i) (ordinalIioSuccEmb_ne_top o i))

theorem ordinalIioSuccEmb_choose_lt_choose_of_lt {o : Ordinal}
    {i j : Set.Iio (Order.succ o)}
    (hj : j ≠ (ordinalIioSuccOrderTop o).top) (hij : i < j) :
    let hi : i ≠ (ordinalIioSuccOrderTop o).top := by
      intro hitop
      rw [hitop] at hij
      exact (not_lt_of_ge ((ordinalIioSuccOrderTop o).le_top j)) hij
    ordinalIioSuccPred o i hi < ordinalIioSuccPred o j hj := by
  classical
  dsimp
  let hi : i ≠ (ordinalIioSuccOrderTop o).top := by
    intro hitop
    rw [hitop] at hij
    exact (not_lt_of_ge ((ordinalIioSuccOrderTop o).le_top j)) hij
  have hispec : ordinalIioSuccEmb o (ordinalIioSuccPred o i hi) = i :=
    ordinalIioSuccEmb_pred o i hi
  have hjspec : ordinalIioSuccEmb o (ordinalIioSuccPred o j hj) = j :=
    ordinalIioSuccEmb_pred o j hj
  have hispecVal : (ordinalIioSuccPred o i hi : Ordinal) = i.1 := by
    simpa using congrArg Subtype.val hispec
  have hjspecVal : (ordinalIioSuccPred o j hj : Ordinal) = j.1 := by
    simpa using congrArg Subtype.val hjspec
  have hval :
      (ordinalIioSuccPred o i hi : Ordinal) <
        (ordinalIioSuccPred o j hj : Ordinal) := by
    rw [hispecVal, hjspecVal]
    exact hij
  exact hval

theorem ordinalIioSuccZero_subsingleton :
    Subsingleton (Set.Iio (Order.succ (0 : Ordinal))) := by
  refine ⟨fun i j => ?_⟩
  apply Subtype.ext
  have hi : i.1 ≤ 0 :=
    (ordinalIioSuccOrderTop (0 : Ordinal)).le_top i
  have hj : j.1 ≤ 0 :=
    (ordinalIioSuccOrderTop (0 : Ordinal)).le_top j
  exact (le_antisymm hi bot_le).trans (le_antisymm hj bot_le).symm

def ordinalIioSuccTopEmbOfLt {o : Ordinal} {i j : Set.Iio o} (hij : i < j) :
    Set.Iio (Order.succ j.1) :=
  ⟨i.1, show i.1 ∈ Set.Iio (Order.succ j.1) from
    (show i.1 < j.1 from hij).trans (Order.lt_succ j.1)⟩

@[simp]
theorem ordinalIioSuccTopEmbOfLt_val {o : Ordinal} {i j : Set.Iio o} (hij : i < j) :
    ((ordinalIioSuccTopEmbOfLt hij : Set.Iio (Order.succ j.1)) : Ordinal) = i.1 :=
  by rfl

theorem ordinalIioSuccTopEmbOfLt_eq_bot_of_val_eq_zero
    {o : Ordinal} {i j : Set.Iio o} (hij : i < j)
    (hi : (i : Ordinal) = 0) :
    ordinalIioSuccTopEmbOfLt hij =
      (⊥ : Set.Iio (Order.succ j.1)) := by
  apply Subtype.ext
  rw [ordinalIioSuccTopEmbOfLt_val, hi]
  exact (ordinalIio_bot_val_eq_zero
    (lt_of_le_of_lt bot_le (Order.lt_succ j.1))).symm

theorem ordinalIioSuccTopEmbOfLt_eq_succEmb
    {o : Ordinal} {i j : Set.Iio o} (hij : i < j) :
    ordinalIioSuccTopEmbOfLt hij =
      ordinalIioSuccEmb j.1 (⟨i.1, show i.1 ∈ Set.Iio j.1 from hij⟩ : Set.Iio j.1) := by
  apply Subtype.ext
  rfl

theorem ordinalIioSuccTopEmbOfLt_eq_succEmb_top
    {o p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
    (hij : i < (⟨Order.succ p, hp⟩ : Set.Iio o)) (hi : (i : Ordinal) = p) :
    ordinalIioSuccTopEmbOfLt hij =
      ordinalIioSuccEmb (Order.succ p) (ordinalIioSuccOrderTop p).top := by
  apply Subtype.ext
  rw [ordinalIioSuccTopEmbOfLt_val, hi]
  rfl

theorem ordinal_lt_succ_eq_or_lt {a p : Ordinal} (h : a < Order.succ p) :
    a = p ∨ a < p := by
  exact Order.lt_succ_iff_eq_or_lt.mp h

def ordinalIioSuccEndpointEmbOfLt {o : Ordinal} {i j : Set.Iio o} (hij : i < j) :
    Set.Iio (Order.succ j.1) :=
  ⟨Order.succ i.1, show Order.succ i.1 ∈ Set.Iio (Order.succ j.1) from
    (Order.succ_le_iff.mpr (show i.1 < j.1 from hij)).trans_lt (Order.lt_succ j.1)⟩

@[simp]
theorem ordinalIioSuccEndpointEmbOfLt_val {o : Ordinal} {i j : Set.Iio o} (hij : i < j) :
    ((ordinalIioSuccEndpointEmbOfLt hij : Set.Iio (Order.succ j.1)) : Ordinal) =
      Order.succ i.1 :=
  by rfl

theorem ordinalIioSubtypeIioEquiv_symm_top_succEndpointEmbOfLt
    {o : Ordinal} {i j : Set.Iio o} (hij : i < j) :
    (((ordinalIioSubtypeIioEquiv (ordinalIioSuccEndpointEmbOfLt hij)).symm
        (ordinalIioSuccOrderTop i.1).top : Set.Iio (ordinalIioSuccEndpointEmbOfLt hij)) :
        Set.Iio (Order.succ j.1)) =
      ordinalIioSuccTopEmbOfLt hij := by
  apply Subtype.ext
  rfl

theorem ordinalIioSubtypeIioEquiv_symm_bot_succEndpointEmbOfLt
    {o : Ordinal} {i j : Set.Iio o} (hij : i < j) :
    let endpoint := ordinalIioSuccEndpointEmbOfLt hij
    let hi : (0 : Ordinal) < endpoint.1 := by
      rw [ordinalIioSuccEndpointEmbOfLt_val]
      exact lt_of_le_of_lt bot_le (Order.lt_succ i.1)
    letI : OrderBot (Set.Iio endpoint.1) := ordinalIioOrderBotOfPos hi
    (((ordinalIioSubtypeIioEquiv endpoint).symm (⊥ : Set.Iio endpoint.1) :
        Set.Iio endpoint) : Set.Iio (Order.succ j.1)) =
      (⊥ : Set.Iio (Order.succ j.1)) := by
  dsimp
  let endpoint := ordinalIioSuccEndpointEmbOfLt hij
  let hi : (0 : Ordinal) < endpoint.1 := by
    rw [ordinalIioSuccEndpointEmbOfLt_val]
    exact lt_of_le_of_lt bot_le (Order.lt_succ i.1)
  let _ : OrderBot (Set.Iio endpoint.1) := ordinalIioOrderBotOfPos hi
  apply Subtype.ext
  rw [ordinalIioSubtypeIioEquiv_symm_apply_val]
  rw [ordinalIio_bot_val_eq_zero hi]
  exact (ordinalIio_bot_val_eq_zero (lt_of_le_of_lt bot_le (Order.lt_succ j.1))).symm

instance hartogsOrdinalToTypeOrderBot (α : Type*) :
    OrderBot (hartogsOrdinal α).ToType :=
  have hne : hartogsOrdinal α ≠ 0 := by
    intro hzero
    have hcard : Order.succ (Cardinal.mk α) = 0 :=
      Cardinal.ord_eq_zero.mp hzero
    have hlt : Cardinal.mk α < 0 := by
      simpa [hcard] using Order.lt_succ (Cardinal.mk α)
    exact (not_lt_of_ge (show (0 : Cardinal) ≤ Cardinal.mk α from zero_le)) hlt
  have : Nonempty (hartogsOrdinal α).ToType :=
    Ordinal.nonempty_toType_iff.mpr hne
  WellFoundedLT.toOrderBot (hartogsOrdinal α).ToType

theorem not_exists_strictMono_cardinal_succ_ord_toType
    (α : Type*) [Preorder α] :
    ¬ ∃ f : (hartogsOrdinal α).ToType → α, StrictMono f := by
  rintro ⟨f, hf⟩
  have hcard :
      Cardinal.mk ((Order.succ (Cardinal.mk α)).ord.ToType) ≤ Cardinal.mk α :=
    Cardinal.mk_le_of_injective hf.injective
  rw [Cardinal.mk_ord_toType] at hcard
  exact (Order.lt_succ (Cardinal.mk α)).not_ge hcard

end

end HahnKaplanskyRealClosedness
