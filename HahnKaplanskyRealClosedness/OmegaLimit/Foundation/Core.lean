/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.Foundation.Ordinal

/-!
# Separated support and coherent block-chain core for omega limits
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

theorem not_exists_strictMono_oneClusterState_val_hartogs
    {F : Polynomial (valuationSubring k Γ)} :
    ¬ ∃ S : (hartogsOrdinal Γ).ToType → OneClusterState k Γ F,
      StrictMono fun i => (S i).val k Γ := by
  rintro ⟨S, hS⟩
  exact not_exists_strictMono_cardinal_succ_ord_toType Γ
    ⟨fun i => (S i).val k Γ, hS⟩

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem finite_coeff_support_of_separated_supports
    {ι : Type*} [LinearOrder ι] (D : ι → HahnSeries Γ k)
    (lo hi : ι → Γ)
    (hsep : ∀ {i j : ι}, i < j → hi i ≤ lo j)
    (hsupp : ∀ i, (D i).support ⊆ Set.Ico (lo i) (hi i)) (γ : Γ) :
    {i : ι | (D i).coeff γ ≠ 0}.Finite := by
  apply Set.Subsingleton.finite
  intro i hiγ j hjγ
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hγi : γ ∈ (D i).support := by
      simpa [Function.mem_support] using hiγ
    have hγj : γ ∈ (D j).support := by
      simpa [Function.mem_support] using hjγ
    have hlt : γ < hi i := (hsupp i hγi).2
    have hle : hi i ≤ γ := (hsep hij).trans (hsupp j hγj).1
    exact False.elim ((not_lt_of_ge hle) hlt)
  · rfl
  · have hγi : γ ∈ (D i).support := by
      simpa [Function.mem_support] using hiγ
    have hγj : γ ∈ (D j).support := by
      simpa [Function.mem_support] using hjγ
    have hlt : γ < hi j := (hsupp j hγj).2
    have hle : hi j ≤ γ := (hsep hji).trans (hsupp i hγi).1
    exact False.elim ((not_lt_of_ge hle) hlt)

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem iUnion_support_isPWO_of_separated_supports
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] (D : ι → HahnSeries Γ k)
    (lo hi : ι → Γ)
    (hsep : ∀ {i j : ι}, i < j → hi i ≤ lo j)
    (hsupp : ∀ i, (D i).support ⊆ Set.Ico (lo i) (hi i)) :
    (⋃ i : ι, (D i).support).IsPWO := by
  classical
  let U : Set Γ := ⋃ i : ι, (D i).support
  rw [Set.isPWO_iff_isWF]
  change U.IsWF
  rw [Set.IsWF, Set.wellFoundedOn_iff, WellFounded.wellFounded_iff_has_min]
  intro t ht
  by_cases hUt : (U ∩ t).Nonempty
  · let Iset : Set ι := {i | ∃ γ : Γ, γ ∈ t ∧ γ ∈ (D i).support}
    have hInon : Iset.Nonempty := by
      rcases hUt with ⟨γ, hγU, hγt⟩
      rcases Set.mem_iUnion.mp hγU with ⟨i, hi⟩
      exact ⟨i, ⟨γ, hγt, hi⟩⟩
    let hIwf : Iset.IsWF := Set.IsWF.of_wellFoundedLT Iset
    let i₀ : ι := hIwf.min hInon
    have hi₀mem : i₀ ∈ Iset := hIwf.min_mem hInon
    rcases hi₀mem with ⟨γ₀, hγ₀t, hγ₀supp⟩
    let fiber : Set Γ := (D i₀).support ∩ t
    have hfiberWF : fiber.IsWF := (D i₀).isPWO_support.isWF.mono (by
      intro γ hγ
      exact hγ.1)
    have hfiberNonempty : fiber.Nonempty := ⟨γ₀, hγ₀supp, hγ₀t⟩
    let m : Γ := hfiberWF.min hfiberNonempty
    have hmFiber : m ∈ fiber := hfiberWF.min_mem hfiberNonempty
    refine ⟨m, hmFiber.2, ?_⟩
    intro x hxt hx
    rcases hx with ⟨hxm, hxU, _hmU⟩
    rcases Set.mem_iUnion.mp hxU with ⟨j, hxj⟩
    have hjmem : j ∈ Iset := ⟨x, hxt, hxj⟩
    rcases lt_trichotomy j i₀ with hji | rfl | hij
    · exact (hIwf.not_lt_min hInon hjmem) hji
    · exact (hfiberWF.not_lt_min hfiberNonempty ⟨hxj, hxt⟩) hxm
    · have hm_hi : m < hi i₀ := (hsupp i₀ hmFiber.1).2
      have hi_le_x : hi i₀ ≤ x := (hsep hij).trans ((hsupp j hxj).1)
      exact (lt_asymm hxm (hm_hi.trans_le hi_le_x)).elim
  · rcases ht with ⟨m, hmt⟩
    refine ⟨m, hmt, ?_⟩
    intro _x _hxt hx
    exact hUt ⟨m, hx.2.2, hmt⟩

def HahnSeries.summableFamilyOfSeparatedSupportsWithPWO
    {ι : Type*} [LinearOrder ι] (D : ι → HahnSeries Γ k)
    (lo hi : ι → Γ)
    (hsep : ∀ {i j : ι}, i < j → hi i ≤ lo j)
    (hsupp : ∀ i, (D i).support ⊆ Set.Ico (lo i) (hi i))
    (hPWO : (⋃ i : ι, (D i).support).IsPWO) :
    HahnSeries.SummableFamily Γ k ι where
  toFun := D
  isPWO_iUnion_support' := hPWO
  finite_co_support' :=
    finite_coeff_support_of_separated_supports k Γ D lo hi hsep hsupp

def HahnSeries.summableFamilyOfSeparatedSupports
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] (D : ι → HahnSeries Γ k)
    (lo hi : ι → Γ)
    (hsep : ∀ {i j : ι}, i < j → hi i ≤ lo j)
    (hsupp : ∀ i, (D i).support ⊆ Set.Ico (lo i) (hi i)) :
    HahnSeries.SummableFamily Γ k ι :=
  HahnSeries.summableFamilyOfSeparatedSupportsWithPWO k Γ D lo hi hsep hsupp
    (iUnion_support_isPWO_of_separated_supports k Γ D lo hi hsep hsupp)

def OneClusterBlockSuccessor.diffSummableFamily
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ) :
    HahnSeries.SummableFamily Γ k ι :=
  HahnSeries.summableFamilyOfSeparatedSupports k Γ
    (fun i => (B i).diffHahnSeries k Γ)
    (fun i => (S i).val k Γ)
    (fun i => (B i).next.val k Γ)
    hsep
    (fun i => (B i).diffHahnSeries_support_subset_Ico k Γ)

def OneClusterBlockSuccessor.diffHahnSeriesLimit
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ) :
    HahnSeries Γ k :=
  (OneClusterBlockSuccessor.diffSummableFamily k Γ S B hsep).hsum

theorem OneClusterBlockSuccessor.diffHahnSeriesLimit_support_subset
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ) :
    (OneClusterBlockSuccessor.diffHahnSeriesLimit k Γ S B hsep).support ⊆
      ⋃ i : ι, ((B i).diffHahnSeries k Γ).support :=
  HahnSeries.SummableFamily.support_hsum_subset

theorem OneClusterBlockSuccessor.diffHahnSeriesLimit_support_subset_Ici
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ)
    {μ : Γ} (hμ : ∀ i : ι, μ ≤ (S i).val k Γ) :
    (OneClusterBlockSuccessor.diffHahnSeriesLimit k Γ S B hsep).support ⊆
      Set.Ici μ := by
  intro γ hγ
  have hmem :=
    OneClusterBlockSuccessor.diffHahnSeriesLimit_support_subset
      k Γ S B hsep hγ
  rcases Set.mem_iUnion.mp hmem with ⟨i, hi⟩
  exact (hμ i).trans ((B i).diffHahnSeries_support_subset_Ico k Γ hi).1

theorem OneClusterBlockSuccessor.le_orderTop_diffHahnSeriesLimit
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ)
    {μ : Γ} (hμ : ∀ i : ι, μ ≤ (S i).val k Γ) :
    (μ : WithTop Γ) ≤
      (OneClusterBlockSuccessor.diffHahnSeriesLimit k Γ S B hsep).orderTop := by
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro γ hγ
  by_contra hne
  have hmem :
      γ ∈ (OneClusterBlockSuccessor.diffHahnSeriesLimit k Γ S B hsep).support := by
    simpa [Function.mem_support] using hne
  exact (not_lt_of_ge
    (OneClusterBlockSuccessor.diffHahnSeriesLimit_support_subset_Ici
      k Γ S B hsep hμ hmem))
    (WithTop.coe_lt_coe.mp hγ)

def OneClusterBlockSuccessor.diffHahnFieldLimit
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ) :
    HahnField k Γ :=
  toLex (OneClusterBlockSuccessor.diffHahnSeriesLimit k Γ S B hsep)

def OneClusterBlockSuccessor.diffLimitValuationSubring
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ)
    (h0 : ∀ i : ι, 0 ≤ (S i).val k Γ) :
    valuationSubring k Γ :=
  ⟨OneClusterBlockSuccessor.diffHahnFieldLimit k Γ S B hsep, by
    rw [mem_valuationSubring_iff, addVal_apply]
    exact OneClusterBlockSuccessor.le_orderTop_diffHahnSeriesLimit
      k Γ S B hsep h0⟩

theorem OneClusterBlockSuccessor.diffLimitValuationSubring_mem_maximalIdeal
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ)
    {μ : Γ} (hμpos : 0 < μ) (hμ : ∀ i : ι, μ ≤ (S i).val k Γ) :
    OneClusterBlockSuccessor.diffLimitValuationSubring k Γ S B hsep
        (fun i => (le_trans (le_of_lt hμpos) (hμ i))) ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [mem_maximalIdeal_iff_pos_addVal, addVal_apply]
  exact (WithTop.coe_lt_coe.mpr hμpos).trans_le
    (OneClusterBlockSuccessor.le_orderTop_diffHahnSeriesLimit
      k Γ S B hsep hμ)

theorem OneClusterBlockSuccessor.bot_state_val_le
    {ι : Type*} [LinearOrder ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ)
    (i : ι) :
    (S ⊥).val k Γ ≤ (S i).val k Γ := by
  by_cases hi : i = ⊥
  · subst hi
    rfl
  · have hlt : (⊥ : ι) < i := lt_of_le_of_ne bot_le (Ne.symm hi)
    exact le_trans (le_of_lt ((B ⊥).val_lt)) (hsep hlt)

theorem OneClusterBlockSuccessor.state_val_strictMono_of_separated
    {ι : Type*} [Preorder ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ) :
    StrictMono fun i : ι => (S i).val k Γ := by
  intro i j hij
  exact (B i).val_lt.trans_le (hsep hij)

theorem not_exists_hartogs_separatedBlockFamily
    {F : Polynomial (valuationSubring k Γ)} :
    ¬ ∃ (S : (hartogsOrdinal Γ).ToType → OneClusterState k Γ F)
        (B : ∀ i : (hartogsOrdinal Γ).ToType, OneClusterBlockSuccessor k Γ (S i)),
      (∀ {i j : (hartogsOrdinal Γ).ToType}, i < j →
        (B i).next.val k Γ ≤ (S j).val k Γ) := by
  rintro ⟨S, B, hsep⟩
  exact not_exists_strictMono_oneClusterState_val_hartogs k Γ
    ⟨S, OneClusterBlockSuccessor.state_val_strictMono_of_separated k Γ S B hsep⟩

/-- A block chain indexed by an arbitrary preorder.  The field `separated` is the key invariant
for limit stages: every block correction is bounded above by all later residual values. -/
structure OneClusterBlockChain
    (ι : Type*) [Preorder ι]
    (F : Polynomial (valuationSubring k Γ)) where
  state : ι → OneClusterState k Γ F
  block : ∀ i : ι, OneClusterBlockSuccessor k Γ (state i)
  separated : ∀ {i j : ι}, i < j → (block i).next.val k Γ ≤ (state j).val k Γ

namespace OneClusterBlockChain

theorem ext_state_block
    {ι : Type*} [Preorder ι]
    {F : Polynomial (valuationSubring k Γ)}
    {C D : OneClusterBlockChain k Γ ι F}
    (hstate : ∀ i, C.state i = D.state i)
    (hblock : ∀ i, Eq.ndrec (C.block i) (hstate i) = D.block i) :
  C = D := by
  cases C
  cases D
  rename_i state₁ block₁ separated₁ state₂ block₂ separated₂
  simp only at hstate hblock ⊢
  have hstateFun : state₁ = state₂ := funext hstate
  cases hstateFun
  simp only at hblock
  have hblockFun : block₁ = block₂ := funext hblock
  cases hblockFun
  simp

def restrictLT
    {ι : Type*} [Preorder ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) (i : ι) :
    OneClusterBlockChain k Γ (Set.Iio i) F where
  state := fun j => C.state j.1
  block := fun j => C.block j.1
  separated := fun {j l} hjl => C.separated (show (j : ι) < (l : ι) from hjl)

@[simp]
theorem restrictLT_state
    {ι : Type*} [Preorder ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) (i : ι) (j : Set.Iio i) :
    (C.restrictLT k Γ i).state j = C.state j.1 :=
  rfl

@[simp]
theorem restrictLT_block
    {ι : Type*} [Preorder ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) (i : ι) (j : Set.Iio i) :
    (C.restrictLT k Γ i).block j = C.block j.1 :=
  rfl

theorem state_val_strictMono
    {ι : Type*} [Preorder ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) :
    StrictMono fun i : ι => (C.state i).val k Γ :=
  OneClusterBlockSuccessor.state_val_strictMono_of_separated k Γ
    C.state C.block C.separated

theorem not_hartogs
    {F : Polynomial (valuationSubring k Γ)} :
    ¬ Nonempty (OneClusterBlockChain k Γ (hartogsOrdinal Γ).ToType F) := by
  rintro ⟨C⟩
  exact not_exists_hartogs_separatedBlockFamily k Γ
    ⟨C.state, C.block, C.separated⟩

theorem not_hartogs_iio
    {F : Polynomial (valuationSubring k Γ)} :
    ¬ Nonempty (OneClusterBlockChain k Γ (Set.Iio (hartogsOrdinal Γ)) F) := by
  let _ : OrderBot (Set.Iio (hartogsOrdinal Γ)) :=
    ordinalIioOrderBotOfPos (hartogsOrdinal_pos Γ)
  rintro ⟨C⟩
  exact not_exists_strictMono_cardinal_succ_ord_toType Γ
    ⟨fun i : (hartogsOrdinal Γ).ToType =>
        (C.state ((Ordinal.ToType.mk (o := hartogsOrdinal Γ)).symm i)).val k Γ,
      by
        intro i j hij
        exact C.state_val_strictMono k Γ
          ((Ordinal.ToType.mk (o := hartogsOrdinal Γ)).symm.strictMono hij)⟩

def topState
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    OneClusterState k Γ F :=
  C.state (ordinalIioSuccOrderTop o).top

def topBlock
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    OneClusterBlockSuccessor k Γ (C.topState k Γ) :=
  C.block (ordinalIioSuccOrderTop o).top

theorem topBlock_val_lt
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    (C.topState k Γ).val k Γ < (C.topBlock k Γ).next.val k Γ :=
  (C.topBlock k Γ).val_lt

def succTopState
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    OneClusterState k Γ F :=
  (C.topBlock k Γ).next

theorem topState_val_lt_succTopState_val
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    (C.topState k Γ).val k Γ < (C.succTopState k Γ).val k Γ :=
  C.topBlock_val_lt k Γ

theorem block_next_val_le_succTopState_val
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    (C.block i).next.val k Γ ≤ (C.succTopState k Γ).val k Γ := by
  by_cases htop : i = (ordinalIioSuccOrderTop o).top
  · subst i
    rfl
  · have hlt : i < (ordinalIioSuccOrderTop o).top := by
      exact (ordinalIioSucc_ne_top_iff_val_lt o i).mp htop
    exact (C.separated hlt).trans (le_of_lt (C.topState_val_lt_succTopState_val k Γ))

theorem OneClusterBlockSuccessor.next_val_eq_of_eq
    {F : Polynomial (valuationSubring k Γ)}
    {S T : OneClusterState k Γ F} (h : S = T)
    (B : OneClusterBlockSuccessor k Γ S) :
    ((Eq.ndrec B h : OneClusterBlockSuccessor k Γ T).next.val k Γ) =
      B.next.val k Γ := by
  cases h
  rfl

theorem OneClusterBlockSuccessor.diffHahnSeries_eq_of_eq
    {F : Polynomial (valuationSubring k Γ)}
    {S T : OneClusterState k Γ F} (h : S = T)
    (B : OneClusterBlockSuccessor k Γ S) :
    (Eq.ndrec B h : OneClusterBlockSuccessor k Γ T).diffHahnSeries k Γ =
      B.diffHahnSeries k Γ := by
  cases h
  rfl

noncomputable def succExtendState
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (j : Set.Iio (Order.succ (Order.succ o))) :
    OneClusterState k Γ F :=
  if htop : j = (ordinalIioSuccOrderTop (Order.succ o)).top then
    C.succTopState k Γ
  else
    C.state (ordinalIioSuccPred (Order.succ o) j htop)

@[simp]
theorem succExtendState_top
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    C.succExtendState k Γ (ordinalIioSuccOrderTop (Order.succ o)).top =
      C.succTopState k Γ := by
  simp [succExtendState]

@[simp]
theorem succExtendState_emb
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (i : Set.Iio (Order.succ o)) :
    C.succExtendState k Γ (ordinalIioSuccEmb (Order.succ o) i) =
      C.state i := by
  dsimp [succExtendState]
  have hne :
      ordinalIioSuccEmb (Order.succ o) i ≠
        (ordinalIioSuccOrderTop (Order.succ o)).top :=
    ordinalIioSuccEmb_ne_top (Order.succ o) i
  rw [dif_neg hne]
  rw [ordinalIioSuccPred_emb]

theorem succExtendState_not_top
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F)
    (j : Set.Iio (Order.succ (Order.succ o)))
    (hj : j ≠ (ordinalIioSuccOrderTop (Order.succ o)).top) :
    C.succExtendState k Γ j =
      C.state (ordinalIioSuccPred (Order.succ o) j hj) := by
  dsimp [succExtendState]
  rw [dif_neg hj]

def diffSummableFamily
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) :
    HahnSeries.SummableFamily Γ k ι :=
  OneClusterBlockSuccessor.diffSummableFamily k Γ C.state C.block C.separated

def diffHahnSeriesLimit
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) :
    HahnSeries Γ k :=
  OneClusterBlockSuccessor.diffHahnSeriesLimit k Γ C.state C.block C.separated

def restrictLTOrdinal
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio o) F) (i : Set.Iio o) :
    OneClusterBlockChain k Γ (Set.Iio i.1) F := by
  classical
  let E := ordinalIioSubtypeIioEquiv i
  refine
    { state := fun j => C.state ((E.symm j).1)
      block := fun j => C.block ((E.symm j).1)
      separated := ?_ }
  intro j l hjl
  exact C.separated (show ((E.symm j).1 : Set.Iio o) < (E.symm l).1 from by
    change j.1 < l.1
    exact hjl)

theorem restrictLTOrdinal_diffHahnSeriesLimit
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio o) F) (i : Set.Iio o) :
    (C.restrictLTOrdinal k Γ i).diffHahnSeriesLimit k Γ =
      ((C.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
  classical
  let R := C.restrictLTOrdinal k Γ i
  let P := C.restrictLT k Γ i
  let E := ordinalIioSubtypeIioEquiv i
  let sR := R.diffSummableFamily k Γ
  let sP := P.diffSummableFamily k Γ
  have heq : sR = HahnSeries.SummableFamily.Equiv E sP := by
    ext j
    dsimp [HahnSeries.SummableFamily.Equiv, sR, sP, R, P,
      OneClusterBlockChain.diffSummableFamily, OneClusterBlockChain.restrictLTOrdinal]
    rfl
  change sR.hsum = sP.hsum
  rw [heq, HahnSeries.SummableFamily.hsum_equiv]

theorem diffHahnSeriesLimit_congr
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C D : OneClusterBlockChain k Γ ι F)
    (hblock : ∀ i, (C.block i).diffHahnSeries k Γ = (D.block i).diffHahnSeries k Γ) :
    C.diffHahnSeriesLimit k Γ = D.diffHahnSeriesLimit k Γ := by
  let sC := C.diffSummableFamily k Γ
  let sD := D.diffSummableFamily k Γ
  have heq : sC = sD := by
    ext i γ
    change ((C.block i).diffHahnSeries k Γ).coeff γ =
      ((D.block i).diffHahnSeries k Γ).coeff γ
    rw [hblock i]
  change sC.hsum = sD.hsum
  rw [heq]

theorem diffHahnSeriesLimit_eq_zero_of_isEmpty
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [IsEmpty ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) :
    C.diffHahnSeriesLimit k Γ = 0 := by
  ext γ
  change ((C.diffSummableFamily k Γ).hsum).coeff γ = 0
  rw [HahnSeries.SummableFamily.coeff_hsum]
  rw [finsum_eq_zero_of_forall_eq_zero]
  intro i
  exact isEmptyElim i

theorem diffHahnSeriesLimit_support_subset
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) :
    (C.diffHahnSeriesLimit k Γ).support ⊆
      ⋃ i : ι, ((C.block i).diffHahnSeries k Γ).support :=
  OneClusterBlockSuccessor.diffHahnSeriesLimit_support_subset k Γ
    C.state C.block C.separated

theorem diffHahnSeriesLimit_support_subset_Ici
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F)
    {μ : Γ} (hμ : ∀ i : ι, μ ≤ (C.state i).val k Γ) :
    (C.diffHahnSeriesLimit k Γ).support ⊆ Set.Ici μ :=
  OneClusterBlockSuccessor.diffHahnSeriesLimit_support_subset_Ici k Γ
    C.state C.block C.separated hμ

theorem diffHahnSeriesLimit_coeff_eq_restrictLT_of_lt_state_val
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) (i : ι) {γ : Γ}
    (hγ : γ < (C.state i).val k Γ) :
    (C.diffHahnSeriesLimit k Γ).coeff γ =
      ((C.restrictLT k Γ i).diffHahnSeriesLimit k Γ).coeff γ := by
  let emb : Set.Iio i ↪ ι :=
    { toFun := fun j => j.1
      inj' := fun j l h => Subtype.ext h }
  let P : HahnSeries.SummableFamily Γ k (Set.Iio i) :=
    (C.restrictLT k Γ i).diffSummableFamily k Γ
  have hterm :
      ∀ j : ι,
        ((C.diffSummableFamily k Γ) j).coeff γ =
          ((P.embDomain emb) j).coeff γ := by
    intro j
    by_cases hj : j < i
    · change ((C.diffSummableFamily k Γ) j).coeff γ =
        ((P.embDomain emb) (emb ⟨j, hj⟩)).coeff γ
      rw [HahnSeries.SummableFamily.embDomain_image]
      rfl
    · have hzero : ((C.diffSummableFamily k Γ) j).coeff γ = 0 := by
        by_contra hne
        have hne' : ¬ ((C.block j).diffHahnSeries k Γ).coeff γ = 0 := by
          change ¬ ((C.diffSummableFamily k Γ) j).coeff γ = 0
          exact hne
        have hmem : γ ∈ ((C.block j).diffHahnSeries k Γ).support := by
          simpa [Function.mem_support] using hne'
        have hstate_le : (C.state i).val k Γ ≤ (C.state j).val k Γ :=
          (C.state_val_strictMono k Γ).monotone (le_of_not_gt hj)
        have hcoeff_lower : (C.state j).val k Γ ≤ γ :=
          ((C.block j).diffHahnSeries_support_subset_Ico k Γ hmem).1
        exact (not_lt_of_ge (hstate_le.trans hcoeff_lower)) hγ
      have hnotrange : j ∉ Set.range emb := by
        rintro ⟨l, rfl⟩
        exact hj l.2
      rw [hzero, HahnSeries.SummableFamily.embDomain_of_notMem_range (s := P) (f := emb) hnotrange,
        HahnSeries.coeff_zero]
  calc
    (C.diffHahnSeriesLimit k Γ).coeff γ =
        ∑ᶠ j : ι, ((C.diffSummableFamily k Γ) j).coeff γ := by
          change ((C.diffSummableFamily k Γ).hsum).coeff γ =
            ∑ᶠ j : ι, ((C.diffSummableFamily k Γ) j).coeff γ
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = ∑ᶠ j : ι, ((P.embDomain emb) j).coeff γ := finsum_congr hterm
    _ = ((P.embDomain emb).hsum).coeff γ := by
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = ((C.restrictLT k Γ i).diffHahnSeriesLimit k Γ).coeff γ := by
          rw [HahnSeries.SummableFamily.hsum_embDomain]
          rfl

theorem diffHahnSeriesLimit_sub_restrictLT_support_subset_Ici
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) (i : ι) :
    (C.diffHahnSeriesLimit k Γ -
      (C.restrictLT k Γ i).diffHahnSeriesLimit k Γ).support ⊆
      Set.Ici ((C.state i).val k Γ) := by
  intro γ hγ
  by_contra hnot
  have hlt : γ < (C.state i).val k Γ := lt_of_not_ge hnot
  have heq := C.diffHahnSeriesLimit_coeff_eq_restrictLT_of_lt_state_val k Γ i hlt
  have hzero :
      (C.diffHahnSeriesLimit k Γ -
        (C.restrictLT k Γ i).diffHahnSeriesLimit k Γ).coeff γ = 0 := by
    simp [HahnSeries.coeff_sub, heq]
  exact hγ hzero

end OneClusterBlockChain

namespace OneClusterBlockChain

theorem diffHahnSeriesLimit_eq_restrictTop_add_topBlock
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    C.diffHahnSeriesLimit k Γ =
      ((C.restrictLT k Γ (ordinalIioSuccOrderTop o).top).diffHahnSeriesLimit k Γ) +
        (C.topBlock k Γ).diffHahnSeries k Γ := by
  classical
  ext γ
  let top : Set.Iio (Order.succ o) := (ordinalIioSuccOrderTop o).top
  let emb := ordinalIioSuccEmb o
  let f : Set.Iio (Order.succ o) → k :=
    fun i => ((C.diffSummableFamily k Γ) i).coeff γ
  have hnot : top ∉ Set.range emb := by
    intro hmem
    exact (ordinalIioSuccEmb_range_iff_ne_top o top).mp hmem rfl
  have hs : (Set.range emb ∩ Function.support f).Finite :=
    ((C.diffSummableFamily k Γ).finite_co_support γ).subset (by
      intro i hi
      exact hi.2)
  have hsplit :
      (∑ᶠ (i : Set.Iio (Order.succ o)), f i) =
        f top + ∑ᶠ (i : Set.Iio o), f (emb i) := by
    calc
      (∑ᶠ (i : Set.Iio (Order.succ o)), f i)
          = ∑ᶠ (i : Set.Iio (Order.succ o)) (_ : i ∈ Set.univ), f i := by
            rw [finsum_mem_univ]
      _ = ∑ᶠ (i : Set.Iio (Order.succ o))
            (_ : i ∈ insert top (Set.range emb)), f i := by
            rw [← ordinalIioSucc_univ_eq_insert_top_range o]
      _ = f top + ∑ᶠ (i : Set.Iio (Order.succ o)) (_ : i ∈ Set.range emb), f i := by
            rw [finsum_mem_insert' f hnot hs]
      _ = f top + ∑ᶠ (i : Set.Iio o), f (emb i) := by
            rw [finsum_mem_range emb.injective]
  have hprefix :
      (((C.restrictLT k Γ top).diffHahnSeriesLimit k Γ).coeff γ) =
        ∑ᶠ (i : Set.Iio o), f (emb i) := by
    let R := C.restrictLT k Γ top
    let E := ordinalIioSuccTopIioEquiv o
    calc
      ((C.restrictLT k Γ top).diffHahnSeriesLimit k Γ).coeff γ
          = ∑ᶠ (j : Set.Iio top), ((R.diffSummableFamily k Γ) j).coeff γ := by
            change ((R.diffSummableFamily k Γ).hsum).coeff γ =
              ∑ᶠ (j : Set.Iio top), ((R.diffSummableFamily k Γ) j).coeff γ
            rw [HahnSeries.SummableFamily.coeff_hsum]
      _ = ∑ᶠ (i : Set.Iio o), ((R.diffSummableFamily k Γ) ((E.symm) i)).coeff γ := by
            simpa using
              (finsum_comp_equiv (E.symm)
                (f := fun j : Set.Iio top => ((R.diffSummableFamily k Γ) j).coeff γ)).symm
      _ = ∑ᶠ (i : Set.Iio o), f (emb i) := by
            apply finsum_congr
            intro i
            rfl
  have htopcoeff :
      ((C.topBlock k Γ).diffHahnSeries k Γ).coeff γ = f top := rfl
  calc
    (C.diffHahnSeriesLimit k Γ).coeff γ
        = ∑ᶠ (i : Set.Iio (Order.succ o)), f i := by
          change ((C.diffSummableFamily k Γ).hsum).coeff γ =
            ∑ᶠ (i : Set.Iio (Order.succ o)), ((C.diffSummableFamily k Γ) i).coeff γ
          rw [HahnSeries.SummableFamily.coeff_hsum]
    _ = f top + ∑ᶠ (i : Set.Iio o), f (emb i) := hsplit
    _ = (((C.restrictLT k Γ top).diffHahnSeriesLimit k Γ) +
          (C.topBlock k Γ).diffHahnSeries k Γ).coeff γ := by
          rw [HahnSeries.coeff_add, hprefix, htopcoeff]
          abel

end OneClusterBlockChain

/-- A block chain with source coherence: every state's source is the initial source plus the
formal Hahn sum of all previous block differences.  This is the shape needed at ordinal limit
stages. -/
structure OneClusterCoherentBlockChain
    (ι : Type*) [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    (F : Polynomial (valuationSubring k Γ))
    extends OneClusterBlockChain k Γ ι F where
  coherent_source : ∀ i : ι,
    ofLex (((state i).source - (state ⊥).source : valuationSubring k Γ) :
      HahnField k Γ) =
      ((toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ)

namespace OneClusterCoherentBlockChain

theorem ext_state_block
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    {C D : OneClusterCoherentBlockChain k Γ ι F}
    (hstate : ∀ i, C.state i = D.state i)
    (hblock : ∀ i, Eq.ndrec (C.block i) (hstate i) = D.block i) :
    C = D := by
  cases C with
  | mk Cchain Ccoherent =>
    cases D with
    | mk Dchain Dcoherent =>
      have hchain : Cchain = Dchain :=
        OneClusterBlockChain.ext_state_block k Γ hstate hblock
      cases hchain
      simp

def BotSourceEq
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (s₀ : valuationSubring k Γ) : Prop :=
  (C.state ⊥).source = s₀

def BotBlockNextValEq
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F) (v₀ : Γ) : Prop :=
  ((C.block ⊥).next.val k Γ) = v₀

def BotBlockDiffHahnSeriesEq
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F) (d₀ : HahnSeries Γ k) : Prop :=
  ((C.block ⊥).diffHahnSeries k Γ) = d₀

@[simp]
theorem cast_block_next_val_same
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (e : OneClusterCoherentBlockChain k Γ ι F =
      OneClusterCoherentBlockChain k Γ ι F)
    (i : ι) :
    ((cast e C : OneClusterCoherentBlockChain k Γ ι F).block i).next.val k Γ =
      (C.block i).next.val k Γ := by
  simp

@[simp]
theorem cast_cast_block_next_val_same
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (e₁ : OneClusterCoherentBlockChain k Γ ι F =
      OneClusterCoherentBlockChain k Γ ι F)
    (e₂ : OneClusterCoherentBlockChain k Γ ι F =
      OneClusterCoherentBlockChain k Γ ι F)
    (i : ι) :
    ((cast e₂ (cast e₁ C) : OneClusterCoherentBlockChain k Γ ι F).block i).next.val k Γ =
      (C.block i).next.val k Γ := by
  simp

@[simp]
theorem cast_cast_block_diffHahnSeries_same
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (e₁ : OneClusterCoherentBlockChain k Γ ι F =
      OneClusterCoherentBlockChain k Γ ι F)
    (e₂ : OneClusterCoherentBlockChain k Γ ι F =
      OneClusterCoherentBlockChain k Γ ι F)
    (i : ι) :
    ((cast e₂ (cast e₁ C) : OneClusterCoherentBlockChain k Γ ι F).block i).diffHahnSeries k Γ =
      (C.block i).diffHahnSeries k Γ := by
  simp

theorem state_val_strictMono
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F) :
    StrictMono fun i : ι => (C.state i).val k Γ :=
  C.toOneClusterBlockChain.state_val_strictMono k Γ

theorem not_hartogs
    {F : Polynomial (valuationSubring k Γ)} :
    ¬ Nonempty (OneClusterCoherentBlockChain k Γ (hartogsOrdinal Γ).ToType F) := by
  rintro ⟨C⟩
  exact OneClusterBlockChain.not_hartogs k Γ ⟨C.toOneClusterBlockChain⟩

theorem not_hartogs_iio
    {F : Polynomial (valuationSubring k Γ)} :
    ¬ (letI : OrderBot (Set.Iio (hartogsOrdinal Γ)) :=
          ordinalIioOrderBotOfPos (hartogsOrdinal_pos Γ);
        Nonempty (OneClusterCoherentBlockChain k Γ (Set.Iio (hartogsOrdinal Γ)) F)) := by
  let _ : OrderBot (Set.Iio (hartogsOrdinal Γ)) :=
    ordinalIioOrderBotOfPos (hartogsOrdinal_pos Γ)
  rintro ⟨C⟩
  exact OneClusterBlockChain.not_hartogs_iio k Γ ⟨C.toOneClusterBlockChain⟩

theorem ofLex_succTopState_sub_bot_eq_diffHahnSeriesLimit
    {o : Ordinal}
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ (Set.Iio (Order.succ o)) F) :
    ofLex (((C.toOneClusterBlockChain.succTopState k Γ).source -
      (C.state ⊥).source : valuationSubring k Γ) : HahnField k Γ) =
      C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ := by
  let top : Set.Iio (Order.succ o) := (ordinalIioSuccOrderTop o).top
  have hsub :
      (C.toOneClusterBlockChain.succTopState k Γ).source - (C.state ⊥).source =
        ((C.state top).source - (C.state ⊥).source) +
          ((C.toOneClusterBlockChain.succTopState k Γ).source - (C.state top).source) := by
    dsimp [top]
    abel
  rw [hsub]
  have hmap :
      ofLex ((((C.state top).source - (C.state ⊥).source) +
          ((C.toOneClusterBlockChain.succTopState k Γ).source -
            (C.state top).source) : valuationSubring k Γ) :
          HahnField k Γ) =
        ofLex (((C.state top).source - (C.state ⊥).source : valuationSubring k Γ) :
          HahnField k Γ) +
        ofLex (((C.toOneClusterBlockChain.succTopState k Γ).source -
          (C.state top).source : valuationSubring k Γ) : HahnField k Γ) := by
    change ((ofLexRingHom k Γ).comp
        (algebraMap (valuationSubring k Γ) (HahnField k Γ)))
        (((C.state top).source - (C.state ⊥).source) +
          ((C.toOneClusterBlockChain.succTopState k Γ).source -
            (C.state top).source) : valuationSubring k Γ) =
      ((ofLexRingHom k Γ).comp
        (algebraMap (valuationSubring k Γ) (HahnField k Γ)))
        ((C.state top).source - (C.state ⊥).source : valuationSubring k Γ) +
      ((ofLexRingHom k Γ).comp
        (algebraMap (valuationSubring k Γ) (HahnField k Γ)))
        ((C.toOneClusterBlockChain.succTopState k Γ).source -
          (C.state top).source : valuationSubring k Γ)
    rw [map_add]
  rw [hmap]
  have htopdiff :
      ofLex (((C.toOneClusterBlockChain.succTopState k Γ).source -
        (C.state top).source : valuationSubring k Γ) : HahnField k Γ) =
        (C.toOneClusterBlockChain.topBlock k Γ).diffHahnSeries k Γ := by
    rfl
  rw [C.coherent_source top, htopdiff]
  exact (C.toOneClusterBlockChain.diffHahnSeriesLimit_eq_restrictTop_add_topBlock k Γ).symm

end OneClusterCoherentBlockChain

theorem OneClusterBlockChain.restrictLT_diffHahnSeriesLimit_congr
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F) {i j : ι} (hij : i = j) :
    ((C.restrictLT k Γ i).diffHahnSeriesLimit k Γ) =
      ((C.restrictLT k Γ j).diffHahnSeriesLimit k Γ) := by
  subst j
  rfl

def OneClusterBlockSuccessor.diffLimitValuationSubringOfBot
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ)
    (hbot0 : 0 ≤ (S ⊥).val k Γ) :
    valuationSubring k Γ :=
  OneClusterBlockSuccessor.diffLimitValuationSubring k Γ S B hsep
    (fun i => le_trans hbot0
      (OneClusterBlockSuccessor.bot_state_val_le k Γ S B hsep i))

theorem OneClusterBlockSuccessor.diffLimitValuationSubringOfBot_mem_maximalIdeal
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (S : ι → OneClusterState k Γ F)
    (B : ∀ i : ι, OneClusterBlockSuccessor k Γ (S i))
    (hsep : ∀ {i j : ι}, i < j → (B i).next.val k Γ ≤ (S j).val k Γ)
    (hbotpos : 0 < (S ⊥).val k Γ) :
    OneClusterBlockSuccessor.diffLimitValuationSubringOfBot k Γ S B hsep
        (le_of_lt hbotpos) ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  simpa [OneClusterBlockSuccessor.diffLimitValuationSubringOfBot] using
    OneClusterBlockSuccessor.diffLimitValuationSubring_mem_maximalIdeal
      k Γ S B hsep hbotpos
      (fun i => OneClusterBlockSuccessor.bot_state_val_le k Γ S B hsep i)

namespace OneClusterBlockChain

def diffLimitValuationSubringOfBot
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ) :
    valuationSubring k Γ :=
  OneClusterBlockSuccessor.diffLimitValuationSubringOfBot k Γ
    C.state C.block C.separated hbot0

theorem diffLimitValuationSubringOfBot_mem_maximalIdeal
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F)
    (hbotpos : 0 < (C.state ⊥).val k Γ) :
    C.diffLimitValuationSubringOfBot k Γ (le_of_lt hbotpos) ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  OneClusterBlockSuccessor.diffLimitValuationSubringOfBot_mem_maximalIdeal k Γ
    C.state C.block C.separated hbotpos

def limitSourceFromBot
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ) :
    valuationSubring k Γ :=
  C.diffLimitValuationSubringOfBot k Γ hbot0 + (C.state ⊥).source

theorem limitSourceFromBot_mem_maximalIdeal
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F)
    (hbotpos : 0 < (C.state ⊥).val k Γ) :
    C.limitSourceFromBot k Γ (le_of_lt hbotpos) ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem
    (C.diffLimitValuationSubringOfBot_mem_maximalIdeal k Γ hbotpos)
    (C.state ⊥).source_mem

theorem ofLex_limitSourceFromBot_sub_bot_eq_diffHahnSeriesLimit
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ) :
    ofLex (((C.limitSourceFromBot k Γ hbot0 - (C.state ⊥).source :
      valuationSubring k Γ) : HahnField k Γ)) =
      C.diffHahnSeriesLimit k Γ := by
  have hsub :
      C.limitSourceFromBot k Γ hbot0 - (C.state ⊥).source =
        C.diffLimitValuationSubringOfBot k Γ hbot0 := by
    dsimp [limitSourceFromBot]
    abel
  rw [hsub]
  rfl

end OneClusterBlockChain

namespace OneClusterCoherentBlockChain

theorem ofLex_limitSourceFromBot_sub_state_eq_diff_sub_restrictLT
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ) (i : ι) :
    ofLex ((((C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 -
      (C.state i).source : valuationSubring k Γ) : HahnField k Γ))) =
      C.toOneClusterBlockChain.diffHahnSeriesLimit k Γ -
        ((C.toOneClusterBlockChain.restrictLT k Γ i).diffHahnSeriesLimit k Γ) := by
  let B := C.toOneClusterBlockChain
  have hsub :
      B.limitSourceFromBot k Γ hbot0 - (C.state i).source =
        (B.limitSourceFromBot k Γ hbot0 - (C.state ⊥).source) -
          ((C.state i).source - (C.state ⊥).source) := by
    dsimp [B]
    abel
  rw [hsub]
  have hmap :
      ofLex (((B.limitSourceFromBot k Γ hbot0 - (C.state ⊥).source) -
          ((C.state i).source - (C.state ⊥).source) : valuationSubring k Γ) :
          HahnField k Γ) =
        ofLex (((B.limitSourceFromBot k Γ hbot0 - (C.state ⊥).source :
          valuationSubring k Γ) : HahnField k Γ)) -
          ofLex ((((C.state i).source - (C.state ⊥).source : valuationSubring k Γ) :
            HahnField k Γ)) := by
    change ((ofLexRingHom k Γ).comp
        (algebraMap (valuationSubring k Γ) (HahnField k Γ)))
        (((B.limitSourceFromBot k Γ hbot0 - (C.state ⊥).source) -
          ((C.state i).source - (C.state ⊥).source) : valuationSubring k Γ)) =
        ((ofLexRingHom k Γ).comp
          (algebraMap (valuationSubring k Γ) (HahnField k Γ)))
          (B.limitSourceFromBot k Γ hbot0 - (C.state ⊥).source :
            valuationSubring k Γ) -
          ((ofLexRingHom k Γ).comp
            (algebraMap (valuationSubring k Γ) (HahnField k Γ)))
            ((C.state i).source - (C.state ⊥).source : valuationSubring k Γ)
    rw [map_sub]
  rw [hmap, B.ofLex_limitSourceFromBot_sub_bot_eq_diffHahnSeriesLimit k Γ hbot0,
    C.coherent_source i]

theorem limitSourceFromBot_sub_state_support_subset_Ici
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ) (i : ι) :
    (ofLex ((((C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 -
      (C.state i).source : valuationSubring k Γ) : HahnField k Γ)))).support ⊆
      Set.Ici ((C.state i).val k Γ) := by
  intro γ hγ
  rw [C.ofLex_limitSourceFromBot_sub_state_eq_diff_sub_restrictLT k Γ hbot0 i] at hγ
  exact C.toOneClusterBlockChain.diffHahnSeriesLimit_sub_restrictLT_support_subset_Ici
    k Γ i hγ

theorem state_val_le_limitSourceFromBot_sub_state_addVal
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ) (i : ι) :
    ((C.state i).val k Γ : WithTop Γ) ≤
      addVal k Γ
        (((C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 -
          (C.state i).source : valuationSubring k Γ) : HahnField k Γ)) := by
  rw [addVal_apply]
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro γ hγ
  by_contra hne
  have hmem :
      γ ∈ (ofLex ((((C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 -
        (C.state i).source : valuationSubring k Γ) : HahnField k Γ)))).support := by
    simpa [Function.mem_support] using hne
  exact (not_lt_of_ge
    (C.limitSourceFromBot_sub_state_support_subset_Ici k Γ hbot0 i hmem))
    (WithTop.coe_lt_coe.mp hγ)

theorem state_val_le_limitSourceFromBot_eval_sub_state_eval_addVal
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ) (i : ι) :
    ((C.state i).val k Γ : WithTop Γ) ≤
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            (C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 : HahnField k Γ) -
          (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            ((C.state i).source : HahnField k Γ)) := by
  exact addVal_eval_map_sub_eval_map_ge_of_ge k Γ F
    (x := (C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 : HahnField k Γ))
    (y := ((C.state i).source : HahnField k Γ))
    (δ := (C.state i).val k Γ)
    (by exact (C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0).property)
    (by exact (C.state i).source.property)
    (C.state_val_le_limitSourceFromBot_sub_state_addVal k Γ hbot0 i)

theorem state_val_le_limitSourceFromBot_eval_addVal
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ) (i : ι) :
    ((C.state i).val k Γ : WithTop Γ) ≤
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 : HahnField k Γ)) := by
  let z : HahnField k Γ :=
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      (C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 : HahnField k Γ)
  let zi : HahnField k Γ :=
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      ((C.state i).source : HahnField k Γ)
  have hdiff : ((C.state i).val k Γ : WithTop Γ) ≤ addVal k Γ (z - zi) := by
    exact C.state_val_le_limitSourceFromBot_eval_sub_state_eval_addVal k Γ hbot0 i
  have hstate : ((C.state i).val k Γ : WithTop Γ) ≤ addVal k Γ zi := by
    dsimp [zi]
    rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) F (C.state i).source]
    exact le_of_eq (OneClusterState.val_spec k Γ (C.state i)).symm
  have hdecomp : z = (z - zi) + zi := by
    abel
  change ((C.state i).val k Γ : WithTop Γ) ≤ addVal k Γ z
  rw [hdecomp]
  exact (addVal k Γ).map_le_add hdiff hstate

theorem state_val_lt_limitSourceFromBot_eval_addVal
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hbot0 : 0 ≤ (C.state ⊥).val k Γ)
    (hforward : ∀ i : ι, ∃ j : ι, i < j) (i : ι) :
    ((C.state i).val k Γ : WithTop Γ) <
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (C.toOneClusterBlockChain.limitSourceFromBot k Γ hbot0 : HahnField k Γ)) := by
  rcases hforward i with ⟨j, hij⟩
  exact (WithTop.coe_lt_coe.mpr (C.state_val_strictMono k Γ hij)).trans_le
    (C.state_val_le_limitSourceFromBot_eval_addVal k Γ hbot0 j)

noncomputable def limitStateFromBot
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hbotpos : 0 < (C.state ⊥).val k Γ)
    (hnot :
      ¬ F.IsRoot
        (C.toOneClusterBlockChain.limitSourceFromBot k Γ (le_of_lt hbotpos))) :
    OneClusterState k Γ F where
  source := C.toOneClusterBlockChain.limitSourceFromBot k Γ (le_of_lt hbotpos)
  source_mem := C.toOneClusterBlockChain.limitSourceFromBot_mem_maximalIdeal k Γ hbotpos
  not_root := hnot

theorem state_val_lt_limitStateFromBot_val
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hbotpos : 0 < (C.state ⊥).val k Γ)
    (hforward : ∀ i : ι, ∃ j : ι, i < j)
    (hnot :
      ¬ F.IsRoot
        (C.toOneClusterBlockChain.limitSourceFromBot k Γ (le_of_lt hbotpos)))
    (i : ι) :
    (C.state i).val k Γ <
      (C.limitStateFromBot k Γ hbotpos hnot).val k Γ := by
  have hlt :=
    C.state_val_lt_limitSourceFromBot_eval_addVal k Γ (le_of_lt hbotpos) hforward i
  rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) F
    (C.toOneClusterBlockChain.limitSourceFromBot k Γ (le_of_lt hbotpos))] at hlt
  have hval :
      addVal k Γ
          ((F.eval (C.toOneClusterBlockChain.limitSourceFromBot k Γ (le_of_lt hbotpos) :
            valuationSubring k Γ) : valuationSubring k Γ) : HahnField k Γ) =
        ((C.limitStateFromBot k Γ hbotpos hnot).val k Γ : WithTop Γ) := by
    simpa [limitStateFromBot] using
      OneClusterState.val_spec k Γ (C.limitStateFromBot k Γ hbotpos hnot)
  rw [hval] at hlt
  exact WithTop.coe_lt_coe.mp hlt

end OneClusterCoherentBlockChain

noncomputable def oneClusterInitialStateOfNoRoot
    {F : Polynomial (valuationSubring k Γ)}
    (hno : ¬ RootInMaximalIdeal k Γ F) :
    OneClusterState k Γ F := by
  classical
  have hstate : Nonempty (OneClusterState k Γ F) := by
    rcases rootInMaximalIdeal_or_initialState k Γ F with hroot | hstate
    · exact False.elim (hno hroot)
    · exact hstate
  exact Classical.choice hstate

noncomputable def oneClusterLimitStateOfNoRoot
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ ι F) :
    OneClusterState k Γ F := by
  classical
  have hbotpos : 0 < (C.state ⊥).val k Γ :=
    (C.state ⊥).val_pos_of_cluster_pos k Γ hsmall Nat.zero_lt_one
  have hnot :
      ¬ F.IsRoot
        (C.toOneClusterBlockChain.limitSourceFromBot k Γ (le_of_lt hbotpos)) := by
    intro hroot
    exact hno
      ⟨C.toOneClusterBlockChain.limitSourceFromBot k Γ (le_of_lt hbotpos),
        C.toOneClusterBlockChain.limitSourceFromBot_mem_maximalIdeal k Γ hbotpos,
        hroot⟩
  exact C.limitStateFromBot k Γ hbotpos hnot

theorem state_val_lt_oneClusterLimitStateOfNoRoot_val
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] [OrderBot ι]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (C : OneClusterCoherentBlockChain k Γ ι F)
    (hforward : ∀ i : ι, ∃ j : ι, i < j)
    (i : ι) :
    (C.state i).val k Γ <
      (oneClusterLimitStateOfNoRoot k Γ hsmall hno C).val k Γ := by
  classical
  dsimp [oneClusterLimitStateOfNoRoot]
  exact C.state_val_lt_limitStateFromBot_val k Γ
    ((C.state ⊥).val_pos_of_cluster_pos k Γ hsmall Nat.zero_lt_one)
    hforward
    (by
      intro hroot
      exact hno
        ⟨C.toOneClusterBlockChain.limitSourceFromBot k Γ
            (le_of_lt ((C.state ⊥).val_pos_of_cluster_pos k Γ hsmall Nat.zero_lt_one)),
          C.toOneClusterBlockChain.limitSourceFromBot_mem_maximalIdeal k Γ
            ((C.state ⊥).val_pos_of_cluster_pos k Γ hsmall Nat.zero_lt_one),
          hroot⟩)
    i

end HahnField

end

end HahnKaplanskyRealClosedness
