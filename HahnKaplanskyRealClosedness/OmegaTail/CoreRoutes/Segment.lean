/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaLimit.PositiveRecursion.Core

/-!
# External natural-limit segments and segment systems
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

universe u v

namespace HahnField

variable (k : Type u) (Γ : Type v)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

open PositiveIioCoherentChainAt

private theorem ordinal_le_succ_eq_or_le {p o : Ordinal} (hp : p ≤ Order.succ o) :
    p = Order.succ o ∨ p ≤ o := by
  by_cases htop : p = Order.succ o
  · exact Or.inl htop
  · have hlt : p < Order.succ o := lt_of_le_of_ne hp htop
    rcases ordinal_lt_succ_eq_or_lt hlt with hp_eq | hp_lt
    · exact Or.inr (le_of_eq hp_eq)
    · exact Or.inr (le_of_lt hp_lt)

private theorem ordinal_succ_le_succ_eq_or_le {p o : Ordinal}
    (hp : Order.succ p ≤ Order.succ o) :
    p = o ∨ Order.succ p ≤ o := by
  rcases ordinal_le_succ_eq_or_le hp with htop | hlower
  · left
    have hp_le_o : p ≤ o := by
      have hp_lt : p < Order.succ o := by
        rw [← htop]
        exact Order.lt_succ p
      rcases ordinal_lt_succ_eq_or_lt hp_lt with hp_eq | hp_lt_o
      · exact le_of_eq hp_eq
      · exact le_of_lt hp_lt_o
    have ho_le_p : o ≤ p := by
      have ho_lt : o < Order.succ p := by
        rw [htop]
        exact Order.lt_succ o
      rcases ordinal_lt_succ_eq_or_lt ho_lt with ho_eq | ho_lt_p
      · exact le_of_eq ho_eq
      · exact le_of_lt ho_lt_p
    exact le_antisymm hp_le_o ho_le_p
  · exact Or.inr hlower

/-- Final external natural-limit recursion data.

This is the internal target for the positive generated core: a single external chain `R`, its
successor equation, natural components on each external limit below-chain, and the agreement that
the limit value of `R` is the natural-components limit step. -/
structure KOneClusterPositiveFinalExternalNaturalLimitStepData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) where
  R : ∀ o : Ordinal.{v}, PositiveIioCoherentChainAt k Γ o F
  hsucc :
    ∀ o : Ordinal.{v},
      R (Order.succ o) =
        PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno (R o)
  hnat :
    ∀ {o : Ordinal.{v}} (ho : Order.IsSuccLimit o),
      let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
      C.NaturalComponents k Γ ho
  hlimit :
    ∀ {o : Ordinal.{v}} (ho : Order.IsSuccLimit o),
      let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
      R o = C.limitStepOfNaturalComponents k Γ ho (hnat ho)

/-- A coherent initial segment of the final external natural-limit recursion.

The final recursion cannot be assembled by proving `NaturalComponents` after defining the chain:
the limit branch needs the lower natural data while defining the current value.  This package is
the internal shape for that simultaneous recursion on an initial segment `Set.Iic o`. -/
structure KOneClusterPositiveFinalExternalNaturalSegment
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (o : Ordinal.{v}) where
  R : ∀ p : Set.Iic o, PositiveIioCoherentChainAt k Γ p.1 F
  hsucc :
    ∀ {p : Ordinal.{v}} (hp : Order.succ p ≤ o),
      R ⟨Order.succ p, hp⟩ =
        PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
          (R ⟨p, le_trans (le_of_lt (Order.lt_succ p)) hp⟩)
  hnat :
    ∀ {p : Ordinal.{v}} (hp : p ≤ o) (hpLimit : Order.IsSuccLimit p),
      let C : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => R ⟨i.1, le_trans (le_of_lt i.2) hp⟩
      C.NaturalComponents k Γ hpLimit
  hlimit :
    ∀ {p : Ordinal.{v}} (hp : p ≤ o) (hpLimit : Order.IsSuccLimit p),
      let C : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => R ⟨i.1, le_trans (le_of_lt i.2) hp⟩
      R ⟨p, hp⟩ = C.limitStepOfNaturalComponents k Γ hpLimit (hnat hp hpLimit)

/-- Extensionality for final external natural-limit segments. -/
theorem KOneClusterPositiveFinalExternalNaturalSegment.ext_R
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    {S T : KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o}
    (hR : ∀ p : Set.Iic o, S.R p = T.R p) :
    S = T := by
  cases S with
  | mk SR Shsucc Shnat Shlimit =>
      cases T with
      | mk TR Thsucc Thnat Thlimit =>
          simp only at hR
          have h : SR = TR := funext hR
          cases h
          rfl

/-- The `R` field of a final external natural-limit segment is determined by its recursion laws. -/
theorem KOneClusterPositiveFinalExternalNaturalSegment.R_eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (S T : KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o)
    (p : Set.Iic o) :
    S.R p = T.R p := by
  let P : Ordinal.{v} → Prop := fun p =>
    ∀ (hp : p ≤ o), S.R ⟨p, hp⟩ = T.R ⟨p, hp⟩
  have hmain : P p.1 := by
    induction p.1 using Ordinal.limitRecOn with
    | zero =>
        intro hp
        funext hpos
        exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
    | add_one q ih =>
        intro hp
        have hq : q ≤ o := le_trans (le_of_lt (Order.lt_succ q)) hp
        change S.R ⟨Order.succ q, hp⟩ = T.R ⟨Order.succ q, hp⟩
        rw [S.hsucc hp, T.hsucc hp, ih hq]
    | limit q hqLimit IH =>
        intro hp
        let CS : PositiveIioCoherentChainAtBelow k Γ q F :=
          fun i => S.R ⟨i.1, le_trans (le_of_lt i.2) hp⟩
        let CT : PositiveIioCoherentChainAtBelow k Γ q F :=
          fun i => T.R ⟨i.1, le_trans (le_of_lt i.2) hp⟩
        have hC : CS = CT := by
          funext i
          exact IH i.1 i.2 (le_trans (le_of_lt i.2) hp)
        change S.R ⟨q, hp⟩ = T.R ⟨q, hp⟩
        calc
          S.R ⟨q, hp⟩ =
              CS.limitStepOfNaturalComponents k Γ hqLimit (S.hnat hp hqLimit) := by
            exact S.hlimit hp hqLimit
          _ = CT.limitStepOfNaturalComponents k Γ hqLimit (T.hnat hp hqLimit) := by
            exact PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_congr
              (k := k) (Γ := Γ) hqLimit hC (S.hnat hp hqLimit) (T.hnat hp hqLimit)
          _ = T.R ⟨q, hp⟩ := (T.hlimit hp hqLimit).symm
  exact hmain p.2

/-- Final external natural-limit segments at the same ordinal are unique. -/
theorem KOneClusterPositiveFinalExternalNaturalSegment.eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (S T : KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o) :
    S = T :=
  KOneClusterPositiveFinalExternalNaturalSegment.ext_R
    (k := k) (Γ := Γ) (fun p =>
      KOneClusterPositiveFinalExternalNaturalSegment.R_eq (k := k) (Γ := Γ) S T p)

/-- The zero initial segment for the final external natural-limit recursion. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegment.zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F} :
    KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno 0 where
  R := fun p hpos => False.elim ((not_lt_of_ge p.2) hpos)
  hsucc := by
    intro p hp
    exact False.elim
      ((not_lt_of_ge hp) (lt_of_le_of_lt bot_le (Order.lt_succ p)))
  hnat := by
    intro p hp hpLimit
    have hp0 : p = 0 := le_antisymm hp bot_le
    subst p
    exact False.elim (Order.not_isSuccLimit_bot hpLimit)
  hlimit := by
    intro p hp hpLimit
    have hp0 : p = 0 := le_antisymm hp bot_le
    subst p
    exact False.elim (Order.not_isSuccLimit_bot hpLimit)

/-- Successor extension of a final external natural-limit initial segment. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegment.succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (S : KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o) :
    KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno (Order.succ o) := by
  let Rsucc : ∀ p : Set.Iic (Order.succ o), PositiveIioCoherentChainAt k Γ p.1 F := fun p =>
    if hlow : p.1 ≤ o then
      S.R ⟨p.1, hlow⟩
    else
      have htop : p.1 = Order.succ o :=
        (ordinal_le_succ_eq_or_le p.2).resolve_right hlow
      htop.symm ▸
        PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
          (S.R ⟨o, (show o ≤ o from le_rfl)⟩)
  have Rsucc_lower :
      ∀ {p : Ordinal} (hp_succ : p ≤ Order.succ o) (hp_low : p ≤ o),
        Rsucc ⟨p, hp_succ⟩ = S.R ⟨p, hp_low⟩ := by
    intro p hp_succ hp_low
    simp [Rsucc, hp_low]
  have Rsucc_top :
      ∀ (hp_succ : Order.succ o ≤ Order.succ o),
        Rsucc ⟨Order.succ o, hp_succ⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (S.R ⟨o, (show o ≤ o from le_rfl)⟩) := by
    intro hp_succ
    simp [Rsucc]
  have hnatSucc :
      ∀ {p : Ordinal} (hp : p ≤ Order.succ o) (hpLimit : Order.IsSuccLimit p),
        let C : PositiveIioCoherentChainAtBelow k Γ p F :=
          fun i => Rsucc ⟨i.1, le_trans (le_of_lt i.2) hp⟩
        C.NaturalComponents k Γ hpLimit := by
    intro p hp hpLimit
    by_cases hp_lower : p ≤ o
    · let Csucc : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => Rsucc ⟨i.1, le_trans (le_of_lt i.2) hp⟩
      let Clower : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => S.R ⟨i.1, le_trans (le_of_lt i.2) hp_lower⟩
      have hC : Csucc = Clower := by
        funext i
        exact Rsucc_lower (le_trans (le_of_lt i.2) hp) (le_trans (le_of_lt i.2) hp_lower)
      change Csucc.NaturalComponents k Γ hpLimit
      rw [hC]
      exact S.hnat hp_lower hpLimit
    · have hp_eq : p = Order.succ o :=
        (ordinal_le_succ_eq_or_le hp).resolve_right hp_lower
      subst p
      exact False.elim (Order.not_isSuccLimit_succ o hpLimit)
  refine
    { R := Rsucc
      hsucc := ?_
      hnat := hnatSucc
      hlimit := ?_ }
  · intro p hp
    by_cases hp_lower : Order.succ p ≤ o
    · have hp_pred_lower : p ≤ o := le_trans (le_of_lt (Order.lt_succ p)) hp_lower
      rw [Rsucc_lower hp hp_lower, Rsucc_lower (le_trans (le_of_lt (Order.lt_succ p)) hp)
        hp_pred_lower]
      exact S.hsucc hp_lower
    · have hp_eq : p = o := (ordinal_succ_le_succ_eq_or_le hp).resolve_right hp_lower
      subst p
      rw [Rsucc_top hp, Rsucc_lower (le_trans (le_of_lt (Order.lt_succ o)) hp)
        (show o ≤ o from le_rfl)]
  · intro p hp hpLimit
    by_cases hp_lower : p ≤ o
    · let Csucc : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => Rsucc ⟨i.1, le_trans (le_of_lt i.2) hp⟩
      let Clower : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => S.R ⟨i.1, le_trans (le_of_lt i.2) hp_lower⟩
      have hC : Csucc = Clower := by
        funext i
        exact Rsucc_lower (le_trans (le_of_lt i.2) hp) (le_trans (le_of_lt i.2) hp_lower)
      have hstep :
          Csucc.limitStepOfNaturalComponents k Γ hpLimit (hnatSucc hp hpLimit) =
            Clower.limitStepOfNaturalComponents k Γ hpLimit (S.hnat hp_lower hpLimit) := by
        exact PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_congr
          (k := k) (Γ := Γ) hpLimit hC (hnatSucc hp hpLimit) (S.hnat hp_lower hpLimit)
      change Rsucc ⟨p, hp⟩ =
        Csucc.limitStepOfNaturalComponents k Γ hpLimit (hnatSucc hp hpLimit)
      rw [Rsucc_lower hp hp_lower]
      rw [hstep]
      exact S.hlimit hp_lower hpLimit
    · have hp_eq : p = Order.succ o :=
        (ordinal_le_succ_eq_or_le hp).resolve_right hp_lower
      subst p
      exact False.elim (Order.not_isSuccLimit_succ o hpLimit)

@[simp] theorem KOneClusterPositiveFinalExternalNaturalSegment.succ_R_lower
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o p : Ordinal.{v}}
    (S : KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o)
    (hp : p ≤ o) :
    (S.succ (k := k) (Γ := Γ)).R
        ⟨p, le_trans hp (le_of_lt (Order.lt_succ o))⟩ =
      S.R ⟨p, hp⟩ := by
  have hnot : p ≠ Order.succ o := by
    intro h
    exact not_lt_of_ge hp (by rw [h]; exact Order.lt_succ o)
  rw [KOneClusterPositiveFinalExternalNaturalSegment.succ]
  simp only
  rw [dif_pos hp]

/-- A coherent system of final external natural-limit initial segments below `o`.

This is the recursion invariant used to build the final segment family: for every `p ≤ o` it
stores the segment at `p`, and its coherence field identifies the restriction of a larger segment
with the top point of the smaller segment. -/
structure KOneClusterPositiveFinalExternalNaturalSegmentSystem
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (o : Ordinal.{v}) where
  segment :
    ∀ p : Set.Iic o,
      KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno p.1
  coherent :
    ∀ {p q : Ordinal.{v}} (hp : p ≤ o) (hq : q ≤ p),
      ((segment ⟨p, hp⟩).R ⟨q, hq⟩) =
        ((segment ⟨q, le_trans hq hp⟩).R ⟨q, (show q ≤ q from le_rfl)⟩)

/-- Extensionality for final external natural-limit segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.ext_segment
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    {S T : KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno o}
    (h :
      ∀ p : Set.Iic o, S.segment p = T.segment p) :
    S = T := by
  cases S with
  | mk Ssegment Scoherent =>
      cases T with
      | mk Tsegment Tcoherent =>
          simp only at h
          have hsegment : Ssegment = Tsegment := funext h
          cases hsegment
          rfl

/-- Final external natural-limit segment systems at the same ordinal are unique. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (S T : KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno o) :
    S = T :=
  KOneClusterPositiveFinalExternalNaturalSegmentSystem.ext_segment
    (k := k) (Γ := Γ) (fun p =>
      KOneClusterPositiveFinalExternalNaturalSegment.eq (k := k) (Γ := Γ)
        (S.segment p) (T.segment p))

/-- The zero coherent segment system. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystem.zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F} :
    KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno 0 where
  segment := fun p =>
    have hp0 : p.1 = 0 := le_antisymm p.2 bot_le
    hp0.symm ▸ KOneClusterPositiveFinalExternalNaturalSegment.zero (k := k) (Γ := Γ)
  coherent := by
    intro p q hp hq
    have hp0 : p = 0 := le_antisymm hp bot_le
    subst p
    have hq0 : q = 0 := le_antisymm hq bot_le
    subst q
    rfl

/-- Successor extension of a coherent system of final external natural-limit initial segments. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystem.succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (S : KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno o) :
    KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno (Order.succ o) := by
  let topSegment : KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno
      (Order.succ o) :=
    (S.segment ⟨o, (show o ≤ o from le_rfl)⟩).succ (k := k) (Γ := Γ)
  let segmentSucc :
      ∀ p : Set.Iic (Order.succ o),
        KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno p.1 := fun p =>
    if hlow : p.1 ≤ o then
      S.segment ⟨p.1, hlow⟩
    else
      have htop : p.1 = Order.succ o :=
        (ordinal_le_succ_eq_or_le p.2).resolve_right hlow
      htop.symm ▸ topSegment
  have segment_lower :
      ∀ {p : Ordinal} (hp_succ : p ≤ Order.succ o) (hp_low : p ≤ o),
        segmentSucc ⟨p, hp_succ⟩ = S.segment ⟨p, hp_low⟩ := by
    intro p hp_succ hp_low
    simp [segmentSucc, hp_low]
  have segment_top :
      ∀ (hp_succ : Order.succ o ≤ Order.succ o),
        segmentSucc ⟨Order.succ o, hp_succ⟩ = topSegment := by
    intro hp_succ
    simp [segmentSucc]
  refine
    { segment := segmentSucc
      coherent := ?_ }
  intro p q hp hq
  by_cases hp_low : p ≤ o
  · have hq_low : q ≤ o := le_trans hq hp_low
    rw [segment_lower hp hp_low, segment_lower (le_trans hq hp) hq_low]
    exact S.coherent hp_low hq
  · have hp_top : p = Order.succ o :=
      (ordinal_le_succ_eq_or_le hp).resolve_right hp_low
    subst p
    by_cases hq_low : q ≤ o
    · rw [segment_top hp, segment_lower (le_trans hq hp) hq_low]
      calc
        (topSegment.R ⟨q, hq⟩) =
            ((S.segment ⟨o, (show o ≤ o from le_rfl)⟩).R ⟨q, hq_low⟩) := by
          exact KOneClusterPositiveFinalExternalNaturalSegment.succ_R_lower
            (k := k) (Γ := Γ) (S.segment ⟨o, (show o ≤ o from le_rfl)⟩) hq_low
        _ = ((S.segment ⟨q, le_trans hq_low (show o ≤ o from le_rfl)⟩).R
              ⟨q, (show q ≤ q from le_rfl)⟩) := by
          exact S.coherent (show o ≤ o from le_rfl) hq_low
    · have hq_top : q = Order.succ o :=
      (ordinal_le_succ_eq_or_le (le_trans hq hp)).resolve_right hq_low
      subst q
      rw [segment_top hp]

@[simp] theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.succ_segment_lower
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o p : Ordinal.{v}}
    (S : KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno o)
    (hp : p ≤ o) :
    (S.succ (k := k) (Γ := Γ)).segment
        ⟨p, le_trans hp (le_of_lt (Order.lt_succ o))⟩ =
      S.segment ⟨p, hp⟩ := by
  unfold KOneClusterPositiveFinalExternalNaturalSegmentSystem.succ
  simp [hp]

/-- The below-chain presented by a family of coherent segment systems below a target `o`. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1) :
    PositiveIioCoherentChainAtBelow k Γ o F :=
  fun p => ((Sbelow p).segment ⟨p.1, (show p.1 ≤ p.1 from le_rfl)⟩).R
    ⟨p.1, (show p.1 ≤ p.1 from le_rfl)⟩

/-- The below-chain extracted from lower segment systems satisfies the successor equation. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o p : Ordinal.{v}}
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1)
    (hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩)
    (hp : Order.succ p < o) :
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow) ⟨Order.succ p, hp⟩ =
      PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
        ((KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
          (k := k) (Γ := Γ) Sbelow) ⟨p, (Order.lt_succ p).trans hp⟩) := by
  let Ssucc := Sbelow ⟨Order.succ p, hp⟩
  let topSeg := Ssucc.segment ⟨Order.succ p, (show Order.succ p ≤ Order.succ p from le_rfl)⟩
  calc
    (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow) ⟨Order.succ p, hp⟩ =
        topSeg.R ⟨Order.succ p, (show Order.succ p ≤ Order.succ p from le_rfl)⟩ := rfl
    _ = PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
          (topSeg.R ⟨p, le_of_lt (Order.lt_succ p)⟩) := by
        exact topSeg.hsucc (show Order.succ p ≤ Order.succ p from le_rfl)
    _ = PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
          ((KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
            (k := k) (Γ := Γ) Sbelow) ⟨p, (Order.lt_succ p).trans hp⟩) := by
        exact congrArg
          (PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno)
          ((Ssucc.coherent
            (show Order.succ p ≤ Order.succ p from le_rfl)
            (le_of_lt (Order.lt_succ p))).trans
            (by
              rw [hSbelow hp (le_of_lt (Order.lt_succ p))]
              rfl))

/-- Top branch of the successor-index stage comparison for the below-chain extracted from
coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_top
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
    {p : Ordinal} {hp : Order.succ p < o} {i : Set.Iio o}
    (hi : i.1 = p) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
        change i.1 < Order.succ p
        rw [hi]
        exact Order.lt_succ p) =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ p, hp⟩ : Set.Iio o) from by
        change i.1 < Order.succ p
        rw [hi]
        exact Order.lt_succ p) =
      C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  exact C.succStageRestrictedPrefix_top_of_succIndex
    k Γ hsmall hunit hno ho
    (fun {q} hq =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
        (k := k) (Γ := Γ) Sbelow hSbelow hq)
    hi

/-- Successor predecessor branch of the successor-index stage comparison for the below-chain
extracted from coherent lower segment systems. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_stageSucc_pred_succ
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
    {q : Ordinal} {hp : Order.succ (Order.succ q) < o}
    (hpred :
      let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
        (k := k) (Γ := Γ) Sbelow
      ∀ {i : Set.Iio o} (hi : i.1 < q),
        C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
          (show i < (⟨Order.succ q,
              (Order.lt_succ (Order.succ q)).trans hp⟩ : Set.Iio o) from by
            exact hi.trans (Order.lt_succ q)) =
        C.succStagePrefixDiffHahnSeriesLimit k Γ ho i)
    {i : Set.Iio o} (hi : i.1 < q) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o) from by
        exact (hi.trans (Order.lt_succ q)).trans (Order.lt_succ (Order.succ q))) =
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  change C.succStageRestrictedPrefixDiffHahnSeriesLimit k Γ ho
      (show i < (⟨Order.succ (Order.succ q), hp⟩ : Set.Iio o) from by
        exact (hi.trans (Order.lt_succ q)).trans (Order.lt_succ (Order.succ q))) =
    C.succStagePrefixDiffHahnSeriesLimit k Γ ho i
  exact C.succStageRestrictedPrefix_pred_of_succSuccIndex
    k Γ hsmall hunit hno ho
    (fun {p} hp =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_succ
        (k := k) (Γ := Γ) Sbelow hSbelow hp)
    hpred hi

/-- A local below-chain satisfying the successor equation has the canonical bottom successor
stage chain. -/
@[simp]
theorem PositiveIioCoherentChainAtBelow.succStageChain_bot_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩)) :
    C.succStageChain k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o) =
      OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno := by
  change C ⟨Order.succ 0, ho.succ_lt ho.bot_lt⟩
      (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal))) =
    OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno
  have hsucc0 := hsucc (p := (0 : Ordinal)) (ho.succ_lt ho.bot_lt)
  calc
    C ⟨Order.succ 0, ho.succ_lt ho.bot_lt⟩
        (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal))) =
        (PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
          (C ⟨0, ho.bot_lt⟩))
          (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal))) := by
          exact congrFun hsucc0 _
    _ = OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno := by
        exact PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
          k Γ hsmall hunit hno (C ⟨0, ho.bot_lt⟩)
          (lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal)))

/-- A local below-chain satisfying the successor equation has the canonical bottom limit state. -/
@[simp]
theorem PositiveIioCoherentChainAtBelow.limitState_bot_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩)) :
    C.limitState k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o) =
      oneClusterInitialStateOfNoRoot k Γ hno := by
  unfold PositiveIioCoherentChainAtBelow.limitState
  rw [PositiveIioCoherentChainAtBelow.succStageChain_bot_of_succ
    (k := k) (Γ := Γ) ho C hsucc]
  exact OneClusterCoherentBlockChain.initialOfNoRoot_topState k Γ hsmall hunit hno

/-- A local below-chain satisfying the successor equation has the canonical bottom limit-state
source. -/
@[simp]
theorem PositiveIioCoherentChainAtBelow.limitState_bot_source_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩)) :
    (C.limitState k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o)).source =
      (oneClusterInitialStateOfNoRoot k Γ hno).source := by
  rw [PositiveIioCoherentChainAtBelow.limitState_bot_of_succ
    (k := k) (Γ := Γ) ho C hsucc]

/-- A local below-chain satisfying the successor equation has the canonical zero-index limit
block next value. -/
@[simp]
theorem PositiveIioCoherentChainAtBelow.limitBlock_bot_next_val_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩)) :
    ((C.limitBlock k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o)).next.val k Γ) =
      (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ := by
  calc
    ((C.limitBlock k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o)).next.val k Γ)
        =
      ((OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno
        |>.toOneClusterBlockChain.topBlock k Γ).next.val k Γ) := by
        unfold PositiveIioCoherentChainAtBelow.limitBlock
        exact PositiveIioCoherentChain.succEndpointTopBlock_next_val_eq_of_eq k Γ
          (PositiveIioCoherentChainAtBelow.succStageChain_bot_of_succ
            (k := k) (Γ := Γ) ho C hsucc)
    _ = (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ := by
        exact OneClusterCoherentBlockChain.initialOfNoRoot_topBlock_next_val
          k Γ hsmall hunit hno

/-- A local below-chain satisfying the successor equation has the canonical zero-index limit
block next value at every index whose ordinal value is zero. -/
theorem PositiveIioCoherentChainAtBelow.limitBlock_next_val_of_val_eq_zero_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩))
    (i : Set.Iio o) (hi : (i : Ordinal) = 0) :
    ((C.limitBlock k Γ ho i).next.val k Γ) =
      (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ := by
  have hbot : i = (⟨0, ho.bot_lt⟩ : Set.Iio o) := by
    apply Subtype.ext
    exact hi
  rw [hbot]
  exact PositiveIioCoherentChainAtBelow.limitBlock_bot_next_val_of_succ
    (k := k) (Γ := Γ) ho C hsucc

/-- A local below-chain satisfying the successor equation has the canonical zero-index limit
block Hahn-series difference. -/
@[simp]
theorem PositiveIioCoherentChainAtBelow.limitBlock_bot_diffHahnSeries_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩)) :
    ((C.limitBlock k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o)).diffHahnSeries k Γ) =
      (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ := by
  calc
    ((C.limitBlock k Γ ho (⟨0, ho.bot_lt⟩ : Set.Iio o)).diffHahnSeries k Γ)
        =
      ((OneClusterCoherentBlockChain.initialOfNoRoot k Γ hsmall hunit hno
        |>.toOneClusterBlockChain.topBlock k Γ).diffHahnSeries k Γ) := by
        unfold PositiveIioCoherentChainAtBelow.limitBlock
        exact PositiveIioCoherentChain.succEndpointTopBlock_diffHahnSeries_eq_of_eq k Γ
          (PositiveIioCoherentChainAtBelow.succStageChain_bot_of_succ
            (k := k) (Γ := Γ) ho C hsucc)
    _ = (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
        (oneClusterInitialStateOfNoRoot k Γ hno)).diffHahnSeries k Γ := by
        exact OneClusterCoherentBlockChain.initialOfNoRoot_topBlock_diffHahnSeries
          k Γ hsmall hunit hno

/-- A local below-chain satisfying the successor equation computes positive-index limit blocks
from the corresponding successor stage. -/
theorem PositiveIioCoherentChainAtBelow.limitBlock_diffHahnSeries_of_pos_of_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (C : PositiveIioCoherentChainAtBelow k Γ o F)
    (hsucc :
      ∀ {p : Ordinal} (hp : Order.succ p < o),
        C ⟨Order.succ p, hp⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            (C ⟨p, (Order.lt_succ p).trans hp⟩))
    (i : Set.Iio o) (hi : (0 : Ordinal) < i.1) :
    ((C.limitBlock k Γ ho i).diffHahnSeries k Γ) =
      (((((C i) hi).succOfNoRoot k Γ hi hsmall hunit hno).succEndpointTopBlock k Γ)
        |>.diffHahnSeries k Γ) := by
  unfold PositiveIioCoherentChainAtBelow.limitBlock
  exact PositiveIioCoherentChain.succEndpointTopBlock_diffHahnSeries_eq_of_eq k Γ
    (PositiveIioCoherentChainAtBelow.succStageChain_of_pos
      (k := k) (Γ := Γ) hsmall hunit hno ho C i
      (hsucc (ho.succ_lt i.2)) hi)

/-- Every point of a final natural segment carries the canonical bottom source and bottom next
value invariants. -/
theorem KOneClusterPositiveFinalExternalNaturalSegment.botInvariants
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o p : Ordinal.{v}}
    (S : KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o)
    (hp : p ≤ o) :
    (S.R ⟨p, hp⟩).BotSourceEq k Γ (oneClusterInitialStateOfNoRoot k Γ hno).source ∧
      (S.R ⟨p, hp⟩).BotBlockNextValEq k Γ
        ((oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
          (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ) := by
  let v₀ : Γ :=
    (oneClusterBlockSuccessorOfNoRoot k Γ hsmall hunit hno
      (oneClusterInitialStateOfNoRoot k Γ hno)).next.val k Γ
  revert hp
  induction p using Ordinal.limitRecOn with
  | zero =>
      intro hp
      refine ⟨?_, ?_⟩
      · intro hpos
        exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
      · intro hpos
        exact False.elim ((lt_irrefl (0 : Ordinal)) hpos)
  | add_one p ih =>
      intro hp
      have hpred : p ≤ o := le_trans (le_of_lt (Order.lt_succ p)) hp
      change
        (S.R ⟨Order.succ p, hp⟩).BotSourceEq k Γ
            (oneClusterInitialStateOfNoRoot k Γ hno).source ∧
          (S.R ⟨Order.succ p, hp⟩).BotBlockNextValEq k Γ v₀
      rw [S.hsucc hp]
      by_cases hpos : (0 : Ordinal) < p
      · refine ⟨?_, ?_⟩
        · exact PositiveIioCoherentChainAt.succOfNoRoot_botSourceEq_of_pos
            k Γ hsmall hunit hno (S.R ⟨p, hpred⟩) hpos (ih hpred).1
        · exact PositiveIioCoherentChainAt.succOfNoRoot_botBlockNextValEq_of_pos
            k Γ hsmall hunit hno (S.R ⟨p, hpred⟩) hpos (ih hpred).2
      · have hp0 : p = 0 := le_antisymm (le_of_not_gt hpos) bot_le
        subst p
        refine ⟨?_, ?_⟩
        · intro hsucc0
          rw [PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
            k Γ hsmall hunit hno (S.R ⟨0, hpred⟩) hsucc0]
          exact OneClusterCoherentBlockChain.initialOfNoRoot_botSourceEq
            k Γ hsmall hunit hno
        · intro hsucc0
          rw [PositiveIioCoherentChainAt.succOfNoRoot_apply_zero
            k Γ hsmall hunit hno (S.R ⟨0, hpred⟩) hsucc0]
          exact OneClusterCoherentBlockChain.initialOfNoRoot_botBlockNextValEq
            k Γ hsmall hunit hno
  | limit p hpLimit IH =>
      intro hp
      let C : PositiveIioCoherentChainAtBelow k Γ p F :=
        fun i => S.R ⟨i.1, le_trans (le_of_lt i.2) hp⟩
      have hnat : C.NaturalComponents k Γ hpLimit := S.hnat hp hpLimit
      have hlimit :
          S.R ⟨p, hp⟩ = C.limitStepOfNaturalComponents k Γ hpLimit hnat := by
        exact S.hlimit hp hpLimit
      have hCsource :
          C.BotSourceEq k Γ (oneClusterInitialStateOfNoRoot k Γ hno).source := by
        intro i hi
        exact (IH i.1 i.2 (le_trans (le_of_lt i.2) hp)).1 hi
      have hlimitSource :
          (letI : OrderBot (Set.Iio p) := ordinalIioOrderBot hpLimit
           (C.limitState k Γ hpLimit ⊥).source) =
            (oneClusterInitialStateOfNoRoot k Γ hno).source := by
        rcases hnat with ⟨s₀, hsource, hbot, _hnext, _hlimitPrefix, _hstagePrefix⟩
        let ibot : Set.Iio p := ⟨Order.succ 0, hpLimit.succ_lt hpLimit.bot_lt⟩
        have hposBot : (0 : Ordinal) < ibot.1 :=
          lt_of_le_of_lt bot_le (Order.lt_succ (0 : Ordinal))
        have hs₀ : s₀ = (oneClusterInitialStateOfNoRoot k Γ hno).source := by
          exact (hsource ibot hposBot).symm.trans (hCsource ibot hposBot)
        simpa [hs₀] using hbot
      have hsuccC :
          ∀ {q : Ordinal} (hq : Order.succ q < p),
            C ⟨Order.succ q, hq⟩ =
              PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
                (C ⟨q, (Order.lt_succ q).trans hq⟩) := by
        intro q hq
        exact S.hsucc (le_trans (le_of_lt hq) hp)
      have hlimitBotNext :
          ∀ i : Set.Iio p, (i : Ordinal) = 0 →
            (C.limitBlock k Γ hpLimit i).next.val k Γ = v₀ := by
        intro i hi
        exact C.limitBlock_next_val_of_val_eq_zero_of_succ
          (k := k) (Γ := Γ) hpLimit hsuccC i hi
      rw [hlimit]
      refine ⟨?_, ?_⟩
      · exact C.limitStepOfNaturalComponents_botSourceEq k Γ hpLimit hnat hlimitSource
      · exact C.limitStepOfNaturalComponents_botBlockNextValEq k Γ hpLimit hnat hlimitBotNext

/-- Lower natural components extracted from coherent segment systems below a target. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1)
    (hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩)
    (j : Set.Iio o) (hj : Order.IsSuccLimit j.1) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
      fun i => C ⟨i.1, (show i.1 < o from i.2.trans j.2)⟩
    Cj.NaturalComponents k Γ hj := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let Sj := Sbelow j
  let topSeg := Sj.segment ⟨j.1, (show j.1 ≤ j.1 from le_rfl)⟩
  let Cseg : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun i => topSeg.R ⟨i.1, (show i.1 ≤ j.1 from le_of_lt i.2)⟩
  let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun i => C ⟨i.1, (show i.1 < o from i.2.trans j.2)⟩
  have hC : Cseg = Cj := by
    funext i
    exact (Sj.coherent (show j.1 ≤ j.1 from le_rfl) (le_of_lt i.2)).trans
      (by
        rw [hSbelow j.2 (le_of_lt i.2)]
        rfl)
  change Cj.NaturalComponents k Γ hj
  rw [← hC]
  exact topSeg.hnat (show j.1 ≤ j.1 from le_rfl) hj

/-- Lower natural limit-step equations extracted from coherent segment systems below a target. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hlimit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1)
    (hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩)
    (j : Set.Iio o) (hj : Order.IsSuccLimit j.1) :
    let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
      (k := k) (Γ := Γ) Sbelow
    let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
      fun i => C ⟨i.1, (show i.1 < o from i.2.trans j.2)⟩
    C j = Cj.limitStepOfNaturalComponents k Γ hj
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
        (k := k) (Γ := Γ) Sbelow hSbelow j hj) := by
  let C := KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain
    (k := k) (Γ := Γ) Sbelow
  let Sj := Sbelow j
  let topSeg := Sj.segment ⟨j.1, (show j.1 ≤ j.1 from le_rfl)⟩
  let Cseg : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun i => topSeg.R ⟨i.1, (show i.1 ≤ j.1 from le_of_lt i.2)⟩
  let Cj : PositiveIioCoherentChainAtBelow k Γ j.1 F :=
    fun i => C ⟨i.1, (show i.1 < o from i.2.trans j.2)⟩
  have hC : Cseg = Cj := by
    funext i
    exact (Sj.coherent (show j.1 ≤ j.1 from le_rfl) (le_of_lt i.2)).trans
      (by
        rw [hSbelow j.2 (le_of_lt i.2)]
        rfl)
  have hstep :
      Cseg.limitStepOfNaturalComponents k Γ hj
          (topSeg.hnat (show j.1 ≤ j.1 from le_rfl) hj) =
        Cj.limitStepOfNaturalComponents k Γ hj
          (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
            (k := k) (Γ := Γ) Sbelow hSbelow j hj) := by
    exact PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_congr
      (k := k) (Γ := Γ) hj hC
      (topSeg.hnat (show j.1 ≤ j.1 from le_rfl) hj)
      (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
        (k := k) (Γ := Γ) Sbelow hSbelow j hj)
  calc
    C j = topSeg.R ⟨j.1, (show j.1 ≤ j.1 from le_rfl)⟩ := rfl
    _ = Cseg.limitStepOfNaturalComponents k Γ hj
          (topSeg.hnat (show j.1 ≤ j.1 from le_rfl) hj) := by
        exact topSeg.hlimit (show j.1 ≤ j.1 from le_rfl) hj
    _ = Cj.limitStepOfNaturalComponents k Γ hj
          (KOneClusterPositiveFinalExternalNaturalSegmentSystem.belowChain_hnat
            (k := k) (Γ := Γ) Sbelow hSbelow j hj) := hstep

end HahnField

end

end HahnKaplanskyRealClosedness
