/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaTail.CoreRoutes.LimitExtension
import HahnKaplanskyRealClosedness.OmegaTail.Data

/-!
# Ordinal towers and global stack recursion
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

/-- A coherent tower of final external natural-limit segment systems up to `o`.

This is the recursion invariant for the final ordinal recursion.  The `system` field stores the
already constructed coherent segment system at every `p ≤ o`, and `coherent` identifies the
restriction of the larger system at `p` with the top system at `q`. -/
structure KOneClusterPositiveFinalExternalNaturalSegmentSystemTower
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (o : Ordinal.{v}) where
  system :
    ∀ p : Set.Iic o,
      KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1
  coherent :
    ∀ {p q : Ordinal.{v}} (hp : p ≤ o) (hq : q ≤ p),
      (system ⟨p, hp⟩).segment ⟨q, hq⟩ =
        (system ⟨q, le_trans hq hp⟩).segment ⟨q, (show q ≤ q from le_rfl)⟩

/-- Extensionality for final external natural-limit system towers.

The coherence field is proposition-valued, so pointwise equality of the stored systems determines
the tower. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.ext_system
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    {T U : KOneClusterPositiveFinalExternalNaturalSegmentSystemTower
      k Γ hsmall hunit hno o}
    (h :
      ∀ p : Set.Iic o, T.system p = U.system p) :
    T = U := by
  cases T with
  | mk Tsystem Tcoherent =>
      cases U with
      | mk Usystem Ucoherent =>
          simp only at h
          have hsystem : Tsystem = Usystem := funext h
          cases hsystem
          rfl

/-- Final external natural-limit system towers at the same ordinal are unique. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (T U : KOneClusterPositiveFinalExternalNaturalSegmentSystemTower
      k Γ hsmall hunit hno o) :
    T = U :=
  KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.ext_system
    (k := k) (Γ := Γ) (fun p =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.eq (k := k) (Γ := Γ)
        (T.system p) (U.system p))

/-- The zero tower of final external natural-limit segment systems. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F} :
    KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno 0 where
  system := fun p =>
    have hp_eq : p.1 = (0 : Ordinal) := le_antisymm p.2 bot_le
    hp_eq.symm ▸
      KOneClusterPositiveFinalExternalNaturalSegmentSystem.zero
        (k := k) (Γ := Γ)
  coherent := by
    intro p q hp hq
    have hp_eq : p = (0 : Ordinal) := le_antisymm hp bot_le
    subst p
    have hq_eq : q = (0 : Ordinal) := le_antisymm hq bot_le
    subst q
    rfl

/-- Successor extension of a coherent tower of final external natural-limit segment systems. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (T : KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno o) :
    KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno
      (Order.succ o) := by
  let topSystem :=
    (T.system ⟨o, (show o ≤ o from le_rfl)⟩).succ (k := k) (Γ := Γ)
  let systemSucc :
      ∀ p : Set.Iic (Order.succ o),
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1 := fun p =>
    if hp : p.1 ≤ o then
      T.system ⟨p.1, hp⟩
    else
      have hp_eq : p.1 = Order.succ o :=
        (ordinal_le_succ_eq_or_le p.2).resolve_right hp
      hp_eq.symm ▸ topSystem
  have system_lower :
      ∀ {p : Ordinal} (hp_succ : p ≤ Order.succ o) (hp_low : p ≤ o),
        systemSucc ⟨p, hp_succ⟩ = T.system ⟨p, hp_low⟩ := by
    intro p hp_succ hp_low
    simp [systemSucc, hp_low]
  have system_top :
      ∀ (hp_succ : Order.succ o ≤ Order.succ o),
        systemSucc ⟨Order.succ o, hp_succ⟩ = topSystem := by
    intro hp_succ
    simp [systemSucc]
  refine
    { system := systemSucc
      coherent := ?_ }
  intro p q hp hq
  by_cases hp_low : p ≤ o
  · have hq_low : q ≤ o := le_trans hq hp_low
    rw [system_lower hp hp_low, system_lower (le_trans hq hp) hq_low]
    exact T.coherent hp_low hq
  · have hp_top : p = Order.succ o :=
      (ordinal_le_succ_eq_or_le hp).resolve_right hp_low
    subst p
    by_cases hq_low : q ≤ o
    · rw [system_top hp, system_lower (le_trans hq hp) hq_low]
      calc
        (topSystem.segment ⟨q, hq⟩) =
            ((T.system ⟨o, (show o ≤ o from le_rfl)⟩).segment ⟨q, hq_low⟩) := by
          exact
            KOneClusterPositiveFinalExternalNaturalSegmentSystem.succ_segment_lower
              (k := k) (Γ := Γ)
              (T.system ⟨o, (show o ≤ o from le_rfl)⟩) hq_low
        _ = ((T.system ⟨q, le_trans hq_low (show o ≤ o from le_rfl)⟩).segment
              ⟨q, (show q ≤ q from le_rfl)⟩) := by
          exact T.coherent (show o ≤ o from le_rfl) hq_low
    · have hq_top : q = Order.succ o :=
        (ordinal_le_succ_eq_or_le (le_trans hq hp)).resolve_right hq_low
      subst q
      rw [system_top hp]

@[simp] theorem KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.succ_system_lower
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o p : Ordinal.{v}}
    (T : KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno o)
    (hp : p ≤ o) :
    (T.succ (k := k) (Γ := Γ)).system
        ⟨p, le_trans hp (le_of_lt (Order.lt_succ o))⟩ =
      T.system ⟨p, hp⟩ := by
  unfold KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.succ
  simp [hp]

/-- Limit extension of a coherent tower of final external natural-limit segment systems.

The only non-local input is the coherence of the lower towers.  It is exactly what is needed to
turn the lower tower tops into the lower-system coherence required by `limitClosed`. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Tbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno p.1)
    (hTbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Tbelow ⟨p, hp⟩).system ⟨q, hq⟩ =
          (Tbelow ⟨q, lt_of_le_of_lt hq hp⟩).system
            ⟨q, (show q ≤ q from le_rfl)⟩) :
    KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno o := by
  classical
  let Sbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1 :=
    fun p => (Tbelow p).system ⟨p.1, (show p.1 ≤ p.1 from le_rfl)⟩
  have hSbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Sbelow ⟨p, hp⟩).segment ⟨q, hq⟩ =
          (Sbelow ⟨q, lt_of_le_of_lt hq hp⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩ := by
    intro p q hp hq
    calc
      (((Tbelow ⟨p, hp⟩).system ⟨p, (show p ≤ p from le_rfl)⟩).segment
            ⟨q, hq⟩) =
          (((Tbelow ⟨p, hp⟩).system ⟨q, hq⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        exact (Tbelow ⟨p, hp⟩).coherent (show p ≤ p from le_rfl) hq
      _ =
          (((Tbelow ⟨q, lt_of_le_of_lt hq hp⟩).system
              ⟨q, (show q ≤ q from le_rfl)⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        rw [hTbelow hp hq]
  let topSystem :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystem.limitClosed
      (k := k) (Γ := Γ) ho Sbelow hSbelow
  let systemLimit :
      ∀ p : Set.Iic o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno p.1 := fun p =>
    if hp : p.1 < o then
      (Tbelow ⟨p.1, hp⟩).system ⟨p.1, (show p.1 ≤ p.1 from le_rfl)⟩
    else
      have hp_eq : p.1 = o := le_antisymm p.2 (le_of_not_gt hp)
      hp_eq.symm ▸ topSystem
  have system_lower :
      ∀ {p : Ordinal} (hp_le : p ≤ o) (hp_lt : p < o),
        systemLimit ⟨p, hp_le⟩ =
          (Tbelow ⟨p, hp_lt⟩).system ⟨p, (show p ≤ p from le_rfl)⟩ := by
    intro p hp_le hp_lt
    simp [systemLimit, hp_lt]
  have system_top :
      ∀ (hp : o ≤ o), systemLimit ⟨o, hp⟩ = topSystem := by
    intro hp
    simp [systemLimit]
  refine
    { system := systemLimit
      coherent := ?_ }
  intro p q hp hq
  by_cases hp_lt : p < o
  · have hq_lt : q < o := lt_of_le_of_lt hq hp_lt
    rw [system_lower hp hp_lt, system_lower (le_trans hq hp) hq_lt]
    calc
      (((Tbelow ⟨p, hp_lt⟩).system ⟨p, (show p ≤ p from le_rfl)⟩).segment
            ⟨q, hq⟩) =
          (((Tbelow ⟨p, hp_lt⟩).system ⟨q, hq⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        exact (Tbelow ⟨p, hp_lt⟩).coherent (show p ≤ p from le_rfl) hq
      _ =
          (((Tbelow ⟨q, hq_lt⟩).system ⟨q, (show q ≤ q from le_rfl)⟩).segment
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        rw [hTbelow hp_lt hq]
  · have hp_eq : p = o := le_antisymm hp (le_of_not_gt hp_lt)
    subst p
    by_cases hq_lt : q < o
    · rw [system_top hp, system_lower (le_trans hq hp) hq_lt]
      exact
        KOneClusterPositiveFinalExternalNaturalSegmentSystem.limitClosed_segment_lower
          (k := k) (Γ := Γ) ho Sbelow hSbelow hq_lt
    · have hq_eq : q = o := le_antisymm hq (le_of_not_gt hq_lt)
      subst q
      rw [system_top hp]

@[simp] theorem KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.limit_system_lower
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o p : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Tbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno p.1)
    (hTbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Tbelow ⟨p, hp⟩).system ⟨q, hq⟩ =
          (Tbelow ⟨q, lt_of_le_of_lt hq hp⟩).system
            ⟨q, (show q ≤ q from le_rfl)⟩)
    (hp : p < o) :
    (KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.limit
      (k := k) (Γ := Γ) ho Tbelow hTbelow).system
        ⟨p, le_of_lt hp⟩ =
      (Tbelow ⟨p, hp⟩).system ⟨p, (show p ≤ p from le_rfl)⟩ := by
  unfold KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.limit
  simp [hp]

/-- A coherent stack of final external natural-limit segment-system towers up to `o`.

The extra layer is needed for the limit branch of the final recursion: lower towers produced at
different indices must agree on their common lower systems before they can be fed to
`limitClosed`. -/
structure KOneClusterPositiveFinalExternalNaturalSegmentSystemStack
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F)
    (o : Ordinal.{v}) where
  tower :
    ∀ p : Set.Iic o,
      KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno p.1
  coherent :
    ∀ {p q : Ordinal.{v}} (hp : p ≤ o) (hq : q ≤ p),
      (tower ⟨p, hp⟩).system ⟨q, hq⟩ =
        (tower ⟨q, le_trans hq hp⟩).system ⟨q, (show q ≤ q from le_rfl)⟩

/-- Extensionality for final external natural-limit stack systems.

The coherence field is proposition-valued, so pointwise equality of the stored towers determines
the stack. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.ext_tower
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    {A B : KOneClusterPositiveFinalExternalNaturalSegmentSystemStack
      k Γ hsmall hunit hno o}
    (h :
      ∀ p : Set.Iic o, A.tower p = B.tower p) :
    A = B := by
  cases A with
  | mk Atower Acoherent =>
      cases B with
      | mk Btower Bcoherent =>
          simp only at h
          have htower : Atower = Btower := funext h
          cases htower
          rfl

/-- Final external natural-limit stack systems at the same ordinal are unique. -/
theorem KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (A B : KOneClusterPositiveFinalExternalNaturalSegmentSystemStack
      k Γ hsmall hunit hno o) :
    A = B :=
  KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.ext_tower
    (k := k) (Γ := Γ) (fun p =>
      KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.eq (k := k) (Γ := Γ)
        (A.tower p) (B.tower p))

/-- The zero stack of final external natural-limit segment-system towers. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F} :
    KOneClusterPositiveFinalExternalNaturalSegmentSystemStack k Γ hsmall hunit hno 0 where
  tower := fun p =>
    have hp_eq : p.1 = (0 : Ordinal) := le_antisymm p.2 bot_le
    hp_eq.symm ▸
      KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.zero
        (k := k) (Γ := Γ)
  coherent := by
    intro p q hp hq
    have hp_eq : p = (0 : Ordinal) := le_antisymm hp bot_le
    subst p
    have hq_eq : q = (0 : Ordinal) := le_antisymm hq bot_le
    subst q
    rfl

/-- Successor extension of a coherent stack of final external natural-limit system towers. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}}
    (A : KOneClusterPositiveFinalExternalNaturalSegmentSystemStack k Γ hsmall hunit hno o) :
    KOneClusterPositiveFinalExternalNaturalSegmentSystemStack k Γ hsmall hunit hno
      (Order.succ o) := by
  let topTower :=
    (A.tower ⟨o, (show o ≤ o from le_rfl)⟩).succ (k := k) (Γ := Γ)
  let towerSucc :
      ∀ p : Set.Iic (Order.succ o),
        KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno p.1 :=
    fun p =>
      if hp : p.1 ≤ o then
        A.tower ⟨p.1, hp⟩
      else
        have hp_eq : p.1 = Order.succ o :=
          (ordinal_le_succ_eq_or_le p.2).resolve_right hp
        hp_eq.symm ▸ topTower
  have tower_lower :
      ∀ {p : Ordinal} (hp_succ : p ≤ Order.succ o) (hp_low : p ≤ o),
        towerSucc ⟨p, hp_succ⟩ = A.tower ⟨p, hp_low⟩ := by
    intro p hp_succ hp_low
    simp [towerSucc, hp_low]
  have tower_top :
      ∀ (hp_succ : Order.succ o ≤ Order.succ o),
        towerSucc ⟨Order.succ o, hp_succ⟩ = topTower := by
    intro hp_succ
    simp [towerSucc]
  refine
    { tower := towerSucc
      coherent := ?_ }
  intro p q hp hq
  by_cases hp_low : p ≤ o
  · have hq_low : q ≤ o := le_trans hq hp_low
    rw [tower_lower hp hp_low, tower_lower (le_trans hq hp) hq_low]
    exact A.coherent hp_low hq
  · have hp_top : p = Order.succ o :=
      (ordinal_le_succ_eq_or_le hp).resolve_right hp_low
    subst p
    by_cases hq_low : q ≤ o
    · rw [tower_top hp, tower_lower (le_trans hq hp) hq_low]
      calc
        (topTower.system ⟨q, hq⟩) =
            ((A.tower ⟨o, (show o ≤ o from le_rfl)⟩).system ⟨q, hq_low⟩) := by
          exact
            KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.succ_system_lower
              (k := k) (Γ := Γ)
              (A.tower ⟨o, (show o ≤ o from le_rfl)⟩) hq_low
        _ = ((A.tower ⟨q, le_trans hq_low (show o ≤ o from le_rfl)⟩).system
              ⟨q, (show q ≤ q from le_rfl)⟩) := by
          exact A.coherent (show o ≤ o from le_rfl) hq_low
    · have hq_top : q = Order.succ o :=
        (ordinal_le_succ_eq_or_le (le_trans hq hp)).resolve_right hq_low
      subst q
      simp [towerSucc]

/-- Limit extension of a coherent stack of final external natural-limit system towers. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    {o : Ordinal.{v}} (ho : Order.IsSuccLimit o)
    (Abelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystemStack k Γ hsmall hunit hno p.1)
    (hAbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Abelow ⟨p, hp⟩).tower ⟨q, hq⟩ =
          (Abelow ⟨q, lt_of_le_of_lt hq hp⟩).tower
            ⟨q, (show q ≤ q from le_rfl)⟩) :
    KOneClusterPositiveFinalExternalNaturalSegmentSystemStack k Γ hsmall hunit hno o := by
  classical
  let Tbelow :
      ∀ p : Set.Iio o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno p.1 :=
    fun p => (Abelow p).tower ⟨p.1, (show p.1 ≤ p.1 from le_rfl)⟩
  have hTbelow :
      ∀ {p q : Ordinal} (hp : p < o) (hq : q ≤ p),
        (Tbelow ⟨p, hp⟩).system ⟨q, hq⟩ =
          (Tbelow ⟨q, lt_of_le_of_lt hq hp⟩).system
            ⟨q, (show q ≤ q from le_rfl)⟩ := by
    intro p q hp hq
    calc
      (((Abelow ⟨p, hp⟩).tower ⟨p, (show p ≤ p from le_rfl)⟩).system
            ⟨q, hq⟩) =
          (((Abelow ⟨p, hp⟩).tower ⟨q, hq⟩).system
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        exact (Abelow ⟨p, hp⟩).coherent (show p ≤ p from le_rfl) hq
      _ =
          (((Abelow ⟨q, lt_of_le_of_lt hq hp⟩).tower
              ⟨q, (show q ≤ q from le_rfl)⟩).system
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        rw [hAbelow hp hq]
  let topTower :=
    KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.limit
      (k := k) (Γ := Γ) ho Tbelow hTbelow
  let towerLimit :
      ∀ p : Set.Iic o,
        KOneClusterPositiveFinalExternalNaturalSegmentSystemTower k Γ hsmall hunit hno p.1 :=
    fun p =>
      if hp : p.1 < o then
        (Abelow ⟨p.1, hp⟩).tower ⟨p.1, (show p.1 ≤ p.1 from le_rfl)⟩
      else
        have hp_eq : p.1 = o := le_antisymm p.2 (le_of_not_gt hp)
        hp_eq.symm ▸ topTower
  have tower_lower :
      ∀ {p : Ordinal} (hp_le : p ≤ o) (hp_lt : p < o),
        towerLimit ⟨p, hp_le⟩ =
          (Abelow ⟨p, hp_lt⟩).tower ⟨p, (show p ≤ p from le_rfl)⟩ := by
    intro p hp_le hp_lt
    simp [towerLimit, hp_lt]
  have tower_top :
      ∀ (hp : o ≤ o), towerLimit ⟨o, hp⟩ = topTower := by
    intro hp
    simp [towerLimit]
  refine
    { tower := towerLimit
      coherent := ?_ }
  intro p q hp hq
  by_cases hp_lt : p < o
  · have hq_lt : q < o := lt_of_le_of_lt hq hp_lt
    rw [tower_lower hp hp_lt, tower_lower (le_trans hq hp) hq_lt]
    calc
      (((Abelow ⟨p, hp_lt⟩).tower ⟨p, (show p ≤ p from le_rfl)⟩).system
            ⟨q, hq⟩) =
          (((Abelow ⟨p, hp_lt⟩).tower ⟨q, hq⟩).system
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        exact (Abelow ⟨p, hp_lt⟩).coherent (show p ≤ p from le_rfl) hq
      _ =
          (((Abelow ⟨q, hq_lt⟩).tower ⟨q, (show q ≤ q from le_rfl)⟩).system
            ⟨q, (show q ≤ q from le_rfl)⟩) := by
        rw [hAbelow hp_lt hq]
  · have hp_eq : p = o := le_antisymm hp (le_of_not_gt hp_lt)
    subst p
    rcases lt_or_ge q o with hq_lt | hq_ge
    · rw [tower_top hp, tower_lower (le_trans hq hp) hq_lt]
      exact
        KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.limit_system_lower
          (k := k) (Γ := Γ) ho Tbelow hTbelow hq_lt
    · have hq_eq : q = o := le_antisymm hq hq_ge
      subst q
      rw [tower_top hp]

/-- Coherent global family of final external natural-limit stack systems.

This is the exact output expected from the final stack recursion: a stack at every ordinal plus
the lower-tower coherence needed by `SegmentFamily.ofStack`. -/
structure KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) where
  stack :
    ∀ o : Ordinal.{v},
      KOneClusterPositiveFinalExternalNaturalSegmentSystemStack k Γ hsmall hunit hno o
  coherent :
    ∀ {o p : Ordinal.{v}} (hp : p ≤ o),
      (stack o).tower ⟨p, hp⟩ =
        (stack p).tower ⟨p, (show p ≤ p from le_rfl)⟩

/-- The final global stack recursion.

The limit branch uses uniqueness of lower towers to supply the lower-tower coherence required by
`Stack.limit`; this is the actual ordinal recursion behind the final external natural-limit
construction. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.ordinalRec
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (o : Ordinal.{v}) :
    KOneClusterPositiveFinalExternalNaturalSegmentSystemStack k Γ hsmall hunit hno o := by
  induction o using Ordinal.limitRecOn with
  | zero =>
      exact KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.zero (k := k) (Γ := Γ)
  | add_one o A =>
      exact A.succ (k := k) (Γ := Γ)
  | limit o ho Abelow =>
      exact
        KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.limit
          (k := k) (Γ := Γ) ho (fun p => Abelow p.1 p.2)
          (by
            intro p q hp hq
            exact
              KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.eq
                (k := k) (Γ := Γ)
                ((Abelow p hp).tower ⟨q, hq⟩)
                ((Abelow q (lt_of_le_of_lt hq hp)).tower
                  ⟨q, (show q ≤ q from le_rfl)⟩))

/-- The global stack recursion packaged with the coherence expected by `SegmentFamily.ofStack`. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily.ofOrdinalRec
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F} :
    KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily k Γ hsmall hunit hno where
  stack := fun o =>
    KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.ordinalRec (k := k) (Γ := Γ) o
  coherent := by
    intro o p hp
    exact
      KOneClusterPositiveFinalExternalNaturalSegmentSystemTower.eq (k := k) (Γ := Γ)
        ((KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.ordinalRec
          (k := k) (Γ := Γ) o).tower ⟨p, hp⟩)
        ((KOneClusterPositiveFinalExternalNaturalSegmentSystemStack.ordinalRec
          (k := k) (Γ := Γ) p).tower ⟨p, (show p ≤ p from le_rfl)⟩)

/-- Coherent final external natural-limit initial segments.

This is the object a genuine final simultaneous recursion should construct.  Coherence says that
larger initial segments restrict to the already constructed smaller segment at the top point. -/
structure KOneClusterPositiveFinalExternalNaturalSegmentFamily
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hno : ¬ RootInMaximalIdeal k Γ F) where
  segment :
    ∀ o : Ordinal.{v},
      KOneClusterPositiveFinalExternalNaturalSegment k Γ hsmall hunit hno o
  coherent :
    ∀ {o p : Ordinal.{v}} (hp : p ≤ o),
      (segment o).R ⟨p, hp⟩ =
        (segment p).R ⟨p, (show p ≤ p from le_rfl)⟩

/-- A global family of coherent segment systems gives the final segment family by taking the top
segment at every ordinal. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentFamily.ofSystem
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (S :
      ∀ o : Ordinal.{v},
        KOneClusterPositiveFinalExternalNaturalSegmentSystem k Γ hsmall hunit hno o)
    (hS :
      ∀ {o p : Ordinal.{v}} (hp : p ≤ o),
        (S o).segment ⟨p, hp⟩ =
          (S p).segment ⟨p, (show p ≤ p from le_rfl)⟩) :
    KOneClusterPositiveFinalExternalNaturalSegmentFamily k Γ hsmall hunit hno where
  segment := fun o => (S o).segment ⟨o, (show o ≤ o from le_rfl)⟩
  coherent := by
    intro o p hp
    calc
      ((S o).segment ⟨o, (show o ≤ o from le_rfl)⟩).R ⟨p, hp⟩ =
          ((S o).segment ⟨p, hp⟩).R ⟨p, (show p ≤ p from le_rfl)⟩ := by
        exact (S o).coherent (show o ≤ o from le_rfl) hp
      _ = ((S p).segment ⟨p, (show p ≤ p from le_rfl)⟩).R
            ⟨p, (show p ≤ p from le_rfl)⟩ := by
        rw [hS hp]

/-- A global coherent stack family gives the final segment family by taking the top tower, then
the top system, then the top segment at every ordinal. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentFamily.ofStack
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (A :
      ∀ o : Ordinal.{v},
        KOneClusterPositiveFinalExternalNaturalSegmentSystemStack k Γ hsmall hunit hno o)
    (hA :
      ∀ {o p : Ordinal.{v}} (hp : p ≤ o),
        (A o).tower ⟨p, hp⟩ =
          (A p).tower ⟨p, (show p ≤ p from le_rfl)⟩) :
    KOneClusterPositiveFinalExternalNaturalSegmentFamily k Γ hsmall hunit hno :=
  KOneClusterPositiveFinalExternalNaturalSegmentFamily.ofSystem
    (k := k) (Γ := Γ)
    (fun o => ((A o).tower ⟨o, (show o ≤ o from le_rfl)⟩).system
      ⟨o, (show o ≤ o from le_rfl)⟩)
    (by
      intro o p hp
      calc
        (((A o).tower ⟨o, (show o ≤ o from le_rfl)⟩).system
              ⟨o, (show o ≤ o from le_rfl)⟩).segment ⟨p, hp⟩ =
            (((A o).tower ⟨o, (show o ≤ o from le_rfl)⟩).system
              ⟨p, hp⟩).segment ⟨p, (show p ≤ p from le_rfl)⟩ := by
          exact
            ((A o).tower ⟨o, (show o ≤ o from le_rfl)⟩).coherent
              (show o ≤ o from le_rfl) hp
        _ =
            (((A o).tower ⟨p, hp⟩).system
              ⟨p, (show p ≤ p from le_rfl)⟩).segment
              ⟨p, (show p ≤ p from le_rfl)⟩ := by
          rw [(A o).coherent (show o ≤ o from le_rfl) hp]
        _ =
            (((A p).tower ⟨p, (show p ≤ p from le_rfl)⟩).system
              ⟨p, (show p ≤ p from le_rfl)⟩).segment
              ⟨p, (show p ≤ p from le_rfl)⟩ := by
          rw [hA hp])

/-- A coherent global stack family gives the final segment family. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily.toSegmentFamily
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (A :
      KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily
        k Γ hsmall hunit hno) :
    KOneClusterPositiveFinalExternalNaturalSegmentFamily k Γ hsmall hunit hno :=
  KOneClusterPositiveFinalExternalNaturalSegmentFamily.ofStack
    (k := k) (Γ := Γ) A.stack A.coherent

/-- Coherent initial segments give the final external natural-limit recursion data.

This is the extraction step for the final simultaneous recursion: after the recursion has built
coherent initial segments, the global chain is the top point of each segment. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentFamily.toLimitStepData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (D : KOneClusterPositiveFinalExternalNaturalSegmentFamily k Γ hsmall hunit hno) :
    KOneClusterPositiveFinalExternalNaturalLimitStepData k Γ hsmall hunit hno := by
  classical
  let R : ∀ o : Ordinal, PositiveIioCoherentChainAt k Γ o F :=
    fun o => (D.segment o).R ⟨o, (show o ≤ o from le_rfl)⟩
  let hnat :
      ∀ {o : Ordinal} (ho : Order.IsSuccLimit o),
        let C : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
        C.NaturalComponents k Γ ho := by
    intro o ho
    let Cseg : PositiveIioCoherentChainAtBelow k Γ o F :=
      fun i => (D.segment o).R
        ⟨i.1, (by simpa [Set.mem_Iic] using le_of_lt i.2)⟩
    let Cext : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
    have hC : Cseg = Cext := by
      funext i
      exact D.coherent (o := o) (p := i.1) (le_of_lt i.2)
    change Cext.NaturalComponents k Γ ho
    rw [← hC]
    exact (D.segment o).hnat le_rfl ho
  refine
    { R := R
      hsucc := ?_
      hnat := hnat
      hlimit := ?_ }
  · intro o
    change (D.segment (Order.succ o)).R
        ⟨Order.succ o, (by simp [Set.mem_Iic])⟩ =
      PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
        ((D.segment o).R ⟨o, (show o ≤ o from le_rfl)⟩)
    calc
      (D.segment (Order.succ o)).R
          ⟨Order.succ o, (by simp [Set.mem_Iic])⟩ =
          PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            ((D.segment (Order.succ o)).R
              ⟨o, (by exact le_of_lt (Order.lt_succ o))⟩) := by
        exact (D.segment (Order.succ o)).hsucc
          le_rfl
      _ = PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno
            ((D.segment o).R ⟨o, (show o ≤ o from le_rfl)⟩) := by
        exact congrArg
          (PositiveIioCoherentChainAt.succOfNoRoot k Γ hsmall hunit hno)
          (D.coherent (o := Order.succ o) (p := o)
            (le_of_lt (Order.lt_succ o)))
  · intro o ho
    let Cseg : PositiveIioCoherentChainAtBelow k Γ o F :=
      fun i => (D.segment o).R
        ⟨i.1, (by simpa [Set.mem_Iic] using le_of_lt i.2)⟩
    let Cext : PositiveIioCoherentChainAtBelow k Γ o F := fun i => R i.1
    have hC : Cseg = Cext := by
      funext i
      exact D.coherent (o := o) (p := i.1) (le_of_lt i.2)
    have hnatSeg : Cseg.NaturalComponents k Γ ho :=
      (D.segment o).hnat le_rfl ho
    have hlimitSeg :
        (D.segment o).R ⟨o, (show o ≤ o from le_rfl)⟩ =
          Cseg.limitStepOfNaturalComponents k Γ ho hnatSeg := by
      exact (D.segment o).hlimit le_rfl ho
    change (D.segment o).R ⟨o, (show o ≤ o from le_rfl)⟩ =
      Cext.limitStepOfNaturalComponents k Γ ho (hnat ho)
    exact hlimitSeg.trans
      (PositiveIioCoherentChainAtBelow.limitStepOfNaturalComponents_congr
        (k := k) (Γ := Γ) ho hC hnatSeg (hnat ho))

/-- A coherent global stack family gives the final external natural-limit recursion data. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily.toLimitStepData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F}
    (A :
      KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily
        k Γ hsmall hunit hno) :
    KOneClusterPositiveFinalExternalNaturalLimitStepData k Γ hsmall hunit hno :=
  A.toSegmentFamily (k := k) (Γ := Γ) |>.toLimitStepData (k := k) (Γ := Γ)

/-- The final ordinal stack recursion gives the external natural-limit recursion data. -/
noncomputable def KOneClusterPositiveFinalExternalNaturalLimitStepData.ofOrdinalStackRec
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    {hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
    {hunit : IsUnit (F.coeff 1)}
    {hno : ¬ RootInMaximalIdeal k Γ F} :
    KOneClusterPositiveFinalExternalNaturalLimitStepData k Γ hsmall hunit hno :=
  KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily.toLimitStepData
    (k := k) (Γ := Γ)
    (KOneClusterPositiveFinalExternalNaturalSegmentSystemStackFamily.ofOrdinalRec
      (k := k) (Γ := Γ))

end HahnField

end

end HahnKaplanskyRealClosedness
