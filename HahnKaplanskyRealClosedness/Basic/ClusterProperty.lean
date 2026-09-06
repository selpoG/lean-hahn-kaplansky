/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Basic.Cluster

/-!
# Odd-cluster hypotheses with coefficient properties

This module packages the common coefficient-condition shape used by subfield routes.  A route can
specialize `P` to a support, integrality, or other coefficient property without rebuilding the
odd-cluster projections in the specialized namespace.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Odd-cluster conditions together with a property of every polynomial coefficient. -/
def KOddClusterHypothesesWithCoeffProperty
    (P : HahnField k Γ → Prop)
    (F : Polynomial (HahnField k Γ)) (m : ℕ) : Prop :=
  0 < m ∧ Odd m ∧
    (∀ i, P (F.coeff i)) ∧
      (∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i)) ∧
        (∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i)) ∧
          addVal k Γ (F.coeff m) = 0

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypothesesWithCoeffProperty.pos
    {P : HahnField k Γ → Prop}
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    0 < m :=
  h.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypothesesWithCoeffProperty.odd
    {P : HahnField k Γ → Prop}
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    Odd m :=
  h.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypothesesWithCoeffProperty.coeff
    {P : HahnField k Γ → Prop}
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    ∀ i, P (F.coeff i) :=
  h.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypothesesWithCoeffProperty.coeff_at
    {P : HahnField k Γ → Prop}
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypothesesWithCoeffProperty k Γ P F m) (i : ℕ) :
    P (F.coeff i) :=
  KOddClusterHypothesesWithCoeffProperty.coeff (k := k) (Γ := Γ) h i

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypothesesWithCoeffProperty.nonneg
    {P : HahnField k Γ → Prop}
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i) :=
  h.2.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypothesesWithCoeffProperty.lower
    {P : HahnField k Γ → Prop}
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    ∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i) :=
  h.2.2.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypothesesWithCoeffProperty.main
    {P : HahnField k Γ → Prop}
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    addVal k Γ (F.coeff m) = 0 :=
  h.2.2.2.2.2

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypothesesWithCoeffProperty.cluster
    {P : HahnField k Γ → Prop}
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    KOddClusterHypotheses k Γ F m :=
  ⟨h.pos, h.odd, h.nonneg, h.lower, h.main⟩

end HahnField

end

end HahnKaplanskyRealClosedness
