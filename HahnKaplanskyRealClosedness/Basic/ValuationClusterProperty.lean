/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Basic.ClusterProperty
import HahnKaplanskyRealClosedness.Basic.LocalClusterProperty

/-!
# Valuation-subring cluster hypotheses with coefficient properties

This module contains the common packaging for valuation-subring cluster routes.  The coefficient
property is abstract so subfields can reuse the same odd, one-cluster, and monic projections.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Valuation-subring odd-cluster conditions with a property of every Hahn-field coefficient.

This is only the valuation-subring specialization of the local-ring package; keeping the name
preserves the existing Hahn-field API for downstream routes.
-/
abbrev ValuationSubringOddClusterHypothesesWithCoeffProperty
    (P : HahnField k Γ → Prop)
    (F : Polynomial (valuationSubring k Γ)) (m : ℕ) : Prop :=
  LocalOddClusterHypothesesWithCoeffProperty
    (R := valuationSubring k Γ) (fun x => P (x : HahnField k Γ)) F m

theorem ValuationSubringOddClusterHypothesesWithCoeffProperty.pos
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ}
    (h : ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    0 < m :=
  LocalOddClusterHypothesesWithCoeffProperty.pos h

theorem ValuationSubringOddClusterHypothesesWithCoeffProperty.odd
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ}
    (h : ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    Odd m :=
  LocalOddClusterHypothesesWithCoeffProperty.odd h

theorem ValuationSubringOddClusterHypothesesWithCoeffProperty.coeff
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ}
    (h : ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    ∀ i, P (F.coeff i : HahnField k Γ) :=
  LocalOddClusterHypothesesWithCoeffProperty.coeff h

theorem ValuationSubringOddClusterHypothesesWithCoeffProperty.coeff_at
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ}
    (h : ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F m) (i : ℕ) :
    P (F.coeff i : HahnField k Γ) :=
  LocalOddClusterHypothesesWithCoeffProperty.coeff_at h i

theorem ValuationSubringOddClusterHypothesesWithCoeffProperty.small
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ}
    (h : ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  LocalOddClusterHypothesesWithCoeffProperty.small h

theorem ValuationSubringOddClusterHypothesesWithCoeffProperty.unit
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ}
    (h : ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F m) :
    IsUnit (F.coeff m) :=
  LocalOddClusterHypothesesWithCoeffProperty.unit h

/-- The `m = 1` specialization of a valuation-subring odd-cluster package. -/
abbrev ValuationSubringOneClusterHypothesesWithCoeffProperty
    (P : HahnField k Γ → Prop)
    (F : Polynomial (valuationSubring k Γ)) : Prop :=
  LocalOneClusterHypothesesWithCoeffProperty
    (R := valuationSubring k Γ) (fun x => P (x : HahnField k Γ)) F

theorem ValuationSubringOddClusterHypothesesWithCoeffProperty.oneClusterHypotheses
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)}
    (h : ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F 1) :
    ValuationSubringOneClusterHypothesesWithCoeffProperty k Γ P F :=
  LocalOddClusterHypothesesWithCoeffProperty.oneClusterHypotheses h

theorem ValuationSubringOneClusterHypothesesWithCoeffProperty.coeff
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)}
    (h : ValuationSubringOneClusterHypothesesWithCoeffProperty k Γ P F) :
    ∀ i, P (F.coeff i : HahnField k Γ) :=
  LocalOneClusterHypothesesWithCoeffProperty.coeff h

theorem ValuationSubringOneClusterHypothesesWithCoeffProperty.coeff_at
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)}
    (h : ValuationSubringOneClusterHypothesesWithCoeffProperty k Γ P F) (i : ℕ) :
    P (F.coeff i : HahnField k Γ) :=
  LocalOneClusterHypothesesWithCoeffProperty.coeff_at h i

theorem ValuationSubringOneClusterHypothesesWithCoeffProperty.small
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)}
    (h : ValuationSubringOneClusterHypothesesWithCoeffProperty k Γ P F) :
    ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  LocalOneClusterHypothesesWithCoeffProperty.small h

theorem ValuationSubringOneClusterHypothesesWithCoeffProperty.unit
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)}
    (h : ValuationSubringOneClusterHypothesesWithCoeffProperty k Γ P F) :
    IsUnit (F.coeff 1) :=
  LocalOneClusterHypothesesWithCoeffProperty.unit h

theorem ValuationSubringOneClusterHypothesesWithCoeffProperty.oddClusterHypotheses
    {P : HahnField k Γ → Prop}
    {F : Polynomial (valuationSubring k Γ)}
    (h : ValuationSubringOneClusterHypothesesWithCoeffProperty k Γ P F) :
    ValuationSubringOddClusterHypothesesWithCoeffProperty k Γ P F 1 :=
  LocalOneClusterHypothesesWithCoeffProperty.oddClusterHypotheses h

end HahnField

end

end HahnKaplanskyRealClosedness
