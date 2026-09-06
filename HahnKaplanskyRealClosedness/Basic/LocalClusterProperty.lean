/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Basic.Cluster

/-!
# Local-ring odd-cluster hypotheses with coefficient properties

This module contains the coefficient-ring part shared by the Hahn valuation-subring and
fixed-denominator Puiseux routes.  The ambient field or support predicate is deliberately kept
out of this package: a route supplies it through `P` when it needs one.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Odd-cluster conditions in a local coefficient ring.  This four-field form is kept separate
from the coefficient-property package so specializations without an extra invariant retain their
original tuple shape. -/
def LocalOddClusterHypotheses
    (F : Polynomial R) (m : ℕ) : Prop :=
  0 < m ∧ Odd m ∧
    (∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal R) ∧
      IsUnit (F.coeff m)

theorem LocalOddClusterHypotheses.pos
    {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypotheses F m) :
    0 < m :=
  h.1

theorem LocalOddClusterHypotheses.odd
    {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypotheses F m) :
    Odd m :=
  h.2.1

theorem LocalOddClusterHypotheses.small
    {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypotheses F m) :
    ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal R :=
  h.2.2.1

theorem LocalOddClusterHypotheses.unit
    {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypotheses F m) :
    IsUnit (F.coeff m) :=
  h.2.2.2

/-- Odd-cluster conditions in a local coefficient ring, together with a property of every
coefficient. -/
def LocalOddClusterHypothesesWithCoeffProperty
    (P : R → Prop) (F : Polynomial R) (m : ℕ) : Prop :=
  0 < m ∧ Odd m ∧
    (∀ i, P (F.coeff i)) ∧
      (∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal R) ∧
        IsUnit (F.coeff m)

theorem LocalOddClusterHypothesesWithCoeffProperty.pos
    {P : R → Prop} {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypothesesWithCoeffProperty P F m) :
    0 < m :=
  h.1

theorem LocalOddClusterHypothesesWithCoeffProperty.odd
    {P : R → Prop} {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypothesesWithCoeffProperty P F m) :
    Odd m :=
  h.2.1

theorem LocalOddClusterHypothesesWithCoeffProperty.coeff
    {P : R → Prop} {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypothesesWithCoeffProperty P F m) :
    ∀ i, P (F.coeff i) :=
  h.2.2.1

theorem LocalOddClusterHypothesesWithCoeffProperty.coeff_at
    {P : R → Prop} {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypothesesWithCoeffProperty P F m) (i : ℕ) :
    P (F.coeff i) :=
  h.coeff i

theorem LocalOddClusterHypothesesWithCoeffProperty.small
    {P : R → Prop} {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypothesesWithCoeffProperty P F m) :
    ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal R :=
  h.2.2.2.1

theorem LocalOddClusterHypothesesWithCoeffProperty.unit
    {P : R → Prop} {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypothesesWithCoeffProperty P F m) :
    IsUnit (F.coeff m) :=
  h.2.2.2.2

/-- The `m = 1` specialization of a local-ring odd-cluster package. -/
def LocalOneClusterHypothesesWithCoeffProperty
    (P : R → Prop) (F : Polynomial R) : Prop :=
  (∀ i, P (F.coeff i)) ∧
    (∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal R) ∧
      IsUnit (F.coeff 1)

theorem LocalOddClusterHypothesesWithCoeffProperty.oneClusterHypotheses
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOddClusterHypothesesWithCoeffProperty P F 1) :
    LocalOneClusterHypothesesWithCoeffProperty P F :=
  ⟨h.coeff, h.small, h.unit⟩

theorem LocalOneClusterHypothesesWithCoeffProperty.coeff
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) :
    ∀ i, P (F.coeff i) :=
  h.1

theorem LocalOneClusterHypothesesWithCoeffProperty.coeff_at
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) (i : ℕ) :
    P (F.coeff i) :=
  h.coeff i

theorem LocalOneClusterHypothesesWithCoeffProperty.small
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) :
    ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal R :=
  h.2.1

theorem LocalOneClusterHypothesesWithCoeffProperty.unit
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) :
    IsUnit (F.coeff 1) :=
  h.2.2

theorem LocalOneClusterHypothesesWithCoeffProperty.oddClusterHypotheses
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) :
    LocalOddClusterHypothesesWithCoeffProperty P F 1 :=
  ⟨by norm_num, by norm_num, h.coeff, h.small, h.unit⟩

end

end HahnKaplanskyRealClosedness
