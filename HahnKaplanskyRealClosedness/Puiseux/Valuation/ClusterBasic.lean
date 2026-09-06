/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Valuation.RootPredicates
import HahnKaplanskyRealClosedness.Basic.ValuationClusterProperty

/-!
# Basic Puiseux valuation-cluster hypotheses

This file contains the valuation-subring cluster predicates and their projections. Bridges to
bounded-coefficient Hahn cluster statements live in `Puiseux.ValuationCluster`.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

/-- Valuation-subring form of the Puiseux-relevant odd-cluster root statement. -/
def BoundedValuationSubringOddClusterRootHypothesis
    [LinearOrder k] [IsStrictOrderedRing k] : Prop :=
  ∀ {F : Polynomial (HahnField.valuationSubring k ℚ)} {m : ℕ},
    0 < m → Odd m →
    (∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i : HahnField k ℚ)) →
    (∀ i, i < m →
      F.coeff i ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ)) →
    IsUnit (F.coeff m) →
    BoundedRootInMaximalIdeal k F

/-- Bundled side conditions for the valuation-subring odd-cluster root statement with bounded
Hahn supports. -/
abbrev BoundedValuationSubringOddClusterHypotheses
    [LinearOrder k] [IsStrictOrderedRing k]
    (F : Polynomial (HahnField.valuationSubring k ℚ)) (m : ℕ) : Prop :=
  HahnField.ValuationSubringOddClusterHypothesesWithCoeffProperty k ℚ
    (fun x => HasBoundedDenominatorSupport k x) F m

end

end Puiseux

end HahnKaplanskyRealClosedness
