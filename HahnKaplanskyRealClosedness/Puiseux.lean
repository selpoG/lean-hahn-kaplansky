/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Roots.SquareRoot
import HahnKaplanskyRealClosedness.Puiseux.Roots.Scaling
import HahnKaplanskyRealClosedness.Puiseux.Lift.Hensel
import HahnKaplanskyRealClosedness.Puiseux.Newton.LowerEdgeFixedLevel

/-!
# Puiseux real-closedness endpoint

This public entry point assembles the fixed-level odd-cluster root theorem with the valuation
criterion to obtain real closedness of the Puiseux series field.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

open scoped PowerSeries

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- Preferred public name for the Puiseux series type. -/
abbrev PuiseuxSeries := Puiseux.Series k

theorem puiseuxSeries_isSquare_of_nonneg
    [IsRealClosed k] {x : PuiseuxSeries k} (hx : 0 ≤ x) :
    IsSquare x :=
  Puiseux.isSquare_of_bounded_square_root_hypothesis k
    (Puiseux.boundedSquareRootHypothesis k) hx

/-- Every odd-degree polynomial over the Puiseux series field has a Puiseux root. -/
theorem puiseuxSeries_exists_root_of_odd_natDegree
    [IsRealClosed k] {F : Polynomial (PuiseuxSeries k)} (hodd : Odd F.natDegree) :
    ∃ x : PuiseuxSeries k, F.IsRoot x := by
  have hlift : Puiseux.LevelSimpleRootLiftHypothesis k := by
    have : ∀ n : ℕ+, IsAdicComplete
        (IsLocalRing.maximalIdeal (Puiseux.fixedDenominatorValuationSubring k n))
        (Puiseux.fixedDenominatorValuationSubring k n) :=
      Puiseux.fixedDenominatorValuationSubring_isAdicComplete k
    exact Puiseux.levelSimpleRootLiftHypothesis_of_isAdicComplete k
  have hboundedCoeff : Puiseux.BoundedCoeffKOddClusterRootHypothesis k :=
    Puiseux.boundedCoeffKOddClusterRootHypothesis_of_levelSimpleRootLift_or_same (k := k)
      hlift
  exact Puiseux.exists_root_of_scaledBoundedHahnRootWitness (k := k)
    ((Puiseux.exists_positive_hahn_root_of_boundedCoeff_KOddCluster_of_odd_natDegree
      (k := k) hboundedCoeff hodd).scaledBoundedHahnRootWitness (k := k))

theorem puiseuxSeries_isRealClosed
    [IsRealClosed k] :
    IsRealClosed (PuiseuxSeries k) := by
  apply IsRealClosed.of_linearOrderedField
  · intro x hx
    exact puiseuxSeries_isSquare_of_nonneg k hx
  · intro F hodd
    exact puiseuxSeries_exists_root_of_odd_natDegree k hodd

end

end HahnKaplanskyRealClosedness
