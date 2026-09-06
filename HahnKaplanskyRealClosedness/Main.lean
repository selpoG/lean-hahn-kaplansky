/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Basic.ClusterProperty
import HahnKaplanskyRealClosedness.Basic.ValuationClusterProperty
import HahnKaplanskyRealClosedness.OmegaTail.Endpoints
import HahnKaplanskyRealClosedness.SimpleCluster.Fixed.OrdinalPrefix

/-!
# The completed Hahn--Kaplansky endpoint

The ordinal-stack construction supplies the multiplicity-one root, and the
resolver-free fixed-lift consumer closes every larger odd multiplicity.  This
file exposes the canonical public theorem through that proof spine.
-/

namespace HahnKaplanskyRealClosedness

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k] [IsRealClosed k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [DivisibleBy Γ ℕ]

theorem hahnKaplansky_realClosed_of_KClusterHypothesis
    (hCluster : HahnField.KOddClusterRootHypothesis k Γ) :
    IsRealClosed (HahnField k Γ) := by
  rcases subsingleton_or_nontrivial Γ with hsub | hnon
  · let _ : Subsingleton Γ := hsub
    exact HahnField.isRealClosed_of_subsingleton_valueGroup k Γ
  · let _ : Nontrivial Γ := hnon
    exact HahnField.isRealClosed_of_KOddCluster_nontrivial k Γ hCluster

/-- The completed ordinal-stack construction solves the multiplicity-one normalized problem. -/
theorem kOddClusterRootAt_one_of_ordinalStackRec :
    HahnField.KOddClusterRootAt k Γ 1 :=
  HahnField.kOddClusterRootAt_one_of_positiveGeneratedBlockProjectionCore
    k Γ (HahnField.kGeneratedBlockProjectionCore_of_ordinalStackRec (k := k) (Γ := Γ))

/-- A higher odd-multiplicity zero branch is resolved by the terminal ordinal construction,
assuming all proper odd multiplicities have already been solved. -/
theorem positiveHahnRoot_of_sameMultiplicityZeroBranch
    (hstep : HahnField.KSameMultiplicityRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : HahnField.KOddClusterRootBelow k Γ m)
    (hbranch : HahnField.KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    HahnField.PositiveHahnRoot k Γ F := by
  by_cases hroot : HahnField.PositiveHahnRoot k Γ F
  · exact hroot
  · rcases HahnField.exists_sameTerminalObstruction_of_withRootBelow_no_positiveRoot
      k Γ hstep hbelow hroot hbranch with ⟨T⟩
    exact T.positiveHahnRoot_of_edgeStep_rootOrStep_terminalResolution
      k Γ hstep hbelow

private theorem currentCoreRootHypothesis_of_rootOrStep_fixedLift
    (hone : HahnField.KOddClusterRootAt k Γ 1) :
    HahnField.KOddClusterRootHypothesis k Γ := by
  let hstepBelow : HahnField.KSameMultiplicityRootOrStepWithRootBelow k Γ :=
    HahnField.kSameMultiplicityRootOrStepWithRootBelow_of_edgeStep_lowerEdge k Γ
      (HahnField.kSameMultiplicityEdgeStepHypothesis_of_newtonInitial k Γ)
      (HahnField.kSameMultiplicityLowerEdgeResolutionWithRootBelow_of_affineNewtonEdge k Γ)
  let hbelowAll : ∀ M : ℕ, HahnField.KOddClusterRootBelow k Γ M := by
    refine HahnField.kOddClusterRootBelow_all_of_inductionStep k Γ ?_
    intro M hbelow F hcluster
    by_cases hM : M = 1
    · subst M
      exact hone hcluster
    · have hMpos : 0 < M := hcluster.pos k Γ
      have hMgt : 1 < M := by omega
      have hbranch : HahnField.KTranslatedSameMultiplicityZeroBranch k Γ F M :=
        ⟨hMgt, hcluster.translatedZeroBranch⟩
      exact positiveHahnRoot_of_sameMultiplicityZeroBranch
        k Γ hstepBelow hbelow hbranch
  let hsame : HahnField.KSameMultiplicityOmegaContinuationHypothesis k Γ := by
    intro F m hbranch
    exact positiveHahnRoot_of_sameMultiplicityZeroBranch
      k Γ hstepBelow (hbelowAll m) hbranch
  apply HahnField.kOddClusterRootHypothesis_of_at_one_or_sameMultiplicityOmega k Γ
  · exact hone
  · exact hsame

theorem hahnKaplansky_KOddClusterRootHypothesis_of_ordinalStackRec_aboveOne
    : HahnField.KOddClusterRootHypothesis k Γ :=
  currentCoreRootHypothesis_of_rootOrStep_fixedLift k Γ
    (kOddClusterRootAt_one_of_ordinalStackRec k Γ)

/-- Every odd-degree polynomial over the Hahn field has a root. -/
theorem hahnKaplansky_exists_root_of_odd_natDegree
    {F : Polynomial (HahnField k Γ)} (hodd : Odd F.natDegree) :
    ∃ x : HahnField k Γ, F.IsRoot x := by
  rcases subsingleton_or_nontrivial Γ with hsub | hnon
  · let _ : Subsingleton Γ := hsub
    have : IsRealClosed (HahnField k Γ) :=
      HahnField.isRealClosed_of_subsingleton_valueGroup k Γ
    exact IsRealClosed.exists_isRoot_of_odd_natDegree hodd
  · let _ : Nontrivial Γ := hnon
    exact HahnField.exists_root_of_KOddCluster_of_odd_natDegree_nontrivial
      k Γ (hahnKaplansky_KOddClusterRootHypothesis_of_ordinalStackRec_aboveOne k Γ) hodd

theorem hahnKaplansky_realClosed_of_ordinalStackRec_aboveOne
    : IsRealClosed (HahnField k Γ) :=
  by
    apply IsRealClosed.of_linearOrderedField
    · intro x hx
      exact HahnField.isSquare_of_nonneg k Γ hx
    · intro F hodd
      exact hahnKaplansky_exists_root_of_odd_natDegree k Γ hodd

/-- Canonical public Hahn--Kaplansky theorem for a real closed coefficient field
and a divisible ordered value group. -/
theorem hahnKaplansky_realClosed_of_realClosed_divisible
    : IsRealClosed (HahnField k Γ) :=
  hahnKaplansky_realClosed_of_ordinalStackRec_aboveOne k Γ

end HahnKaplanskyRealClosedness
