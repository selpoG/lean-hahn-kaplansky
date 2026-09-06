/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.OmegaTail.CoreRoutes.Final

/-!
# Canonical endpoints for the positive generated route

This module contains only the `m = 1` endpoint consumed by the Hahn proof.  Historical
omega-chain terminal resolvers are intentionally kept out of the canonical import graph.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The Hartogs endpoint only needs one generated limit-step function under the no-root
assumption; later route data supplies exactly this boundary. -/
theorem rootInMaximalIdeal_of_positiveLimitStepExists
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (limitStepExists :
      (¬ RootInMaximalIdeal k Γ F) →
        Nonempty
          (∀ {o : Ordinal.{u_2}}, Order.IsSuccLimit o →
            PositiveIioCoherentChainAtBelow k Γ o F →
            PositiveIioCoherentChainAt k Γ o F)) :
    RootInMaximalIdeal k Γ F := by
  by_contra hno
  rcases limitStepExists hno with ⟨limitStep⟩
  let C : PositiveIioCoherentChainAt k Γ (hartogsOrdinal Γ) F :=
    PositiveIioCoherentChainAt.recOfNoRoot k Γ hsmall hunit hno limitStep
      (hartogsOrdinal Γ)
  exact PositiveIioCoherentChainAt.not_hartogs k Γ ⟨C⟩

theorem rootInMaximalIdeal_of_oneClusterPositiveGeneratedLimitStepCompat
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hlimit : KOneClusterPositiveGeneratedLimitStepCompatHypothesis k Γ)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) :
    RootInMaximalIdeal k Γ F :=
  rootInMaximalIdeal_of_positiveLimitStepExists k Γ hsmall hunit
    (fun hno =>
      kOneClusterPositiveGeneratedLimitStepHypothesis_of_generatedLimitStepCompat
        k Γ hlimit hsmall hunit hno)

theorem rootInMaximalIdeal_of_oneClusterPositiveGeneratedBlockProjectionCore
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hlimit : KOneClusterPositiveGeneratedBlockProjectionCoreHypothesis k Γ)
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) :
    RootInMaximalIdeal k Γ F :=
  rootInMaximalIdeal_of_oneClusterPositiveGeneratedLimitStepCompat k Γ
    (kGeneratedLimitStepCompat_of_generatedBlockProjectionCore k Γ hlimit)
    hsmall hunit

theorem kOddClusterRootAt_one_of_positiveGeneratedBlockProjectionCore
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hlimit : KOneClusterPositiveGeneratedBlockProjectionCoreHypothesis k Γ) :
    KOddClusterRootAt k Γ 1 := by
  intro F hcluster
  rcases exists_lift_of_KOddClusterHypotheses k Γ hcluster with
    ⟨G, hG, hsmall, hunit⟩
  have hrootMax : RootInMaximalIdeal k Γ G :=
    rootInMaximalIdeal_of_oneClusterPositiveGeneratedBlockProjectionCore
      k Γ hlimit hsmall hunit
  have hpos := RootInMaximalIdeal.positiveHahnRootInMap k Γ hrootMax
  simpa [PositiveHahnRootInMap, hG] using hpos

end HahnField

end

end HahnKaplanskyRealClosedness
