/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Lift.FixedLevel

/-!
# Fixed-level Puiseux residue polynomials

This file contains residue-polynomial and residue-branch API for fixed-denominator valuation
levels.  Odd-cluster-specific facts live in `Puiseux.ValuationFixedLevelClusterBasic` and
`Puiseux.ValuationFixedLevelClusterRoutes`.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- Residue polynomial of a fixed-denominator valuation-level polynomial. -/
def fixedLevelResiduePolynomial (N : ℕ+)
    (F : Polynomial (fixedDenominatorValuationSubring k N)) : Polynomial k :=
  F.map (fixedDenominatorConstantCoeffRingHom k N)

@[simp]
theorem coeff_fixedLevelResiduePolynomial {N : ℕ+}
    (F : Polynomial (fixedDenominatorValuationSubring k N)) (i : ℕ) :
    (fixedLevelResiduePolynomial k N F).coeff i =
      fixedDenominatorConstantCoeffRingHom k N (F.coeff i) := by
  simp [fixedLevelResiduePolynomial, Polynomial.coeff_map]

@[simp]
theorem fixedLevelResiduePolynomial_comp_X_add_C {N : ℕ+}
    (F : Polynomial (fixedDenominatorValuationSubring k N))
    (y : fixedDenominatorValuationSubring k N) :
    fixedLevelResiduePolynomial k N (F.comp (Polynomial.X + Polynomial.C y)) =
      (fixedLevelResiduePolynomial k N F).comp
        (Polynomial.X + Polynomial.C (fixedDenominatorConstantCoeffRingHom k N y)) := by
  simp [fixedLevelResiduePolynomial, Polynomial.map_comp]

/-- A residue branch is recorded by a root and its root multiplicity. -/
def FixedLevelResidueBranchMultiplicity (N : ℕ+)
    (F : Polynomial (fixedDenominatorValuationSubring k N)) (_m : ℕ)
    (a : k) (r : ℕ) : Prop :=
  (fixedLevelResiduePolynomial k N F).rootMultiplicity a = r

theorem FixedLevelResidueBranchMultiplicity.exists_lift {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ} {a : k} {r : ℕ}
    (_h : FixedLevelResidueBranchMultiplicity k N F m a r) :
    ∃ y : fixedDenominatorValuationSubring k N,
      fixedDenominatorConstantCoeffRingHom k N y = a :=
  fixedDenominatorConstantCoeffRingHom_surjective k N a

theorem FixedLevelResidueBranchMultiplicity.translate_lift {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ} {a : k} {r : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (h : FixedLevelResidueBranchMultiplicity k N F m a r)
    (hy : fixedDenominatorConstantCoeffRingHom k N y = a) :
    FixedLevelResidueBranchMultiplicity k N
      (F.comp (Polynomial.X + Polynomial.C y)) m 0 r := by
  change (fixedLevelResiduePolynomial k N
      (F.comp (Polynomial.X + Polynomial.C y))).rootMultiplicity 0 = r
  rw [fixedLevelResiduePolynomial_comp_X_add_C]
  rw [← Polynomial.rootMultiplicity_eq_rootMultiplicity]
  simpa [hy, FixedLevelResidueBranchMultiplicity] using h

theorem FixedLevelResidueBranchMultiplicity.exists_translated_zero_branch {N : ℕ+}
    {F : Polynomial (fixedDenominatorValuationSubring k N)} {m : ℕ} {a : k} {r : ℕ}
    (h : FixedLevelResidueBranchMultiplicity k N F m a r) :
    ∃ y : fixedDenominatorValuationSubring k N,
      fixedDenominatorConstantCoeffRingHom k N y = a ∧
        FixedLevelResidueBranchMultiplicity k N
          (F.comp (Polynomial.X + Polynomial.C y)) m 0 r := by
  rcases h.exists_lift (k := k) with ⟨y, hy⟩
  exact ⟨y, hy, h.translate_lift (k := k) hy⟩

end

end Puiseux

end HahnKaplanskyRealClosedness
