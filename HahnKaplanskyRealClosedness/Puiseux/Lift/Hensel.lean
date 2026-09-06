/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Lift.PowerSeries

/-!
# Hensel-lifting targets for Puiseux valuation levels

This file packages Hensel-lifting targets for the Puiseux valuation subring and its
fixed-denominator valuation levels.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

open scoped PowerSeries

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- Explicit Hensel-lifting target for the Puiseux valuation subring.

This is equivalent to `HenselianLocalRing (valuationSubring k)`, but is better suited as a
proof-facing contract because it avoids packaging the goal as a typeclass instance. -/
def HenselLiftHypothesis : Prop :=
  ∀ f : Polynomial (valuationSubring k), f.Monic →
    ∀ a₀ : IsLocalRing.ResidueField (valuationSubring k),
      Polynomial.aeval a₀ f = 0 →
        Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0 →
          ∃ a : valuationSubring k, f.IsRoot a ∧
            IsLocalRing.residue (valuationSubring k) a = a₀

/-- The same Hensel-lifting target, written through the explicit constant-coefficient residue map
to `k`. -/
def ConstantCoeffHenselLiftHypothesis : Prop :=
  ∀ f : Polynomial (valuationSubring k), f.Monic → ∀ a₀ : k,
    f.eval₂ (constantCoeffRingHom k) a₀ = 0 →
      f.derivative.eval₂ (constantCoeffRingHom k) a₀ ≠ 0 →
        ∃ a : valuationSubring k, f.IsRoot a ∧ constantCoeffRingHom k a = a₀

/-- Fixed-denominator form of the constant-coefficient Hensel-lifting target.

Every polynomial over the Puiseux valuation subring has its coefficients in one such level, so
this is the finite-level reduction needed before proving Hensel lifting by completeness of
`k((t^(1/n)))`. -/
def FixedLevelConstantCoeffHenselLiftHypothesis : Prop :=
  ∀ n : ℕ+, ∀ f : Polynomial (valuationSubring k),
    (∀ i : ℕ, (f.coeff i : Series k) ∈ fixedDenominatorValuationSubring k n) →
      f.Monic → ∀ a₀ : k,
        f.eval₂ (constantCoeffRingHom k) a₀ = 0 →
          f.derivative.eval₂ (constantCoeffRingHom k) a₀ ≠ 0 →
            ∃ a : valuationSubring k,
              (a : Series k) ∈ fixedDenominatorValuationSubring k n ∧
                f.IsRoot a ∧ constantCoeffRingHom k a = a₀

/-- Hensel-lifting target stated internally on each fixed-denominator valuation level. -/
def LevelConstantCoeffHenselLiftHypothesis : Prop :=
  ∀ n : ℕ+, ∀ f : Polynomial (fixedDenominatorValuationSubring k n), f.Monic →
    ∀ a₀ : k,
      f.eval₂ (fixedDenominatorConstantCoeffRingHom k n) a₀ = 0 →
        f.derivative.eval₂ (fixedDenominatorConstantCoeffRingHom k n) a₀ ≠ 0 →
          ∃ a : fixedDenominatorValuationSubring k n, f.IsRoot a ∧
            fixedDenominatorConstantCoeffRingHom k n a = a₀

/-- Fixed-denominator level-internal simple-root lift target without a monicity assumption. -/
def LevelSimpleRootLiftHypothesis : Prop :=
  ∀ n : ℕ+, ∀ f : Polynomial (fixedDenominatorValuationSubring k n), ∀ a₀ : k,
    f.eval₂ (fixedDenominatorConstantCoeffRingHom k n) a₀ = 0 →
      f.derivative.eval₂ (fixedDenominatorConstantCoeffRingHom k n) a₀ ≠ 0 →
        ∃ a : fixedDenominatorValuationSubring k n, f.IsRoot a ∧
          fixedDenominatorConstantCoeffRingHom k n a = a₀

theorem residueFieldEquiv_aeval
    (a₀ : IsLocalRing.ResidueField (valuationSubring k))
    (f : Polynomial (valuationSubring k)) :
    residueFieldEquiv k (Polynomial.aeval a₀ f) =
      f.eval₂ (constantCoeffRingHom k) (residueFieldEquiv k a₀) := by
  rw [Polynomial.aeval_def]
  have hcomp :
      (residueFieldEquiv k).toRingHom.comp
          (algebraMap (valuationSubring k)
            (IsLocalRing.ResidueField (valuationSubring k))) =
        constantCoeffRingHom k := by
    ext x
    change residueFieldEquiv k
        (algebraMap (valuationSubring k)
          (IsLocalRing.ResidueField (valuationSubring k)) x) =
      constantCoeffRingHom k x
    rw [IsLocalRing.ResidueField.algebraMap_eq, residueFieldEquiv_residue]
  simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hcomp] using
    (show
      (residueFieldEquiv k).toRingHom
          (Polynomial.eval₂
            (algebraMap (valuationSubring k) (IsLocalRing.ResidueField (valuationSubring k)))
            a₀ f) =
        f.eval₂ (constantCoeffRingHom k) ((residueFieldEquiv k).toRingHom a₀) from
      Polynomial.hom_eval₂ f
        (algebraMap (valuationSubring k) (IsLocalRing.ResidueField (valuationSubring k)))
        (residueFieldEquiv k).toRingHom a₀)

theorem levelConstantCoeffHenselLiftHypothesis_of_henselianLocalRing
    (h : ∀ n : ℕ+, HenselianLocalRing (fixedDenominatorValuationSubring k n)) :
    LevelConstantCoeffHenselLiftHypothesis k := by
  intro n f hf a₀ hroot hder
  have : HenselianLocalRing (fixedDenominatorValuationSubring k n) := h n
  have hlift :=
    ((HenselianLocalRing.TFAE (fixedDenominatorValuationSubring k n)).out 0 2).mp
      (show HenselianLocalRing (fixedDenominatorValuationSubring k n) from inferInstance)
  exact hlift (K := k) (fixedDenominatorConstantCoeffRingHom k n)
    (fixedDenominatorConstantCoeffRingHom_surjective k n) f hf a₀ hroot hder

theorem levelConstantCoeffHenselLiftHypothesis_of_isAdicComplete
    [∀ n : ℕ+, IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n)] :
    LevelConstantCoeffHenselLiftHypothesis k :=
  levelConstantCoeffHenselLiftHypothesis_of_henselianLocalRing k
    (fixedLevelHenselianLocalRing_of_isAdicComplete k)

theorem levelSimpleRootLiftHypothesis_of_isAdicComplete
    [∀ n : ℕ+, IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n)] :
    LevelSimpleRootLiftHypothesis k := by
  intro n f a₀ hroot hder
  have : IsAdicComplete
      (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
      (fixedDenominatorValuationSubring k n) := inferInstance
  rcases fixedDenominatorConstantCoeffRingHom_surjective k n a₀ with ⟨a₀R, ha₀R⟩
  have hroot_mem :
      f.eval a₀R ∈ IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n) := by
    rw [← fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) n,
      RingHom.mem_ker]
    calc
      fixedDenominatorConstantCoeffRingHom k n (f.eval a₀R)
          = f.eval₂ (fixedDenominatorConstantCoeffRingHom k n)
              (fixedDenominatorConstantCoeffRingHom k n a₀R) := by
              exact
                Polynomial.hom_eval₂ f (RingHom.id (fixedDenominatorValuationSubring k n))
                  (fixedDenominatorConstantCoeffRingHom k n) a₀R
      _ = 0 := by
              simpa [ha₀R] using hroot
  have hder_ne :
      fixedDenominatorConstantCoeffRingHom k n (f.derivative.eval a₀R) ≠ 0 := by
    intro hzero
    apply hder
    have hder_eval :
        fixedDenominatorConstantCoeffRingHom k n (f.derivative.eval a₀R) =
          f.derivative.eval₂ (fixedDenominatorConstantCoeffRingHom k n)
            (fixedDenominatorConstantCoeffRingHom k n a₀R) := by
      exact
        Polynomial.hom_eval₂ f.derivative
          (RingHom.id (fixedDenominatorValuationSubring k n))
          (fixedDenominatorConstantCoeffRingHom k n) a₀R
    rw [ha₀R, hzero] at hder_eval
    exact hder_eval.symm
  have hder_unit :
      IsUnit
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
          (f.derivative.eval a₀R)) :=
    (fixedDenominator_isUnit_of_constantCoeffRingHom_ne_zero k
      (f.derivative.eval a₀R) hder_ne).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n)))
  rcases exists_root_of_isAdicComplete_simpleRoot
      (fixedDenominatorValuationSubring k n)
      (IsLocalRing.maximalIdeal (fixedDenominatorValuationSubring k n))
      (f := f) (a₀ := a₀R) hroot_mem hder_unit with
    ⟨a, haroot, hasub⟩
  refine ⟨a, haroot, ?_⟩
  have hsub0 :
      fixedDenominatorConstantCoeffRingHom k n (a - a₀R) = 0 := by
    have hker :
        a - a₀R ∈ RingHom.ker (fixedDenominatorConstantCoeffRingHom k n) := by
      rw [fixedDenominatorConstantCoeffRingHom_ker_eq_maximalIdeal (k := k) n]
      exact hasub
    exact hker
  have hcc_eq :
      fixedDenominatorConstantCoeffRingHom k n a =
        fixedDenominatorConstantCoeffRingHom k n a₀R := by
    exact sub_eq_zero.mp (by simpa using hsub0)
  simpa [ha₀R] using hcc_eq

end

end Puiseux

end HahnKaplanskyRealClosedness
