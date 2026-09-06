/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Newton.PolynomialSupport
import HahnKaplanskyRealClosedness.SimpleCluster.Fixed.Foundation

/-!
# Bounded-support affine Newton lower edges

This module connects the Hahn affine-Newton lower-edge argument to the bounded-support root
predicate used by the Puiseux route.  The lower-multiplicity input remains explicit: this is the
induction slice consumed by the eventual Puiseux cluster theorem.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- Bounded-support roots for all odd clusters of multiplicity strictly below `M`. -/
def BoundedCoeffKOddClusterRootBelow (M : ℕ) : Prop :=
  ∀ {F : Polynomial (HahnField k ℚ)} {r : ℕ},
    r < M → BoundedCoeffKOddClusterHypotheses k F r →
      ∃ y : HahnField k ℚ,
        (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
          HasBoundedDenominatorSupport k y ∧ F.IsRoot y

theorem exists_bounded_root_of_lowerEdge_affine_newton_edge
    [IsRealClosed k]
    {G : Polynomial (HahnField k ℚ)} {n : ℕ} {δ : ℚ}
    (hmain : n ∈ G.support)
    (htop : HahnField.coeffValueOfMemSupport k ℚ G hmain = 0)
    (hm : Odd n)
    (hzero : HahnField.newtonWeight k ℚ G δ 0 =
      ((n • δ : ℚ) : WithTop ℚ))
    (hlower_pos : ∀ i, i < n → (hisupp : i ∈ G.support) →
      0 < HahnField.coeffValueOfMemSupport k ℚ G hisupp)
    (hbelow : ∃ j, j < n ∧ j ∈ G.support ∧
      HahnField.newtonWeight k ℚ G δ j < (n • δ : ℚ))
    (hnonneg : ∀ i, n < i → (hisupp : i ∈ G.support) →
      0 ≤ HahnField.coeffValueOfMemSupport k ℚ G hisupp)
    (hGbd : HasBoundedDenominatorSupportPolynomial k G)
    (hrootBelow : BoundedCoeffKOddClusterRootBelow k n) :
    ∃ y : HahnField k ℚ,
      (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
        HasBoundedDenominatorSupport k y ∧ G.IsRoot y := by
  rcases HahnField.exists_root_of_lowerEdge_affine_newton_edge_with_property
      (k := k) (Γ := ℚ) hmain htop hm hzero hlower_pos hbelow hnonneg
      (fun y => HasBoundedDenominatorSupport k y)
      (fun y a hy => hasBoundedDenominatorSupport_add k hy
        (hasBoundedDenominatorSupport_single k a (hasDenominator_zero 1)))
      (fun y γ hy => by
        rcases exists_hasDenominator γ with ⟨N, hγ⟩
        exact hasBoundedDenominatorSupport_mul k
          (hasBoundedDenominatorSupport_hahnMonomial k hγ) hy)
      (fun {θ μ} a i => by
        rcases exists_hasDenominator θ with ⟨Nθ, hθ⟩
        rcases exists_hasDenominator μ with ⟨Nμ, hμ⟩
        have hscale : HasBoundedDenominatorSupportPolynomial k
            (HahnField.scalePolynomial k ℚ G θ μ) :=
          hasBoundedDenominatorSupportPolynomial_scale k hGbd hθ hμ
        exact (hasBoundedDenominatorSupportPolynomial_comp_X_add_C k hscale
          (hasBoundedDenominatorSupport_single k a (hasDenominator_zero 1))) i)
      (fun hr hcluster => hrootBelow hr hcluster) with
    ⟨y, hypos, hybd, hyroot⟩
  exact ⟨y, hypos, hybd, hyroot⟩

theorem exists_bounded_root_of_nonlower_initial_root
    [IsRealClosed k]
    {G : Polynomial (HahnField k ℚ)} {M : ℕ} {δ : ℚ}
    (hδpos : 0 < δ)
    (hge : ∀ i, ((M • δ : ℚ) : WithTop ℚ) ≤
      HahnField.newtonWeight k ℚ G δ i)
    {a : k} {r : ℕ}
    (hrpos : 0 < r) (hrodd : Odd r) (hrlt : r < M)
    (hmul : (HahnField.newtonInitialPolynomial k ℚ G δ (M • δ)).rootMultiplicity a = r)
    (hGbd : HasBoundedDenominatorSupportPolynomial k G)
    (hrootBelow : BoundedCoeffKOddClusterRootBelow k M) :
    ∃ y : HahnField k ℚ,
      (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
        HasBoundedDenominatorSupport k y ∧ G.IsRoot y := by
  rcases exists_hasDenominator δ with ⟨nδ, hδ⟩
  rcases exists_hasDenominator (M • δ) with ⟨nμ, hμ⟩
  have hscaled := hasBoundedDenominatorSupportPolynomial_scale k hGbd hδ hμ
  have htranslated := hasBoundedDenominatorSupportPolynomial_comp_X_add_C k hscaled
    (hasBoundedDenominatorSupport_single k a (hasDenominator_zero 1))
  have hcluster : HahnField.KOddClusterHypotheses k ℚ
      ((HahnField.scalePolynomial k ℚ G δ (M • δ)).comp
        (Polynomial.X + Polynomial.C (toLex
          (HahnSeries.single 0 a)))) r :=
    HahnField.oddClusterHypotheses_scalePolynomial_comp_single_zero_of_rootMultiplicity
      k ℚ G hge hmul hrpos hrodd
  have hrootScaled : ∃ w : HahnField k ℚ,
      (0 : WithTop ℚ) < HahnField.addVal k ℚ w ∧
        HasBoundedDenominatorSupport k w ∧
          ((HahnField.scalePolynomial k ℚ G δ (M • δ)).comp
            (Polynomial.X + Polynomial.C (toLex
              (HahnSeries.single 0 a)))).IsRoot w := by
    apply hrootBelow hrlt
    refine ⟨hcluster.pos, hcluster.odd, ?_, hcluster.nonneg,
      hcluster.lower, hcluster.main⟩
    exact fun i => htranslated i
  rcases HahnField.exists_root_of_scalePolynomial_comp_single_zero_with_property
      (k := k) (Γ := ℚ) G a (HasBoundedDenominatorSupport k)
      (fun w hw => hasBoundedDenominatorSupport_add k hw
        (hasBoundedDenominatorSupport_single k a (hasDenominator_zero 1)))
      (fun w hw => hasBoundedDenominatorSupport_mul k
        (hasBoundedDenominatorSupport_hahnMonomial k hδ) hw)
      hrootScaled with ⟨z, hzlower, hzbd, hzroot⟩
  have hzpos : (0 : WithTop ℚ) < HahnField.addVal k ℚ z := by
    have hδtop : (0 : WithTop ℚ) < (δ : ℚ) := by exact_mod_cast hδpos
    exact hδtop.trans_le hzlower
  exact ⟨z, hzpos, hzbd, hzroot⟩

end

end Puiseux

end HahnKaplanskyRealClosedness
