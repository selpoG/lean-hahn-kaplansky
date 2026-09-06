/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Newton.LowerEdge
import HahnKaplanskyRealClosedness.Puiseux.Lift.ClusterRoutes
import HahnKaplanskyRealClosedness.Puiseux.Newton.FixedStepSupport

/-!
# Fixed-level consumers of bounded affine Newton edges

This module transports the bounded-coefficient lower-multiplicity induction input to the
fixed-denominator valuation levels.  The reverse transport is already used by the fixed-level
route; keeping this direction separate makes the induction boundary explicit.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k] [LinearOrder k] [IsStrictOrderedRing k]

open HahnField

/-- A bounded fixed-step candidate can be returned to a finite ramified denominator level when
the fixed-lift polynomial is the Hahn image of a level polynomial.  The candidate support is the
single support obligation needed to construct the bounded Hahn root witness. -/
theorem FixedLevelRamifiedRoot.of_fixedStepChainFromData_candidate_isRoot
    [IsRealClosed k]
    {N : ℕ+} {G : Polynomial (fixedDenominatorValuationSubring k N)}
    {F : Polynomial (HahnField k ℚ)} {m : ℕ}
    {start : HahnField.valuationSubring k ℚ}
    (C : HahnField.KOddClusterFixedStepChainFromData k ℚ F m start)
    (hcandidate : HasBoundedDenominatorSupport k (C.candidate k ℚ : HahnField k ℚ))
    (hmap :
      C.liftData.lift =
        G.map (fixedDenominatorValuationToHahnValuationSubring k N))
    (hroot :
        (C.liftData.lift.map
          (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).IsRoot
        (C.candidate k ℚ : HahnField k ℚ)) :
    FixedLevelRamifiedRoot k N G := by
  rcases boundedRootInMaximalIdeal_of_fixedStepChainFromData_candidate_isRoot_of_bounded
      (k := k) C hcandidate hroot with ⟨x, hxmem, hxbd, hxroot⟩
  refine BoundedRootInMaximalIdeal.fixedLevelRamifiedRoot (k := k) (F := G)
    ⟨x, hxmem, hxbd, ?_⟩
  rw [← hmap]
  exact hxroot

private theorem fixedLevelRamifiedRoot_of_bounded_affineNewtonLowerEdge
    [IsRealClosed k]
    {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y)
    {G : Polynomial (HahnField k ℚ)} {δ : ℚ}
    (hG : G =
      (((F.comp (Polynomial.X + Polynomial.C y)).map
        (fixedDenominatorValuationToHahnValuationSubring k N)).map
          (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))))
    (hzero : HahnField.addVal k ℚ (G.coeff 0) =
      ((M • δ : ℚ) : WithTop ℚ))
    (hbelow : ∃ j, j < M ∧ j ∈ G.support ∧
      HahnField.newtonWeight k ℚ G δ j < (M • δ : ℚ))
    (hrootBelow : BoundedCoeffKOddClusterRootBelow k M) :
    FixedLevelRamifiedRoot k N (F.comp (Polynomial.X + Polynomial.C y)) := by
  let P : Polynomial (fixedDenominatorValuationSubring k N) :=
    F.comp (Polynomial.X + Polynomial.C y)
  let H : Polynomial (HahnField.valuationSubring k ℚ) :=
    P.map (fixedDenominatorValuationToHahnValuationSubring k N)
  have hHcluster : BoundedValuationSubringOddClusterHypotheses k H M := by
    simpa [P, H, fixedDenominatorValuationToHahnValuationSubring_map_comp_X_add_C
      (k := k) F y] using hbranch.translatedBoundedValuationHypotheses_comp (k := k)
  have hcoeff (i : ℕ) : G.coeff i = (H.coeff i : HahnField k ℚ) := by
    rw [hG]
    simp [P, H, Polynomial.coeff_map]
    rfl
  have hGbd : HasBoundedDenominatorSupportPolynomial k G := by
    intro i
    rw [hcoeff i]
    exact HahnField.ValuationSubringOddClusterHypothesesWithCoeffProperty.coeff
      (k := k) (Γ := ℚ) hHcluster i
  have hGm : G.coeff M ≠ 0 := by
    rw [hcoeff M]
    intro hzero'
    apply hHcluster.unit.ne_zero
    exact Subtype.ext hzero'
  have hmain : M ∈ G.support := Polynomial.mem_support_iff.mpr hGm
  have hmainval : HahnField.addVal k ℚ (G.coeff M) = 0 := by
    rw [hcoeff M]
    exact HahnField.addVal_eq_zero_of_isUnit k ℚ (H.coeff M) hHcluster.unit
  have htop : HahnField.coeffValueOfMemSupport k ℚ G hmain = 0 := by
    have hval' := hmainval
    rw [HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ G hmain] at hval'
    exact WithTop.coe_eq_coe.mp (by simpa using hval')
  have hnewtonZero : HahnField.newtonWeight k ℚ G δ 0 =
      ((M • δ : ℚ) : WithTop ℚ) := by
    rw [HahnField.newtonWeight, hzero]
    simp
  have hlower_pos : ∀ i, i < M → (hisupp : i ∈ G.support) →
      0 < HahnField.coeffValueOfMemSupport k ℚ G hisupp := by
    intro i hi hisupp
    have hmem : H.coeff i ∈ IsLocalRing.maximalIdeal
        (HahnField.valuationSubring k ℚ) :=
      HahnField.ValuationSubringOddClusterHypothesesWithCoeffProperty.small
        (k := k) (Γ := ℚ) hHcluster i hi
    have hpos : (0 : WithTop ℚ) < HahnField.addVal k ℚ (G.coeff i) := by
      rw [hcoeff i]
      exact (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ (H.coeff i)).mp hmem
    rw [HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ G hisupp] at hpos
    exact WithTop.coe_lt_coe.mp hpos
  have hnonneg : ∀ i, M < i → (hisupp : i ∈ G.support) →
      0 ≤ HahnField.coeffValueOfMemSupport k ℚ G hisupp := by
    intro i _ hisupp
    have hnonneg' : (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (G.coeff i) := by
      rw [hcoeff i]
      exact (H.coeff i).property
    rw [HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ G hisupp] at hnonneg'
    exact WithTop.coe_le_coe.mp hnonneg'
  rcases exists_bounded_root_of_lowerEdge_affine_newton_edge (k := k)
      hmain htop hbranch.odd hnewtonZero hlower_pos hbelow hnonneg hGbd hrootBelow with
    ⟨x, hxpos, hxbd, hxroot⟩
  have hrootP :
      ((P.map (fixedDenominatorValuationToHahnValuationSubring k N)).map
        (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).IsRoot x := by
    simpa [P, H, hG] using hxroot
  let z : HahnField.valuationSubring k ℚ := ⟨x, le_of_lt hxpos⟩
  have hzmem : z ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) :=
    (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ z).mpr (by simpa [z] using hxpos)
  have hzroot : (P.map (fixedDenominatorValuationToHahnValuationSubring k N)).IsRoot z := by
    rw [Polynomial.IsRoot] at hrootP ⊢
    have hcoe :
        (((P.map (fixedDenominatorValuationToHahnValuationSubring k N)).eval z :
          HahnField.valuationSubring k ℚ) : HahnField k ℚ) = 0 := by
      calc
        (((P.map (fixedDenominatorValuationToHahnValuationSubring k N)).eval z :
            HahnField.valuationSubring k ℚ) : HahnField k ℚ) =
            ((P.map (fixedDenominatorValuationToHahnValuationSubring k N)).map
              (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).eval
              (z : HahnField k ℚ) := by
                exact (HahnField.eval_map_algebraMap_eq_coe_eval k ℚ
                  (P.map (fixedDenominatorValuationToHahnValuationSubring k N)) z).symm
        _ = 0 := hrootP
    exact Subtype.ext hcoe
  exact BoundedRootInMaximalIdeal.fixedLevelRamifiedRoot (k := k)
    (F := P) ⟨z, hzmem, hxbd, hzroot⟩

private theorem boundedRootInMaximalIdeal_of_fixedLevel_nonlower_initialRoot
    [IsRealClosed k]
    {N : ℕ+} {F : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    {y : fixedDenominatorValuationSubring k N}
    (hbranch : FixedLevelTranslatedSameMultiplicityZeroBranch k N F M y)
    {G : Polynomial (HahnField k ℚ)}
    (hG : G = (((F.comp (Polynomial.X + Polynomial.C y)).map
      (fixedDenominatorValuationToHahnValuationSubring k N)).map
        (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))))
    {δ : ℚ} (hδpos : 0 < δ)
    (hzero : HahnField.addVal k ℚ (G.coeff 0) =
      ((M • δ : ℚ) : WithTop ℚ))
    (hgood : ∀ j, 0 < j → j < M →
      (((M - j) • δ : ℚ) : WithTop ℚ) ≤
        HahnField.addVal k ℚ (G.coeff j))
    {a : k} {r : ℕ}
    (hrpos : 0 < r) (hrodd : Odd r) (hrlt : r < M)
    (hmul : (HahnField.newtonInitialPolynomial k ℚ G δ (M • δ)).rootMultiplicity a = r)
    (hrootBelow : BoundedCoeffKOddClusterRootBelow k M) :
    BoundedRootInMaximalIdeal k
      ((F.comp (Polynomial.X + Polynomial.C y)).map
        (fixedDenominatorValuationToHahnValuationSubring k N)) := by
  let P : Polynomial (fixedDenominatorValuationSubring k N) :=
    F.comp (Polynomial.X + Polynomial.C y)
  let R : Polynomial (HahnField.valuationSubring k ℚ) :=
    P.map (fixedDenominatorValuationToHahnValuationSubring k N)
  let Q : Polynomial (HahnField k ℚ) :=
    R.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))
  have hGQ : G = Q := by
    simpa [P, R, Q] using hG
  have hRcluster : BoundedValuationSubringOddClusterHypotheses k R M := by
    simpa [P, R, fixedDenominatorValuationToHahnValuationSubring_map_comp_X_add_C
      (k := k) F y] using hbranch.translatedBoundedValuationHypotheses_comp (k := k)
  have hval : HahnField.addVal k ℚ ((R.eval 0 :
      HahnField.valuationSubring k ℚ) : HahnField k ℚ) =
      ((M • δ : ℚ) : WithTop ℚ) := by
    have hcoeff : Q.coeff 0 =
        ((R.eval 0 : HahnField.valuationSubring k ℚ) : HahnField k ℚ) := by
      simp only [Q, Polynomial.coeff_map]
      change ((R.coeff 0 : HahnField.valuationSubring k ℚ) : HahnField k ℚ) =
        ((R.eval 0 : HahnField.valuationSubring k ℚ) : HahnField k ℚ)
      rw [Polynomial.coeff_zero_eq_eval_zero]
    rw [← hcoeff]
    simpa [hGQ] using hzero
  have hunit : IsUnit ((R.comp (Polynomial.X + Polynomial.C (0 :
      HahnField.valuationSubring k ℚ))).coeff M) := by
    simpa using hRcluster.unit
  have hnotBelow : ∀ j, 0 < j → j < M →
      (((M - j) • δ : ℚ) : WithTop ℚ) ≤
        HahnField.addVal k ℚ
          ((R.comp (Polynomial.X + Polynomial.C (0 :
            HahnField.valuationSubring k ℚ))).coeff j : HahnField k ℚ) := by
    intro j hjpos hjM
    simpa [Q, hGQ, Algebra.algebraMap_ofSubsemiring_apply] using hgood j hjpos hjM
  have hgeR := HahnField.newtonWeight_ge_map_comp_X_add_C_of_unit_scale_nonbelow
    (k := k) (Γ := ℚ) (g := R) (A := 0) (m := M) (δ := δ) (γ := M • δ)
    hval hunit hδpos rfl hnotBelow
  have hge : ∀ i, ((M • δ : ℚ) : WithTop ℚ) ≤
      HahnField.newtonWeight k ℚ G δ i := by
    intro i
    simpa [Q, hGQ] using hgeR i
  have hGbd : HasBoundedDenominatorSupportPolynomial k G := by
    intro i
    simpa [Q, hGQ, Algebra.algebraMap_ofSubsemiring_apply] using
      HahnField.ValuationSubringOddClusterHypothesesWithCoeffProperty.coeff
        (k := k) (Γ := ℚ) hRcluster i
  rcases exists_bounded_root_of_nonlower_initial_root (k := k) hδpos hge hrpos hrodd hrlt
      hmul hGbd hrootBelow with ⟨z, hzpos, hzbd, hzroot⟩
  let zO : HahnField.valuationSubring k ℚ := ⟨z, le_of_lt hzpos⟩
  have hzmem : zO ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) :=
    (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ zO).mpr (by simpa [zO] using hzpos)
  have hzrootQ : Q.IsRoot (zO : HahnField k ℚ) := by
    simpa [Q, hGQ, zO] using hzroot
  have hzrootR : R.IsRoot zO := by
    rw [Polynomial.IsRoot] at hzrootQ ⊢
    have hcoe : ((R.eval zO : HahnField.valuationSubring k ℚ) : HahnField k ℚ) = 0 := by
      calc
        ((R.eval zO : HahnField.valuationSubring k ℚ) : HahnField k ℚ) =
            (R.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).eval
              (zO : HahnField k ℚ) := by
                exact (HahnField.eval_map_algebraMap_eq_coe_eval k ℚ R zO).symm
        _ = 0 := hzrootQ
    exact Subtype.ext hcoe
  exact ⟨zO, hzmem, hzbd, hzrootR⟩

/-- A fixed-step chain for a translated fixed-level polynomial, started at zero, is only needed
in the non-lower-edge branch.  The affine lower-edge branch is handled directly by the bounded
support root theorem below. -/
private def FixedLevelSameMultiplicityFixedStepContinuationAt [IsRealClosed k]
    (M : ℕ) : Prop :=
  ∀ {N : ℕ+} {G : Polynomial (fixedDenominatorValuationSubring k N)}
    {y : fixedDenominatorValuationSubring k N},
    FixedLevelTranslatedSameMultiplicityZeroBranch k N G M y →
      (G.comp (Polynomial.X + Polynomial.C y)).coeff 0 ≠ 0 →
        ∃ δ : ℚ, 0 < δ ∧
          HahnField.addVal k ℚ
              (((((G.comp (Polynomial.X + Polynomial.C y)).map
                (fixedDenominatorValuationToHahnValuationSubring k N)).map
              (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).coeff 0)) =
            ((M • δ : ℚ) : WithTop ℚ) ∧
            ((∃ a : k, ∃ r : ℕ,
                0 < r ∧ Odd r ∧ r < M ∧
                  (HahnField.newtonInitialPolynomial k ℚ
                    (((G.comp (Polynomial.X + Polynomial.C y)).map
                      (fixedDenominatorValuationToHahnValuationSubring k N)).map
                      (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)))
                    δ (M • δ)).rootMultiplicity a = r) ∨
              PositiveHahnRootInMap k
                ((G.comp (Polynomial.X + Polynomial.C y)).map
                  (fixedDenominatorValuationToHahnValuationSubring k N)) ∨
              ∃ C : HahnField.KOddClusterFixedStepChainFromData k ℚ
                (((G.comp (Polynomial.X + Polynomial.C y)).map
                    (fixedDenominatorValuationToHahnValuationSubring k N)).map
                  (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))) M
                0,
              C.liftData.lift =
                  (G.comp (Polynomial.X + Polynomial.C y)).map
                    (fixedDenominatorValuationToHahnValuationSubring k N) ∧
                ((∃ L : ℕ+, ∀ n : ℕ,
                    HasDenominator L (C.stepValue k ℚ n)) ∨
                  FixedStepFullInitialRootMultiplicity (k := k) C) ∧
                  (¬ BddAbove (Set.range (C.stepValue k ℚ)) ∨
                    (C.liftData.lift.map
                      (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).IsRoot
                      (C.candidate k ℚ : HahnField k ℚ)))

private theorem
    fixedLevelTranslatedSameMultiplicityZeroBranchRootHypothesisAt_of_fixedStepContinuation
    [IsRealClosed k]
    {M : ℕ} (hbelow : BoundedCoeffKOddClusterRootBelow k M)
    (hcontinue : FixedLevelSameMultiplicityFixedStepContinuationAt k M) :
    FixedLevelTranslatedSameMultiplicityZeroBranchRootAt k M := by
  intro N G y hymem hy0 hmultiple hrodd hbranch
  let P : Polynomial (fixedDenominatorValuationSubring k N) :=
    G.comp (Polynomial.X + Polynomial.C y)
  have hbranchData : FixedLevelTranslatedSameMultiplicityZeroBranch k N G M y :=
    ⟨hymem, hy0, hmultiple, hrodd, hbranch⟩
  by_cases hzero : P.coeff 0 = 0
  · refine ⟨1, 0, Ideal.zero_mem _, ?_⟩
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero]
    simp [Polynomial.coeff_map, P, hzero]
  · rcases hcontinue hbranchData hzero with ⟨δ, hδpos, hnewtonZero, hcontinue⟩
    let Q : Polynomial (HahnField k ℚ) :=
      (P.map (fixedDenominatorValuationToHahnValuationSubring k N)).map
        (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))
    by_cases hgood :
        ∀ j, 0 < j → j < M →
          (((M - j) • δ : ℚ) : WithTop ℚ) ≤
            HahnField.addVal k ℚ (Q.coeff j)
    · rcases hcontinue with hinitial | hroot | hchain
      · rcases hinitial with ⟨a, r, hrpos, hrodd, hrlt, hmul⟩
        have hroot := boundedRootInMaximalIdeal_of_fixedLevel_nonlower_initialRoot
          (k := k) hbranchData (G := Q) (by rfl) hδpos
          (by simpa [Q, P] using hnewtonZero)
          (by simpa [Q, P] using hgood) hrpos hrodd hrlt hmul hbelow
        exact BoundedRootInMaximalIdeal.fixedLevelRamifiedRoot (k := k)
          (F := P) (by simpa [P] using hroot)
      · have hrootR : BoundedRootInMaximalIdeal k
            (P.map (fixedDenominatorValuationToHahnValuationSubring k N)) :=
          PositiveHahnRootInMap.boundedRootInMaximalIdeal (k := k) hroot
        exact BoundedRootInMaximalIdeal.fixedLevelRamifiedRoot (k := k) (F := P)
          (by simpa [P] using hrootR)
      rcases hchain with ⟨C, hmap, hstep, hroot_or_unbounded⟩
      have hcandidate : HasBoundedDenominatorSupport k
          (C.candidate k ℚ : HahnField k ℚ) :=
        by
          rcases hstep with hstep | hfull
          · rcases hstep with ⟨L, hstep⟩
            have hsource : ∃ L : ℕ+, ∀ n : ℕ,
                HasDenominatorSupport k L ((C.source n).1 : HahnField k ℚ) := by
              refine ⟨L, ?_⟩
              exact hasBoundedDenominatorSupport_fixedStepChainFromData_source_of_stepValue
                (k := k) C
                (by simpa [C.start_source] using hasDenominatorSupport_zero k L) hstep
            exact hasBoundedDenominatorSupport_fixedStepChainFromData_candidate_of_source
              (k := k) C hsource
          · have hcoeff : ∀ i : ℕ,
                HasDenominatorSupport k N
                  (C.liftData.lift.coeff i : HahnField k ℚ) := by
              intro i
              have hmap' : C.liftData.lift =
                  P.map (fixedDenominatorValuationToHahnValuationSubring k N) := by
                simpa [P] using hmap
              rw [hmap', Polynomial.coeff_map]
              change HasDenominatorSupport k N ((P.coeff i : Series k) : HahnField k ℚ)
              exact (P.coeff i).property.2
            have hcandidate' := candidate_bounded_of_full_initial_rootMultiplicity
              (k := k) C hcoeff
              (by simpa [C.start_source] using hasDenominatorSupport_zero k N) hfull
            exact hcandidate'
      have hroot :
          (C.liftData.lift.map
            (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).IsRoot
          (C.candidate k ℚ : HahnField k ℚ) := by
        rcases hroot_or_unbounded with hnot_bdd | hroot
        · exact C.candidate_isRoot_map_of_unboundedStepValue k ℚ hnot_bdd
        · exact hroot
      exact FixedLevelRamifiedRoot.of_fixedStepChainFromData_candidate_isRoot
        (k := k) C hcandidate hmap hroot
    · push Not at hgood
      rcases hgood with ⟨j, hjpos, hjM, hjbelow⟩
      have hjne : Q.coeff j ≠ 0 := by
        intro hzero'
        rw [hzero', AddValuation.map_zero] at hjbelow
        exact not_top_lt hjbelow
      have hjSupp : j ∈ Q.support := Polynomial.mem_support_iff.mpr hjne
      have hjbelowVal :
          HahnField.coeffValueOfMemSupport k ℚ Q hjSupp < (M - j) • δ := by
        apply WithTop.coe_lt_coe.mp
        calc
          ((HahnField.coeffValueOfMemSupport k ℚ Q hjSupp : ℚ) : WithTop ℚ) =
              HahnField.addVal k ℚ (Q.coeff j) :=
            (HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ Q hjSupp).symm
          _ < (((M - j) • δ : ℚ) : WithTop ℚ) := hjbelow
      have hnewtonBelow : HahnField.newtonWeight k ℚ Q δ j <
          ((M • δ : ℚ) : WithTop ℚ) := by
        rw [HahnField.newtonWeight_eq_of_mem_support k ℚ Q δ hjSupp]
        dsimp [HahnField.newtonWeightOfMemSupport]
        have hsum :
            HahnField.coeffValueOfMemSupport k ℚ Q hjSupp + j • δ <
              (M - j) • δ + j • δ := by
          simpa [add_comm] using add_lt_add_left hjbelowVal (j • δ)
        have hsplit : (M - j) • δ + j • δ = M • δ := by
          rw [← add_nsmul, Nat.sub_add_cancel hjM.le]
        have hsum' :
            HahnField.coeffValueOfMemSupport k ℚ Q hjSupp + j • δ < M • δ := by
          rw [← hsplit]
          exact hsum
        exact WithTop.coe_lt_coe.mpr hsum'
      exact fixedLevelRamifiedRoot_of_bounded_affineNewtonLowerEdge
        (k := k) hbranchData (G := Q) (δ := δ) (by rfl)
        (by simpa [Q] using hnewtonZero)
        ⟨j, hjM, hjSupp, hnewtonBelow⟩ hbelow

private theorem not_bddAbove_range_of_strictMono_of_common_denominator
    {f : ℕ → ℚ} {N : ℕ+}
    (hmono : StrictMono f)
    (hden : ∀ n, HasDenominator N (f n)) :
    ¬ BddAbove (Set.range f) := by
  intro hbdd
  rcases hbdd with ⟨b, hb⟩
  have hNpos : (0 : ℚ) < (N : ℚ) := by positivity
  have hgap : ∀ n, (1 : ℚ) / (N : ℚ) ≤ f (n + 1) - f n := by
    intro n
    have hdiff : HasDenominator N (f (n + 1) - f n) := by
      simpa [sub_eq_add_neg] using
        hasDenominator_add_same (hden (n + 1)) (hasDenominator_neg (hden n))
    rcases hdiff with ⟨z, hz⟩
    have hzpos : (0 : ℚ) < (z : ℚ) := by
      have hqpos : 0 < f (n + 1) - f n :=
        sub_pos.mpr (hmono (Nat.lt_succ_self n))
      rw [hz] at hqpos
      exact (div_pos_iff_of_pos_right hNpos).mp hqpos
    have hzint : (0 : ℤ) < z := by exact_mod_cast hzpos
    have hz1 : (1 : ℚ) ≤ (z : ℚ) := by
      have hz1int : (1 : ℤ) ≤ z := by
        simpa using (Int.add_one_le_iff.mpr hzint)
      exact_mod_cast hz1int
    rw [hz]
    exact (div_le_div_iff_of_pos_right hNpos).mpr hz1
  have hbound : ∀ n : ℕ, f 0 + (n : ℚ) / (N : ℚ) ≤ f n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep := hgap n
        have hi :
            f 0 + (n : ℚ) / (N : ℚ) + (1 : ℚ) / (N : ℚ) ≤
              f n + (1 : ℚ) / (N : ℚ) := by
          exact add_le_add_left ih ((1 : ℚ) / (N : ℚ))
        calc
          f 0 + ((n + 1 : ℕ) : ℚ) / (N : ℚ) =
              (f 0 + (n : ℚ) / (N : ℚ)) + (1 : ℚ) / (N : ℚ) := by
                push_cast
                ring
          _ ≤ f n + (1 : ℚ) / (N : ℚ) := hi
          _ ≤ f (n + 1) := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (b - f 0) * (N : ℚ) < (n : ℚ) :=
    exists_nat_gt ((b - f 0) * (N : ℚ))
  have hn' : b < f 0 + (n : ℚ) / (N : ℚ) := by
    have hdiv : b - f 0 < (n : ℚ) / (N : ℚ) := by
      apply (lt_div_iff₀ hNpos).mpr
      simpa [sub_mul] using hn
    linarith
  exact (not_lt_of_ge (hb ⟨n, rfl⟩)) (hn'.trans_le (hbound n))

private theorem exists_fixedLevel_step_of_no_positiveRoot
    [IsRealClosed k]
    {N : ℕ+} {Q : Polynomial (HahnField k ℚ)} {M : ℕ}
    (hbranch : HahnField.KTranslatedSameMultiplicityZeroBranch k ℚ Q M)
    (D : HahnField.KOddClusterLiftData k ℚ Q M)
    {A : HahnField.valuationSubring k ℚ}
    (hA : A ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ))
    (hAsupp : HasDenominatorSupport k N (A : HahnField k ℚ))
    (hDbd : ∀ i : ℕ, HasDenominatorSupport k N (D.lift.coeff i : HahnField k ℚ))
    (hrootBelow : BoundedCoeffKOddClusterRootBelow k M)
    (hno : ¬ PositiveHahnRootInMap k D.lift) :
    ∃ A' : HahnField.valuationSubring k ℚ,
      HahnField.OddClusterStep k ℚ D.lift M A A' ∧
        HasDenominatorSupport k N (A' : HahnField k ℚ) := by
  by_cases hroot : D.lift.IsRoot A
  · exfalso
    apply hno
    refine ⟨(A : HahnField k ℚ), ?_, ⟨N, hAsupp⟩, ?_⟩
    · exact (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ A).mp hA
    · rw [Polynomial.IsRoot]
      rw [HahnField.eval_map_algebraMap_eq_coe_eval]
      have hroot' : D.lift.eval A = 0 := by
        simpa [Polynomial.IsRoot] using hroot
      exact congrArg (fun z : HahnField.valuationSubring k ℚ =>
        (z : HahnField k ℚ)) hroot'
  have hmpos : 0 < M := Nat.lt_trans Nat.zero_lt_one hbranch.one_lt
  have hmodd : Odd M := hbranch.branch.1.odd
  rcases HahnField.exists_main_correction_improves_eval_at_of_cluster_with_value
      (k := k) (Γ := ℚ) (F := D.lift) (m := M) (y := A)
      hmpos hmodd D.lower D.unit hA (by rwa [Polynomial.IsRoot] at hroot) with
    ⟨γ, δ, _c, hδpos, hγpos, _hc, hscale, hval, _hmain⟩
  let H : Polynomial (HahnField k ℚ) :=
    (D.lift.comp (Polynomial.X + Polynomial.C A)).map
      (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))
  have hH_eq : H = Q.comp (Polynomial.X +
      Polynomial.C (A : HahnField k ℚ)) := by
    dsimp [H]
    rw [Polynomial.map_comp, D.map_eq]
    congr 1
    ext i
    by_cases hi : i = 0
    · subst i
      rw [Polynomial.coeff_map]
      simp only [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
      rfl
    · simp [Polynomial.coeff_C, hi]
  have hDmap : ∀ i : ℕ,
      HasDenominatorSupport k N
        ((D.lift.map
          (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))).coeff i) := by
    intro i
    rw [Polynomial.coeff_map]
    exact hDbd i
  have hHbd : HasBoundedDenominatorSupportPolynomial k H := by
    intro i
    refine ⟨N, ?_⟩
    have hcomp := hasDenominatorSupportPolynomial_comp_X_add_C_of_common_denominator
      (k := k) hDmap hAsupp i
    simpa [H, Polynomial.map_comp, Algebra.algebraMap_ofSubsemiring_apply] using hcomp
  have hunitA : IsUnit ((D.lift.comp (Polynomial.X + Polynomial.C A)).coeff M) :=
    HahnField.isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal
      k ℚ D.unit hA
  have hzero : HahnField.addVal k ℚ (H.coeff 0) =
      ((M • δ : ℚ) : WithTop ℚ) := by
    have hcoeff0 : H.coeff 0 =
        ((D.lift.eval A : HahnField.valuationSubring k ℚ) : HahnField k ℚ) := by
      simpa [H] using HahnField.coeff_zero_map_comp_X_add_C k ℚ D.lift A
    rw [hcoeff0]
    rw [← hscale] at hval
    exact hval
  have hmain : M ∈ H.support := by
    apply Polynomial.mem_support_iff.mpr
    dsimp [H]
    rw [Polynomial.coeff_map]
    intro hzero'
    apply hunitA.ne_zero
    exact Subtype.ext hzero'
  have hmainval : HahnField.addVal k ℚ (H.coeff M) = 0 := by
    dsimp [H]
    rw [Polynomial.coeff_map]
    exact HahnField.addVal_eq_zero_of_isUnit k ℚ _ hunitA
  have htop : HahnField.coeffValueOfMemSupport k ℚ H hmain = 0 := by
    have hval' := hmainval
    rw [HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ H hmain] at hval'
    exact WithTop.coe_eq_coe.mp (by simpa using hval')
  have htransport : ∀ {x : HahnField k ℚ},
      (0 : WithTop ℚ) < HahnField.addVal k ℚ x →
        HasBoundedDenominatorSupport k x → H.IsRoot x →
          PositiveHahnRootInMap k D.lift := by
    intro x hxpos hxbd hxroot
    have hApos : (0 : WithTop ℚ) < HahnField.addVal k ℚ (A : HahnField k ℚ) := by
      exact (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ A).mp hA
    rcases hxbd with ⟨N', hxbd⟩
    have hxbd' : HasDenominatorSupport k (N' * N) x :=
      hasDenominatorSupport_mono_den k
        (fun q hq => hasDenominator_mul_right (n' := N) hq) hxbd
    have hAsupp' : HasDenominatorSupport k (N' * N) (A : HahnField k ℚ) :=
      hasDenominatorSupport_mono_den k
        (fun q hq => by
          simpa [mul_comm] using (hasDenominator_mul_right (n' := N') hq)) hAsupp
    refine ⟨x + (A : HahnField k ℚ),
      (HahnField.addVal k ℚ).map_lt_add hxpos hApos,
      ⟨N' * N, hasDenominatorSupport_add k hxbd' hAsupp'⟩, ?_⟩
    have hxroot' := hxroot
    rw [hH_eq] at hxroot'
    have hQroot : Q.IsRoot (x + (A : HahnField k ℚ)) := by
      rw [Polynomial.IsRoot] at hxroot' ⊢
      simpa [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C] using hxroot'
    simpa [D.map_eq] using hQroot
  by_cases hnotBelow : ∀ j, 0 < j → j < M →
      (((M - j) • δ : ℚ) : WithTop ℚ) ≤
        HahnField.addVal k ℚ
          ((D.lift.comp (Polynomial.X + Polynomial.C A)).coeff j : HahnField k ℚ)
  · rcases
    exists_nonzero_root_odd_rootMultiplicity_newtonInitialPolynomial_map_comp_X_add_C_of_unit_scale
        k ℚ (g := D.lift) (A := A) (m := M) (δ := δ) (γ := γ)
        hmodd hval hδpos hunitA hscale with
    ⟨c, hc, hmulPos, hmulOdd, hmulLe⟩
    let p : Polynomial k :=
      HahnField.newtonInitialPolynomial k ℚ
        ((D.lift.comp (Polynomial.X + Polynomial.C A)).map
          (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))) δ γ
    have hpzero : p.coeff 0 ≠ 0 := by
      dsimp [p]
      exact HahnField.coeff_newtonInitialPolynomial_ne_zero_of_mem k ℚ
        (HahnField.zero_mem_newtonInitialSupport_map_comp_X_add_C_of_eval_addVal_eq
          k ℚ hval)
    have hpne : p ≠ 0 := by
      intro hp
      exact hpzero (by simp [p, hp])
    have hrootp : p.IsRoot c := (Polynomial.rootMultiplicity_pos hpne).mp (by
      simpa [p, H] using hmulPos)
    have hge : ∀ i ∈ Finset.range
        ((D.lift.comp (Polynomial.X + Polynomial.C A)).natDegree + 1),
        (γ : WithTop ℚ) ≤ HahnField.newtonWeight k ℚ H δ i := by
      intro i _hi
      exact HahnField.newtonWeight_ge_map_comp_X_add_C_of_unit_scale_nonbelow
        k ℚ hval hunitA hδpos hscale hnotBelow i
    have hdeg : p.natDegree = M := by
      dsimp [p, H]
      exact HahnField.natDegree_newtonInitialPolynomial_map_comp_X_add_C_eq_of_unit_scale
        k ℚ hδpos hunitA hscale
    have hrle : p.rootMultiplicity c ≤ M := by simpa [p, H, hdeg] using hmulLe
    by_cases hrlt : p.rootMultiplicity c < M
    · rcases exists_bounded_root_of_nonlower_initial_root (k := k)
          (G := H) (M := M) (δ := δ) (a := c) (r := p.rootMultiplicity c) hδpos
          (by
            intro i
            rw [hscale]
            exact HahnField.newtonWeight_ge_map_comp_X_add_C_of_unit_scale_nonbelow
              k ℚ hval hunitA hδpos hscale hnotBelow i)
          (by simpa [p, H] using hmulPos)
          (by simpa [p, H] using hmulOdd) hrlt
          (by
            rw [hscale]) hHbd hrootBelow with
        ⟨x, hxpos, hxbd, hxroot⟩
      exact False.elim (hno (htransport hxpos hxbd hxroot))
    · have hreq : p.rootMultiplicity c = M :=
        Nat.le_antisymm hrle (Nat.le_of_not_gt hrlt)
      have hδden : HasDenominator N δ := by
        exact hasDenominator_newtonStep_of_full_initial_rootMultiplicity
          (k := k) (F := D.lift) (m := M) (N := N) (y := A)
          (γ := M • δ) (δ := δ) hmpos hDbd hAsupp hδpos rfl hunitA hc
          (by
            rw [hscale]
            exact hreq)
      rcases HahnField.exists_oddClusterStep_of_current_edge_initial_root
          k ℚ hA hval hδpos hγpos hc hscale hge (by simpa [p] using hrootp) with
        ⟨A', hstep⟩
      rcases hstep with
        ⟨hA'mem, γ', δ', c', hδ'pos, hγ'pos, hc', hscale', hA'eq, hval', hdiff', himprove'⟩
      have hγeq : γ' = γ := by
        apply WithTop.coe_injective
        exact hval'.symm.trans hval
      have hδeq : δ' = δ := by
        apply nsmul_right_injective (M := ℚ) (Nat.ne_of_gt hmpos)
        rw [hγeq] at hscale'
        exact hscale'.trans hscale.symm
      refine ⟨A', ?_, ?_⟩
      · exact ⟨hA'mem, γ', δ', c', hδ'pos, hγ'pos, hc', hscale', hA'eq,
          hval', hdiff', himprove'⟩
      · have hδ'den : HasDenominator N δ' := by
          simpa [hδeq] using hδden
        rw [hA'eq]
        exact hasDenominatorSupport_add k
          (hasDenominatorSupport_singleOfNonneg k c' hδ'den (le_of_lt hδ'pos)) hAsupp
  · push Not at hnotBelow
    rcases hnotBelow with ⟨j, hjpos, hjM, hjbelow⟩
    have hjbelow' : HahnField.addVal k ℚ (H.coeff j) <
        (((M - j) • δ : ℚ) : WithTop ℚ) := by
      simpa [H, Algebra.algebraMap_ofSubsemiring_apply] using hjbelow
    have hjne : H.coeff j ≠ 0 := by
      intro hzero'
      rw [hzero', AddValuation.map_zero] at hjbelow'
      exact not_top_lt hjbelow'
    have hjSupp : j ∈ H.support := Polynomial.mem_support_iff.mpr hjne
    have hjbelowVal :
        HahnField.coeffValueOfMemSupport k ℚ H hjSupp < (M - j) • δ := by
      apply WithTop.coe_lt_coe.mp
      calc
        ((HahnField.coeffValueOfMemSupport k ℚ H hjSupp : ℚ) : WithTop ℚ) =
            HahnField.addVal k ℚ (H.coeff j) :=
          (HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ H hjSupp).symm
        _ < (((M - j) • δ : ℚ) : WithTop ℚ) := hjbelow'
    have hjnewton : HahnField.newtonWeight k ℚ H δ j <
        ((M • δ : ℚ) : WithTop ℚ) := by
      rw [HahnField.newtonWeight_eq_of_mem_support k ℚ H δ hjSupp]
      dsimp [HahnField.newtonWeightOfMemSupport]
      have hsum :
          HahnField.coeffValueOfMemSupport k ℚ H hjSupp + j • δ <
            (M - j) • δ + j • δ := by
        simpa [add_comm] using add_lt_add_left hjbelowVal (j • δ)
      have hsplit : (M - j) • δ + j • δ = M • δ := by
        rw [← add_nsmul, Nat.sub_add_cancel hjM.le]
      have hsum' :
          HahnField.coeffValueOfMemSupport k ℚ H hjSupp + j • δ < M • δ := by
        rw [← hsplit]
        exact hsum
      exact WithTop.coe_lt_coe.mpr hsum'
    have hnewtonZero : HahnField.newtonWeight k ℚ H δ 0 =
        ((M • δ : ℚ) : WithTop ℚ) := by
      rw [HahnField.newtonWeight, hzero]
      simp
    rcases exists_bounded_root_of_lowerEdge_affine_newton_edge (k := k)
        hmain htop hmodd hnewtonZero
        (by
          intro i hi hisupp
          have hsmall :
              (D.lift.comp (Polynomial.X + Polynomial.C A)).coeff i ∈
                IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) :=
            (D.translatedCluster k ℚ hA).1 i hi
          have hpos : (0 : WithTop ℚ) < HahnField.addVal k ℚ (H.coeff i) := by
            dsimp [H]
            rw [Polynomial.coeff_map]
            exact (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ _).mp hsmall
          rw [HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ H hisupp] at hpos
          exact WithTop.coe_lt_coe.mp hpos)
        ⟨j, hjM, hjSupp, hjnewton⟩
        (by
          intro i _hi hisupp
          have hnonneg : (0 : WithTop ℚ) ≤ HahnField.addVal k ℚ (H.coeff i) := by
            dsimp [H]
            rw [Polynomial.coeff_map]
            exact (HahnField.mem_valuationSubring_iff k ℚ _).mp
              ((D.lift.comp (Polynomial.X + Polynomial.C A)).coeff i).property
          rw [HahnField.addVal_coeff_eq_coeffValueOfMemSupport k ℚ H hisupp] at hnonneg
          exact WithTop.coe_le_coe.mp hnonneg)
        hHbd hrootBelow with ⟨x, hxpos, hxbd, hxroot⟩
    exact False.elim (hno (htransport hxpos hxbd hxroot))

theorem fixedLevelOddClusterRootBelow_of_boundedCoeffRootBelow
    [IsRealClosed k]
    {M : ℕ} (hbelow : BoundedCoeffKOddClusterRootBelow k M) :
    FixedLevelOddClusterRootBelow k M := by
  intro N F r hr hF
  let H : Polynomial (HahnField k ℚ) :=
    (F.map (fixedDenominatorValuationToHahnValuationSubring k N)).map
      (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))
  have hH : BoundedCoeffKOddClusterHypotheses k H r := by
    refine ⟨hF.pos, hF.odd, ?_, ?_, ?_, ?_⟩
    · intro i
      simp only [H, Polynomial.coeff_map]
      exact ⟨N, (F.coeff i).property.2⟩
    · intro i
      simp only [H, Polynomial.coeff_map]
      exact (HahnField.mem_valuationSubring_iff k ℚ
        (fixedDenominatorValuationToHahnValuationSubring k N (F.coeff i))).mp
        (fixedDenominatorValuationToHahnValuationSubring k N (F.coeff i)).property
    · intro i hi
      simp only [H, Polynomial.coeff_map]
      have hpos :
          (0 : WithTop ℚ) < addVal k (F.coeff i : Series k) :=
        (mem_fixedDenominator_maximalIdeal_iff_pos_addVal (k := k) (F.coeff i)).mp
          (hF.small i hi)
      simpa [addVal_apply, Algebra.algebraMap_ofSubsemiring_apply] using hpos
    · simp only [H, Polynomial.coeff_map]
      exact HahnField.addVal_eq_zero_of_isUnit k ℚ
        (fixedDenominatorValuationToHahnValuationSubring k N (F.coeff r))
        (hF.unit.map (fixedDenominatorValuationToHahnValuationSubring k N))
  rcases hbelow hr hH with ⟨y, hypos, hybd, hyroot⟩
  let yO : HahnField.valuationSubring k ℚ := ⟨y, le_of_lt hypos⟩
  have hrootO :
      (F.map (fixedDenominatorValuationToHahnValuationSubring k N)).IsRoot yO := by
    rw [Polynomial.IsRoot] at hyroot ⊢
    have hcoe :
        (((F.map (fixedDenominatorValuationToHahnValuationSubring k N)).eval yO :
          HahnField.valuationSubring k ℚ) : HahnField k ℚ) = 0 := by
      calc
        (((F.map (fixedDenominatorValuationToHahnValuationSubring k N)).eval yO :
            HahnField.valuationSubring k ℚ) : HahnField k ℚ) =
            H.eval (yO : HahnField k ℚ) := by
              exact (HahnField.eval_map_algebraMap_eq_coe_eval k ℚ
                (F.map (fixedDenominatorValuationToHahnValuationSubring k N)) yO).symm
        _ = 0 := by
          simpa [H, yO] using hyroot
    exact Subtype.ext hcoe
  exact BoundedRootInMaximalIdeal.fixedLevelRamifiedRoot (k := k)
    (F := F) ⟨yO, (HahnField.mem_maximalIdeal_iff_pos_addVal k ℚ yO).mpr
      (by simpa [yO] using hypos), hybd, hrootO⟩

private theorem exists_bounded_root_of_fixedLevelRootAt
    [IsRealClosed k]
    {M : ℕ} (hfixed : FixedLevelOddClusterRootAt k M)
    {F : Polynomial (HahnField k ℚ)}
    (hF : BoundedCoeffKOddClusterHypotheses k F M) :
    ∃ y : HahnField k ℚ,
      (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
        HasBoundedDenominatorSupport k y ∧ F.IsRoot y := by
  let FO : Polynomial (HahnField.valuationSubring k ℚ) :=
    valuationSubringPolynomialOfNonnegCoeffs k F
      (HahnField.KOddClusterHypothesesWithCoeffProperty.nonneg
        (k := k) (Γ := ℚ) hF)
  have hFbd : ∀ i : ℕ, HasBoundedDenominatorSupport k (F.coeff i) :=
    HahnField.KOddClusterHypothesesWithCoeffProperty.coeff
      (k := k) (Γ := ℚ) hF
  have hFObd : ∀ i : ℕ,
      HasBoundedDenominatorSupport k (FO.coeff i : HahnField k ℚ) := by
    intro i
    rw [show (FO.coeff i : HahnField k ℚ) = F.coeff i by
      exact coeff_valuationSubringPolynomialOfNonnegCoeffs (k := k) F
        (HahnField.KOddClusterHypothesesWithCoeffProperty.nonneg
          (k := k) (Γ := ℚ) hF) i]
    exact hFbd i
  let P : Polynomial (valuationSubring k) :=
    valuationSubringPolynomialOfHahn k FO hFObd
  rcases exists_fixedDenominatorValuationSubring_polynomial_coeff k P with ⟨N, hN⟩
  let incl := fixedDenominatorValuationToValuationSubring k N
  have hlifts : P ∈ Polynomial.lifts incl := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine ⟨⟨(P.coeff i : Series k), hN i⟩, ?_⟩
    ext
    rfl
  rcases Polynomial.exists_support_eq_of_mem_lifts hlifts with ⟨G, hGmap, _hGsupport⟩
  have hGcluster : FixedLevelOddCluster k N G M := by
    refine ⟨hF.pos, hF.odd, ?_, ?_⟩
    · intro i hi
      have hcoeff :
          incl (G.coeff i) = P.coeff i := by
        have h := congrArg (fun Q : Polynomial (valuationSubring k) => Q.coeff i)
          hGmap
        simpa [incl, Polynomial.coeff_map] using h
      have hFOsmall :
          FO.coeff i ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) := by
        rw [HahnField.mem_maximalIdeal_iff_pos_addVal]
        rw [coeff_valuationSubringPolynomialOfNonnegCoeffs]
        exact HahnField.KOddClusterHypothesesWithCoeffProperty.lower
          (k := k) (Γ := ℚ) hF i hi
      have hPsmall :
          P.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k) :=
        coeff_mem_maximalIdeal_valuationSubringPolynomialOfHahn
          (k := k) hFObd hFOsmall
      rw [mem_fixedDenominator_maximalIdeal_iff_pos_addVal]
      have hPpos :
          (0 : WithTop ℚ) < addVal k ((P.coeff i : valuationSubring k) : Series k) :=
        (mem_maximalIdeal_iff_pos_addVal (k := k) (P.coeff i)).mp hPsmall
      have hseries :
          ((G.coeff i : fixedDenominatorValuationSubring k N) : Series k) =
            ((P.coeff i : valuationSubring k) : Series k) :=
        congrArg (fun x : valuationSubring k => (x : Series k)) hcoeff
      simpa [hseries] using hPpos
    · have hcoeff :
          incl (G.coeff M) = P.coeff M := by
        have h := congrArg (fun Q : Polynomial (valuationSubring k) => Q.coeff M)
          hGmap
        simpa [incl, Polynomial.coeff_map] using h
      have hFOunit : IsUnit (FO.coeff M) :=
        (HahnField.isUnit_iff_addVal_eq_zero k ℚ (FO.coeff M)).mpr (by
          rw [coeff_valuationSubringPolynomialOfNonnegCoeffs]
          exact HahnField.KOddClusterHypothesesWithCoeffProperty.main
            (k := k) (Γ := ℚ) hF)
      have hPunit : IsUnit (P.coeff M) :=
        isUnit_coeff_valuationSubringPolynomialOfHahn (k := k) hFObd hFOunit
      have hPcc_ne : constantCoeffRingHom k (P.coeff M) ≠ 0 :=
        constantCoeffRingHom_ne_zero_of_isUnit k hPunit
      refine fixedDenominator_isUnit_of_constantCoeffRingHom_ne_zero
        (k := k) (G.coeff M) ?_
      intro hzero
      apply hPcc_ne
      rw [← hcoeff]
      simpa [incl, fixedDenominatorConstantCoeffRingHom] using hzero
  have hrootG : FixedLevelRamifiedRoot k N G := hfixed hGcluster
  have hrootH :
      BoundedRootInMaximalIdeal k
        (G.map (fixedDenominatorValuationToHahnValuationSubring k N)) :=
    FixedLevelRamifiedRoot.boundedRootInMaximalIdeal (k := k) hrootG
  have hmapFO :
      G.map (fixedDenominatorValuationToHahnValuationSubring k N) = FO := by
    calc
      G.map (fixedDenominatorValuationToHahnValuationSubring k N) =
          (G.map incl).map (toHahnValuationSubring k) := by
            rw [Polynomial.map_map]
            rfl
      _ = P.map (toHahnValuationSubring k) := by rw [hGmap]
      _ = FO := map_valuationSubringPolynomialOfHahn (k := k) FO hFObd
  rcases BoundedRootInMaximalIdeal.exists_positive_hahn_root (k := k) hrootH with
    ⟨y, hypos, hybd, hyroot⟩
  refine ⟨y, hypos, hybd, ?_⟩
  have hmapF :
      (G.map (fixedDenominatorValuationToHahnValuationSubring k N)).map
          (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)) = F := by
    calc
      (G.map (fixedDenominatorValuationToHahnValuationSubring k N)).map
          (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)) =
          FO.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)) := by
            rw [hmapFO]
      _ = F := by
        simpa [FO] using
          (map_valuationSubringPolynomialOfNonnegCoeffs
            (k := k) F
              (HahnField.KOddClusterHypothesesWithCoeffProperty.nonneg
                (k := k) (Γ := ℚ) hF))
  simpa [hmapF] using hyroot

private theorem exists_fixedLevel_chain_of_no_positiveRoot
    [IsRealClosed k]
    {N : ℕ+} {P : Polynomial (fixedDenominatorValuationSubring k N)} {M : ℕ}
    (hP : FixedLevelOddCluster k N P M)
    (hM : 1 < M)
    {Q : Polynomial (HahnField k ℚ)}
    (hQ : (P.map (fixedDenominatorValuationToHahnValuationSubring k N)).map
        (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ)) = Q)
    (hrootBelow : BoundedCoeffKOddClusterRootBelow k M)
    (hno : ¬ PositiveHahnRootInMap k
      (P.map (fixedDenominatorValuationToHahnValuationSubring k N))) :
    ∃ C : HahnField.KOddClusterFixedStepChainFromData k ℚ Q M 0,
      C.liftData.lift = P.map (fixedDenominatorValuationToHahnValuationSubring k N) ∧
        (∃ L : ℕ+, ∀ n : ℕ, HasDenominator L (C.stepValue k ℚ n)) ∧
          ¬ BddAbove (Set.range (C.stepValue k ℚ)) := by
  let R : Polynomial (HahnField.valuationSubring k ℚ) :=
    P.map (fixedDenominatorValuationToHahnValuationSubring k N)
  have hRcluster : BoundedValuationSubringOddClusterHypotheses k R M := by
    simpa [R] using hP.boundedValuationSubringHypotheses (k := k)
  let D : HahnField.KOddClusterLiftData k ℚ Q M :=
    { lift := R
      map_eq := by simpa [R] using hQ
      lower := fun i hi =>
        HahnField.ValuationSubringOddClusterHypothesesWithCoeffProperty.small
          (k := k) (Γ := ℚ) hRcluster i hi
      unit := hRcluster.unit }
  have hDbd : ∀ i : ℕ,
      HasDenominatorSupport k N (D.lift.coeff i : HahnField k ℚ) := by
    intro i
    dsimp [D, R]
    rw [Polynomial.coeff_map]
    change HasDenominatorSupport k N ((P.coeff i : Series k) : HahnField k ℚ)
    exact (P.coeff i).property.2
  have hbranch : HahnField.KTranslatedSameMultiplicityZeroBranch k ℚ Q M := by
    refine ⟨hM, ?_⟩
    exact (D.oddClusterHypotheses k ℚ hP.pos hP.odd).translatedZeroBranch
  let S : Type _ :=
    {A : HahnField.valuationSubring k ℚ //
      A ∈ IsLocalRing.maximalIdeal (HahnField.valuationSubring k ℚ) ∧
        HasDenominatorSupport k N (A : HahnField k ℚ)}
  let next : S → S := fun T =>
    let hstep := exists_fixedLevel_step_of_no_positiveRoot
      (k := k) hbranch D T.2.1 T.2.2 hDbd hrootBelow (by simpa [D, R] using hno)
    ⟨Classical.choose hstep, (Classical.choose_spec hstep).1.1,
      (Classical.choose_spec hstep).2⟩
  have hnext : ∀ T : S,
      HahnField.OddClusterStep k ℚ D.lift M T.1 (next T).1 := by
    intro T
    dsimp [next]
    exact (Classical.choose_spec (exists_fixedLevel_step_of_no_positiveRoot
      (k := k) hbranch D T.2.1 T.2.2 hDbd hrootBelow (by simpa [D, R] using hno))).1
  let U : ℕ → S :=
    Nat.rec
      ⟨0, Ideal.zero_mem _, hasDenominatorSupport_zero k N⟩
      (fun _ T => next T)
  have hUzero : (U 0).1 = 0 := by simp [U]
  have hUstep : ∀ n : ℕ,
      HahnField.OddClusterStep k ℚ D.lift M (U n).1 (U (n + 1)).1 := by
    intro n
    simpa [U] using hnext (U n)
  let C : HahnField.KOddClusterFixedStepChainFromData k ℚ Q M 0 :=
    { one_lt := hM
      liftData := D
      source := fun n => ⟨(U n).1, (U n).2.1⟩
      start_source := hUzero
      step := fun n => hUstep n }
  have hsource : ∀ n : ℕ,
      HasDenominatorSupport k N ((C.source n).1 : HahnField k ℚ) := by
    intro n
    simpa [C] using (U n).2.2
  have hstep : ∀ n : ℕ, HasDenominator N (C.stepValue k ℚ n) :=
    hasCommonDenominator_fixedStepChainFromData_stepValue_of_source
      (k := k) C hsource
  have hnot_bdd : ¬ BddAbove (Set.range (C.stepValue k ℚ)) :=
    not_bddAbove_range_of_strictMono_of_common_denominator
      C.stepValue_strictMono hstep
  refine ⟨C, ?_, ⟨N, hstep⟩, hnot_bdd⟩
  simp [C, D, R]

theorem boundedCoeffKOddClusterRootHypothesis_of_levelSimpleRootLift_or_same
    [IsRealClosed k]
    (hlift : LevelSimpleRootLiftHypothesis k) :
    BoundedCoeffKOddClusterRootHypothesis k := by
  have hAt : ∀ M : ℕ, ∀ {F : Polynomial (HahnField k ℚ)},
      BoundedCoeffKOddClusterHypotheses k F M →
        ∃ y : HahnField k ℚ,
          (0 : WithTop ℚ) < HahnField.addVal k ℚ y ∧
            HasBoundedDenominatorSupport k y ∧ F.IsRoot y := by
    intro M
    induction M using Nat.strong_induction_on with
    | h M ih =>
        intro F hF
        have hbelowCoeff : BoundedCoeffKOddClusterRootBelow k M := by
          intro F' r hr hcluster
          exact ih r hr hcluster
        have hbelowFixed : FixedLevelOddClusterRootBelow k M :=
          fixedLevelOddClusterRootBelow_of_boundedCoeffRootBelow (k := k) hbelowCoeff
        have hcontinueAt : FixedLevelSameMultiplicityFixedStepContinuationAt k M := by
          intro N G y hbranchData hP0
          let P : Polynomial (fixedDenominatorValuationSubring k N) :=
            G.comp (Polynomial.X + Polynomial.C y)
          have hP : FixedLevelOddCluster k N P M :=
            hbranchData.translatedOddCluster (k := k)
          let R : Polynomial (HahnField.valuationSubring k ℚ) :=
            P.map (fixedDenominatorValuationToHahnValuationSubring k N)
          let Q : Polynomial (HahnField k ℚ) :=
            R.map (algebraMap (HahnField.valuationSubring k ℚ) (HahnField k ℚ))
          have hRcluster : BoundedValuationSubringOddClusterHypotheses k R M := by
            simpa [R] using hP.boundedValuationSubringHypotheses (k := k)
          let D : HahnField.KOddClusterLiftData k ℚ Q M :=
            { lift := R
              map_eq := rfl
              lower := fun i hi =>
                HahnField.ValuationSubringOddClusterHypothesesWithCoeffProperty.small
                  (k := k) (Γ := ℚ) hRcluster i hi
              unit := hRcluster.unit }
          have hroot0 : ¬ D.lift.IsRoot (0 : HahnField.valuationSubring k ℚ) := by
            intro hroot
            apply hP0
            have hcoeff : D.lift.coeff 0 = 0 := by
              rw [Polynomial.IsRoot] at hroot
              rw [Polynomial.coeff_zero_eq_eval_zero]
              exact hroot
            have hinj : Function.Injective
                (fixedDenominatorValuationToHahnValuationSubring k N) := by
              intro a b hab
              ext
              exact congrArg (fun z : HahnField.valuationSubring k ℚ =>
                (z : HahnField k ℚ)) hab
            apply hinj
            simpa [D, R, Polynomial.coeff_map] using hcoeff
          rcases HahnField.exists_main_correction_improves_eval_at_of_cluster_with_value
              (k := k) (Γ := ℚ) (F := D.lift) (m := M)
              (y := 0) hP.pos hP.odd D.lower D.unit (Ideal.zero_mem _)
              (by rwa [Polynomial.IsRoot] at hroot0) with
            ⟨γ, δ, c, hδpos, _hγpos, _hc, hscale, hval, _himprove⟩
          have hcoeff0 : Q.coeff 0 =
              ((D.lift.eval (0 : HahnField.valuationSubring k ℚ) :
                HahnField.valuationSubring k ℚ) : HahnField k ℚ) := by
            calc
              Q.coeff 0 = Q.eval (0 : HahnField k ℚ) :=
                Polynomial.coeff_zero_eq_eval_zero Q
              _ = ((D.lift.eval (0 : HahnField.valuationSubring k ℚ) :
                HahnField.valuationSubring k ℚ) : HahnField k ℚ) := by
                simpa [Q, D] using
                  (HahnField.eval_map_algebraMap_eq_coe_eval k ℚ R
                    (0 : HahnField.valuationSubring k ℚ))
          have hnewtonZero : HahnField.addVal k ℚ (Q.coeff 0) =
              ((M • δ : ℚ) : WithTop ℚ) := by
            rw [hcoeff0]
            rw [← hscale] at hval
            exact hval
          refine ⟨δ, hδpos, hnewtonZero, ?_⟩
          by_cases hrootQ : PositiveHahnRootInMap k R
          · exact Or.inr (Or.inl (by simpa [P] using hrootQ))
          · rcases exists_fixedLevel_chain_of_no_positiveRoot
                (k := k) hP hbranchData.one_lt (Q := Q) (by rfl)
                hbelowCoeff (by simpa [D] using hrootQ) with ⟨C, hmap, hstep, hnot_bdd⟩
            exact Or.inr (Or.inr ⟨C, by simpa [P] using hmap,
              Or.inl hstep, Or.inl hnot_bdd⟩)
        have hsameAt : FixedLevelTranslatedSameMultiplicityZeroBranchRootAt k M :=
          fixedLevelTranslatedSameMultiplicityZeroBranchRootHypothesisAt_of_fixedStepContinuation
            (k := k) hbelowCoeff hcontinueAt
        have hfixed : FixedLevelOddClusterRootAt k M :=
          fixedLevelOddClusterRootAt_of_below_levelSimpleRootLift_or_same
            (k := k) hlift hbelowFixed hsameAt
        exact exists_bounded_root_of_fixedLevelRootAt (k := k) hfixed hF
  intro F M hmpos hModd hFbd hnonneg hlower hmain
  exact hAt M ⟨hmpos, hModd, hFbd, hnonneg, hlower, hmain⟩

end

end Puiseux

end HahnKaplanskyRealClosedness
