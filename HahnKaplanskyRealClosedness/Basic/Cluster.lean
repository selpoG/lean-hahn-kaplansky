/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Basic.Residue

/-!
# K[X]-level odd-cluster route and high-level reductions
-/

namespace HahnKaplanskyRealClosedness

open Polynomial
open HahnSeries

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- Bundled coefficient conditions for the `K[X]` odd-cluster statement. -/
def KOddClusterHypotheses (F : (HahnField k Γ)[X]) (m : ℕ) : Prop :=
  0 < m ∧ Odd m ∧
    (∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i)) ∧
      (∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i)) ∧
        addVal k Γ (F.coeff m) = 0

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.pos {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    0 < m :=
  h.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.odd {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    Odd m :=
  h.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.nonneg {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i) :=
  h.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.lower {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    ∀ i, i < m → (0 : WithTop Γ) < addVal k Γ (F.coeff i) :=
  h.2.2.2.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.main {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    addVal k Γ (F.coeff m) = 0 :=
  h.2.2.2.2

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem coeff_newtonInitialPolynomial_zero_zero_eq_zero_of_KOddCluster_lt
    {F : (HahnField k Γ)[X]} {m i : ℕ}
    (h : KOddClusterHypotheses k Γ F m) (hi : i < m) :
    (newtonInitialPolynomial k Γ F 0 0).coeff i = 0 := by
  rw [coeff_newtonInitialPolynomial]
  apply newtonInitialCoeff_of_notMem
  intro hmem
  rcases (mem_newtonInitialSupport k Γ F 0 0).mp hmem with ⟨_hisupp, hweight⟩
  have hval : addVal k Γ (F.coeff i) = 0 := by
    simpa [newtonWeight] using hweight
  exact (ne_of_gt (KOddClusterHypotheses.lower (k := k) (Γ := Γ) h i hi)) hval

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem coeff_newtonInitialPolynomial_zero_zero_ne_zero_of_KOddCluster
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    (newtonInitialPolynomial k Γ F 0 0).coeff m ≠ 0 := by
  rw [coeff_newtonInitialPolynomial]
  apply newtonInitialCoeff_ne_zero_of_mem
  rw [mem_newtonInitialSupport]
  constructor
  · rw [Polynomial.mem_support_iff]
    intro hcoeff
    have htop : addVal k Γ (F.coeff m) = ⊤ := by
      rw [hcoeff, AddValuation.map_zero]
    rw [h.main] at htop
    exact WithTop.coe_ne_top (a := (0 : Γ)) htop
  · simp [newtonWeight, h.main]

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem natTrailingDegree_newtonInitialPolynomial_zero_zero_of_KOddCluster
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    (newtonInitialPolynomial k Γ F 0 0).natTrailingDegree = m := by
  let p : k[X] := newtonInitialPolynomial k Γ F 0 0
  have hcoeff_ne : p.coeff m ≠ 0 :=
    coeff_newtonInitialPolynomial_zero_zero_ne_zero_of_KOddCluster k Γ h
  have hp_ne : p ≠ 0 := by
    intro hp
    exact hcoeff_ne (by rw [hp, Polynomial.coeff_zero])
  apply le_antisymm
  · exact Polynomial.natTrailingDegree_le_of_ne_zero hcoeff_ne
  · apply Polynomial.le_natTrailingDegree hp_ne
    intro i hi
    exact coeff_newtonInitialPolynomial_zero_zero_eq_zero_of_KOddCluster_lt k Γ h hi

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem rootMultiplicity_zero_newtonInitialPolynomial_zero_zero_of_KOddCluster
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    (newtonInitialPolynomial k Γ F 0 0).rootMultiplicity 0 = m := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  exact natTrailingDegree_newtonInitialPolynomial_zero_zero_of_KOddCluster k Γ h

/-- A root at a fixed odd-cluster multiplicity. -/
def KOddClusterRootAt (m : ℕ) : Prop :=
  ∀ {F : (HahnField k Γ)[X]},
    KOddClusterHypotheses k Γ F m → PositiveHahnRoot k Γ F

/-- Roots for all odd-cluster multiplicities below `M`. -/
def KOddClusterRootBelow (M : ℕ) : Prop :=
  ∀ {F : (HahnField k Γ)[X]} {m : ℕ},
    m < M → KOddClusterHypotheses k Γ F m → PositiveHahnRoot k Γ F

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem kOddClusterRootBelow_zero :
    KOddClusterRootBelow k Γ 0 := by
  intro F m hm
  omega

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem kOddClusterRootBelow_succ_of_rootBelow_rootAt {M : ℕ}
    (hbelow : KOddClusterRootBelow k Γ M) (hAt : KOddClusterRootAt k Γ M) :
    KOddClusterRootBelow k Γ (M + 1) := by
  intro F m hm hcluster
  by_cases hlt : m < M
  · exact hbelow hlt hcluster
  · have hEq : m = M := by omega
    subst m
    exact hAt hcluster

/-- A selected odd residue branch of the zero-slope initial polynomial.

This is the Hahn analogue of the Puiseux residue branch API, stripped of fixed-level and
denominator data.  The branch records that the initial polynomial has an odd root multiplicity
`r` at residue root `a`. -/
def KResidueBranchMultiplicity (F : (HahnField k Γ)[X]) (m : ℕ) (a : k)
    (r : ℕ) : Prop :=
  KOddClusterHypotheses k Γ F m ∧
    (newtonInitialPolynomial k Γ F 0 0).rootMultiplicity a = r ∧ 0 < r ∧ r ≤ m ∧ Odd r

/-- A translated branch whose chosen residue root is `0`. -/
def KTranslatedZeroBranch (F : (HahnField k Γ)[X]) (m r : ℕ) : Prop :=
  KResidueBranchMultiplicity k Γ F m 0 r

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.zero_residueBranchMultiplicity
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    KResidueBranchMultiplicity k Γ F m 0 m :=
  ⟨h, rootMultiplicity_zero_newtonInitialPolynomial_zero_zero_of_KOddCluster k Γ h,
    h.pos, le_rfl, h.odd⟩

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KOddClusterHypotheses.translatedZeroBranch
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    KTranslatedZeroBranch k Γ F m m :=
  h.zero_residueBranchMultiplicity

/-- Same-multiplicity translated branch.  This is the boundary that must not be hidden inside
the ordinary induction step. -/
def KTranslatedSameMultiplicityZeroBranch (F : (HahnField k Γ)[X]) (m : ℕ) : Prop :=
  1 < m ∧ KTranslatedZeroBranch k Γ F m m

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KTranslatedSameMultiplicityZeroBranch.one_lt
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    1 < m :=
  h.1

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem KTranslatedSameMultiplicityZeroBranch.branch
    {F : (HahnField k Γ)[X]} {m : ℕ}
    (h : KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    KTranslatedZeroBranch k Γ F m m :=
  h.2

/-- Same-multiplicity omega continuation closes the same-multiplicity branch. -/
def KSameMultiplicityOmegaContinuationHypothesis : Prop :=
  ∀ {F : (HahnField k Γ)[X]} {m : ℕ},
    KTranslatedSameMultiplicityZeroBranch k Γ F m → PositiveHahnRoot k Γ F

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem kOddClusterRootBelow_all_of_inductionStep
    (hstep : ∀ M : ℕ, KOddClusterRootBelow k Γ M → KOddClusterRootAt k Γ M) :
    ∀ M : ℕ, KOddClusterRootBelow k Γ M := by
  intro M
  induction M with
  | zero =>
      exact kOddClusterRootBelow_zero k Γ
  | succ M ih =>
      exact kOddClusterRootBelow_succ_of_rootBelow_rootAt k Γ ih (hstep M ih)

/-- Omega continuation for all odd-cluster multiplicities strictly above one. -/
def KOddClusterOmegaContinuationAboveOneHypothesis : Prop :=
  ∀ {F : (HahnField k Γ)[X]} {m : ℕ},
    1 < m → KOddClusterHypotheses k Γ F m → PositiveHahnRoot k Γ F

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- Same-multiplicity omega continuation directly closes the above-one branch: an above-one
odd cluster is its own translated zero branch of the same multiplicity. -/
theorem kOddClusterOmegaContinuationAboveOneHypothesis_of_sameMultiplicityOmega
    (hsame : KSameMultiplicityOmegaContinuationHypothesis k Γ) :
    KOddClusterOmegaContinuationAboveOneHypothesis k Γ := by
  intro F m hm hcluster
  exact hsame ⟨hm, hcluster.translatedZeroBranch⟩

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem kOddClusterRootHypothesis_of_at_one_or_aboveOne
    (hone : KOddClusterRootAt k Γ 1)
    (habove : KOddClusterOmegaContinuationAboveOneHypothesis k Γ) :
    KOddClusterRootHypothesis k Γ := by
  intro F m hmpos hmodd hnonneg hlower hmain
  have hcluster : KOddClusterHypotheses k Γ F m :=
    ⟨hmpos, hmodd, hnonneg, hlower, hmain⟩
  by_cases hm : m = 1
  · subst m
    exact hone hcluster
  · have hmgt : 1 < m := by omega
    exact habove hmgt hcluster

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem kOddClusterRootHypothesis_of_at_one_or_sameMultiplicityOmega
    (hone : KOddClusterRootAt k Γ 1)
    (hsame : KSameMultiplicityOmegaContinuationHypothesis k Γ) :
    KOddClusterRootHypothesis k Γ :=
  kOddClusterRootHypothesis_of_at_one_or_aboveOne k Γ hone
    (kOddClusterOmegaContinuationAboveOneHypothesis_of_sameMultiplicityOmega k Γ hsame)

/-- If a monomial-scaled polynomial satisfies the `K[X]` odd-cluster coefficient inequalities,
then the original polynomial has a Hahn-field root. -/
theorem exists_root_of_KOddCluster_scaled
    (hCluster : KOddClusterRootHypothesis k Γ)
    {F : (HahnField k Γ)[X]} {m : ℕ} {δ lam : Γ}
    (hmpos : 0 < m) (hmodd : Odd m)
    (hintegral : ∀ i,
      (0 : WithTop Γ) ≤
        (-(lam : Γ) : WithTop Γ) + addVal k Γ (F.coeff i) + i • (δ : WithTop Γ))
    (hlower : ∀ i, i < m →
      (0 : WithTop Γ) <
        (-(lam : Γ) : WithTop Γ) + addVal k Γ (F.coeff i) + i • (δ : WithTop Γ))
    (hmain :
      (-(lam : Γ) : WithTop Γ) + addVal k Γ (F.coeff m) + m • (δ : WithTop Γ) =
        0) :
    ∃ x : HahnField k Γ, F.IsRoot x := by
  have hscaled : ∃ y : HahnField k Γ, (scalePolynomial k Γ F δ lam).IsRoot y := by
    rcases hCluster (F := scalePolynomial k Γ F δ lam) hmpos hmodd
        (by
          intro i
          simpa [addVal_coeff_scalePolynomial] using hintegral i)
        (by
          intro i hi
          simpa [addVal_coeff_scalePolynomial] using hlower i hi)
        (by
          simpa [addVal_coeff_scalePolynomial] using hmain) with
      ⟨y, _hy, hyroot⟩
    exact ⟨y, hyroot⟩
  exact exists_root_of_scalePolynomial_root k Γ hscaled

/-- Top-degree specialization of `exists_root_of_KOddCluster_scaled`.

This is the intended bridge from slope selection: once `δ` and `lam` make the scaled polynomial
integral, with all lower coefficients in the maximal ideal and the top coefficient a unit, the
original odd-degree polynomial has a root. -/
theorem exists_root_of_KOddCluster_natDegree_scaled
    (hCluster : KOddClusterRootHypothesis k Γ)
    {F : (HahnField k Γ)[X]} {δ lam : Γ}
    (hodd : Odd F.natDegree)
    (hintegral : ∀ i,
      (0 : WithTop Γ) ≤
        (-(lam : Γ) : WithTop Γ) + addVal k Γ (F.coeff i) + i • (δ : WithTop Γ))
    (hlower : ∀ i, i < F.natDegree →
      (0 : WithTop Γ) <
        (-(lam : Γ) : WithTop Γ) + addVal k Γ (F.coeff i) + i • (δ : WithTop Γ))
    (hmain :
      (-(lam : Γ) : WithTop Γ) + addVal k Γ (F.coeff F.natDegree) +
          F.natDegree • (δ : WithTop Γ) =
        0) :
    ∃ x : HahnField k Γ, F.IsRoot x := by
  apply exists_root_of_KOddCluster_scaled (k := k) (Γ := Γ) hCluster
  · exact Nat.pos_of_ne_zero (by
      intro hzero
      exact Nat.not_odd_zero (hzero ▸ hodd))
  · exact hodd
  · exact hintegral
  · exact hlower
  · exact hmain

/-- Over a nontrivial value group, the `K[X]` odd-cluster theorem implies odd-degree root
existence for Hahn-field polynomials: choose a very small slope so the natural-degree term becomes
the unique initial term after scaling. -/
theorem exists_root_of_KOddCluster_of_odd_natDegree_nontrivial
    [Nontrivial Γ] [DivisibleBy Γ ℕ]
    (hCluster : KOddClusterRootHypothesis k Γ)
    {F : (HahnField k Γ)[X]} (hodd : Odd F.natDegree) :
    ∃ x : HahnField k Γ, F.IsRoot x := by
  have hF : F ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hodd
    exact Nat.not_odd_zero hodd
  rcases exists_natDegree_dominating_slope k Γ hF with ⟨δ, γn, hγn, hdom⟩
  let lam : Γ := γn + F.natDegree • δ
  apply exists_root_of_KOddCluster_natDegree_scaled (k := k) (Γ := Γ) hCluster
    (δ := δ) (lam := lam) hodd
  · intro i
    by_cases hi_lt : i < F.natDegree
    · exact le_of_lt (by
        by_cases hisupp : i ∈ F.support
        · have hierase : i ∈ F.support.erase F.natDegree := by
            exact Finset.mem_erase.mpr ⟨ne_of_lt hi_lt, hisupp⟩
          have hpos := withTop_scaledValue_pos_of_dominating (Γ := Γ) (Nat.le_of_lt hi_lt)
            (hdom i hierase)
          simpa [lam, addVal_coeff_eq_coeffValueOfMemSupport k Γ F hisupp] using hpos
        · have hcoeff : F.coeff i = 0 := Polynomial.notMem_support_iff.mp hisupp
          simp [lam, hcoeff])
    · by_cases hi_eq : i = F.natDegree
      · subst i
        exact le_of_eq (by
          rw [hγn]
          simpa [lam] using
            (withTop_scaledValue_natDegree_eq_zero (Γ := Γ) F.natDegree γn δ).symm)
      · have hn_lt : F.natDegree < i := lt_of_le_of_ne (le_of_not_gt hi_lt) (Ne.symm hi_eq)
        have hcoeff : F.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn_lt
        simp [lam, hcoeff]
  · intro i hi
    by_cases hisupp : i ∈ F.support
    · have hierase : i ∈ F.support.erase F.natDegree := by
        exact Finset.mem_erase.mpr ⟨ne_of_lt hi, hisupp⟩
      have hpos := withTop_scaledValue_pos_of_dominating (Γ := Γ) (Nat.le_of_lt hi)
        (hdom i hierase)
      simpa [lam, addVal_coeff_eq_coeffValueOfMemSupport k Γ F hisupp] using hpos
    · have hcoeff : F.coeff i = 0 := Polynomial.notMem_support_iff.mp hisupp
      simp [lam, hcoeff]
  · rw [hγn]
    simpa [lam] using
      withTop_scaledValue_natDegree_eq_zero (Γ := Γ) F.natDegree γn δ

/-- Nontrivial-value-group form of the Hahn--Kaplansky reduction: the `K[X]` odd-cluster
theorem implies real-closedness of the Hahn field. -/
theorem isRealClosed_of_KOddCluster_nontrivial
    [IsRealClosed k] [Nontrivial Γ] [DivisibleBy Γ ℕ]
    (hCluster : KOddClusterRootHypothesis k Γ) :
    IsRealClosed (HahnField k Γ) := by
  apply isRealClosed_of_odd_roots k Γ
  intro F hodd
  exact exists_root_of_KOddCluster_of_odd_natDegree_nontrivial k Γ hCluster hodd

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If the value group is subsingleton, the Hahn field is real closed because it is ring
equivalent to the coefficient field. -/
theorem isRealClosed_of_subsingleton_valueGroup [IsRealClosed k] [Subsingleton Γ] :
    IsRealClosed (HahnField k Γ) :=
  isRealClosed_of_ringEquiv (subsingletonValueGroupRingEquiv k Γ)

end HahnField

end

end HahnKaplanskyRealClosedness
