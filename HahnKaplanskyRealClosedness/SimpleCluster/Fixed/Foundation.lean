/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.SimpleCluster.Omega

/-!
# Fixed-step foundation and lower-edge resolution
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- A fixed-lift step chain starting from a maximal-ideal source.  The zero-start chain is the
special case with `start := 0`; arbitrary starts arise after lower-edge improvement. -/
structure KOddClusterFixedStepChainFromData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (F : Polynomial (HahnField k Γ)) (m : ℕ) (start : valuationSubring k Γ) where
  one_lt : 1 < m
  liftData : KOddClusterLiftData k Γ F m
  source : ℕ → {A : valuationSubring k Γ // A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)}
  start_source : (source 0).1 = start
  step : ∀ n : ℕ, OddClusterStep k Γ liftData.lift m (source n).1 (source (n + 1)).1

/-- Same-multiplicity root-or-step input with the lower-multiplicity induction input explicit. -/
def KSameMultiplicityRootOrStepWithRootBelow
    [IsRealClosed k] [DivisibleBy Γ ℕ] : Prop :=
  ∀ {F : Polynomial (HahnField k Γ)} {m : ℕ},
    KOddClusterRootBelow k Γ m →
      KTranslatedSameMultiplicityZeroBranch k Γ F m →
        ∃ D : KOddClusterLiftData k Γ F m,
          ∀ A : valuationSubring k Γ,
            A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) →
              PositiveHahnRoot k Γ F ∨
                ∃ A' : valuationSubring k Γ, OddClusterStep k Γ D.lift m A A'

/-- Fixed-lift same-multiplicity root-or-step input.  Unlike
`KSameMultiplicityRootOrStepWithRootBelow`, this keeps the chosen lift data fixed.  This is the
form needed for terminal self-continuation, where the next bounded chain must continue from the
same lift that produced the terminal candidate step. -/
def KSameMultiplicityFixedLiftRootOrStepWithRootBelow
    [IsRealClosed k] [DivisibleBy Γ ℕ] : Prop :=
  ∀ {F : Polynomial (HahnField k Γ)} {m : ℕ},
    KOddClusterRootBelow k Γ m →
      KTranslatedSameMultiplicityZeroBranch k Γ F m →
        (D : KOddClusterLiftData k Γ F m) →
          ∀ A : valuationSubring k Γ,
            A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) →
              PositiveHahnRoot k Γ F ∨
                ∃ A' : valuationSubring k Γ, OddClusterStep k Γ D.lift m A A'

theorem KOddClusterLiftData.oddClusterHypotheses
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (D : KOddClusterLiftData k Γ F m) (hm_pos : 0 < m) (hm_odd : Odd m) :
    KOddClusterHypotheses k Γ F m := by
  refine ⟨hm_pos, hm_odd, ?_, ?_, ?_⟩
  · intro i
    rw [← D.map_eq, Polynomial.coeff_map]
    exact (D.lift.coeff i).property
  · intro i hi
    rw [← D.map_eq, Polynomial.coeff_map]
    exact (mem_maximalIdeal_iff_pos_addVal k Γ (D.lift.coeff i)).mp (D.lower i hi)
  · rw [← D.map_eq, Polynomial.coeff_map]
    exact addVal_eq_zero_of_isUnit k Γ (D.lift.coeff m) D.unit

theorem KTranslatedSameMultiplicityZeroBranch.comp_X_add_C
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbranch : KTranslatedSameMultiplicityZeroBranch k Γ F m)
    (A : valuationSubring k Γ)
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    KTranslatedSameMultiplicityZeroBranch k Γ
      (F.comp (Polynomial.X +
        Polynomial.C (algebraMap (valuationSubring k Γ) (HahnField k Γ) A))) m := by
  rcases exists_KOddClusterLiftData k Γ hbranch.branch.1 with ⟨D⟩
  refine ⟨hbranch.one_lt, ?_⟩
  exact (D.comp_X_add_C k Γ A hA).oddClusterHypotheses k Γ
    (KOddClusterHypotheses.pos k Γ hbranch.branch.1)
    (KOddClusterHypotheses.odd k Γ hbranch.branch.1)
    |>.translatedZeroBranch

/-- A source where some lower coefficient lies below the current `m`-slope edge.  The
complement is the non-below edge case where the Newton initial polynomial, rather than the
main term alone, must provide the next odd-cluster correction. -/
structure KSameMultiplicityLowerEdgeObstruction
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (F : Polynomial (HahnField k Γ)) (m : ℕ) where
  branch : KTranslatedSameMultiplicityZeroBranch k Γ F m
  liftData : KOddClusterLiftData k Γ F m
  source : valuationSubring k Γ
  source_mem : source ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)
  gamma : Γ
  delta : Γ
  eval_eq :
    addVal k Γ ((liftData.lift.eval source : valuationSubring k Γ) : HahnField k Γ) =
      (gamma : WithTop Γ)
  delta_pos : 0 < delta
  scale : m • delta = gamma
  index : ℕ
  index_pos : 0 < index
  index_lt : index < m
  below :
    addVal k Γ
        ((liftData.lift.comp (Polynomial.X + Polynomial.C source)).coeff index :
          HahnField k Γ) <
      (((m - index) • delta : Γ) : WithTop Γ)

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
private theorem lowerEdge_fullMultiplicity_factorization
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    {R : Polynomial k} {c : k} {m : ℕ}
    (hR : R ≠ 0) (hdeg : R.natDegree ≤ m)
    (hmul : R.rootMultiplicity c = m) :
    ∃ u : k, u ≠ 0 ∧ R = Polynomial.C u * (Polynomial.X - Polynomial.C c) ^ m := by
  have hdvd : (Polynomial.X - Polynomial.C c) ^ m ∣ R := by
    rw [← hmul]
    exact Polynomial.pow_rootMultiplicity_dvd R c
  rcases hdvd with ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hR
    simpa [hzero] using hq
  have hpow0 : (Polynomial.X - Polynomial.C c) ^ m ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c)
  have hqdeg : q.natDegree = 0 := by
    have hsum : m + q.natDegree = R.natDegree := by
      rw [hq, Polynomial.natDegree_mul hpow0 hq0,
        Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      simp
    omega
  let u := q.coeff 0
  have hqC : q = Polynomial.C u := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  have hu : u ≠ 0 := by
    intro hu0
    apply hq0
    rw [hqC, hu0, Polynomial.C_0]
  refine ⟨u, hu, ?_⟩
  rw [hq, hqC, mul_comm]

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
private theorem lowerEdge_exists_affine_newton_edge
    [Field k] [Nontrivial Γ] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [DivisibleBy Γ ℕ]
    {G : Polynomial (HahnField k Γ)} {δ : Γ} {n : ℕ}
    (hmain : n ∈ G.support)
    (htop : coeffValueOfMemSupport k Γ G hmain = 0)
    (hlower_pos : ∀ i, i < n → (hisupp : i ∈ G.support) →
      0 < coeffValueOfMemSupport k Γ G hisupp)
    (hbelow : ∃ j, j < n ∧ j ∈ G.support ∧
      newtonWeight k Γ G δ j < (n • δ : Γ))
    (hnonneg : ∀ i, n < i → (hisupp : i ∈ G.support) →
      0 ≤ coeffValueOfMemSupport k Γ G hisupp) :
    ∃ θ : Γ, 0 < θ ∧ θ < δ ∧
      (∀ i, ((n • θ : Γ) : WithTop Γ) ≤ newtonWeight k Γ G θ i) ∧
      ∃ j, j < n ∧ j ∈ G.support ∧
        newtonWeight k Γ G θ j = (n • θ : Γ) := by
  classical
  let S : Finset ℕ := G.support.filter (fun i => i < n)
  have hS : S.Nonempty := by
    rcases hbelow with ⟨j, hjlt, hjsupp, _⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨hjsupp, hjlt⟩⟩
  let ratio : ℕ → Γ := fun i =>
    if hi : i ∈ S then
      DivisibleBy.div
        (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hi).1)
        (n - i)
    else 0
  have hratio_pos : ∀ i, i ∈ S → 0 < ratio i := by
    intro i hi
    have hi_lt := (Finset.mem_filter.mp hi).2
    have hi_ne : n - i ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hi_lt)
    have hvalpos : 0 < coeffValueOfMemSupport k Γ G
        (Finset.mem_filter.mp hi).1 :=
      hlower_pos i hi_lt (Finset.mem_filter.mp hi).1
    have hdivpos : 0 < DivisibleBy.div
        (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hi).1) (n - i) := by
      by_contra hnot
      have hle : DivisibleBy.div
          (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hi).1) (n - i) ≤ 0 :=
        le_of_not_gt hnot
      have hmul_le : (n - i) • DivisibleBy.div
          (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hi).1) (n - i) ≤ 0 := by
        simpa using nsmul_le_nsmul_right hle (n - i)
      rw [DivisibleBy.div_cancel _ hi_ne] at hmul_le
      exact (not_le_of_gt hvalpos) hmul_le
    simpa [ratio, dif_pos hi] using hdivpos
  rcases Finset.exists_min_image S ratio hS with ⟨j₀, hj₀, hmin⟩
  let θ : Γ := ratio j₀
  have hθpos : 0 < θ := hratio_pos j₀ hj₀
  have hθlt : θ < δ := by
    rcases hbelow with ⟨j, hjlt, hjsupp, hjbelow⟩
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨hjsupp, hjlt⟩
    have hminj : ratio j₀ ≤ ratio j := hmin j hjS
    have hratioj : ratio j = DivisibleBy.div
        (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hjS).1) (n - j) := by
      simp [ratio, dif_pos hjS]
    have hval_lt :
        coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hjS).1 < (n - j) • δ := by
      have hsplit : n • δ = (n - j) • δ + j • δ := by
        rw [← add_nsmul, Nat.sub_add_cancel hjlt.le]
      have hbelow' :
          ((coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hjS).1 + j • δ : Γ) :
            WithTop Γ) < (n • δ : Γ) := by
        simpa [newtonWeight_eq_of_mem_support k Γ G δ hjsupp,
          newtonWeightOfMemSupport] using hjbelow
      have hbelowΓ :
          coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hjS).1 + j • δ <
            n • δ := WithTop.coe_lt_coe.mp hbelow'
      rw [hsplit] at hbelowΓ
      exact (add_lt_add_iff_right (j • δ)).mp hbelowΓ
    have hratioj_lt : ratio j < δ := by
      by_contra hnot
      have hle : δ ≤ ratio j := le_of_not_gt hnot
      have hmul : (n - j) • δ ≤ (n - j) • ratio j :=
        nsmul_le_nsmul_right hle (n - j)
      rw [hratioj, DivisibleBy.div_cancel _
        (Nat.ne_of_gt (Nat.sub_pos_of_lt hjlt))] at hmul
      exact (not_lt_of_ge hmul) hval_lt
    exact lt_of_le_of_lt hminj hratioj_lt
  have hge : ∀ i, ((n • θ : Γ) : WithTop Γ) ≤ newtonWeight k Γ G θ i := by
    intro i
    by_cases hi : i ∈ G.support
    · have hi_le : i ≤ n ∨ n < i := le_or_gt i n
      rcases hi_le with hi_le | hni
      · by_cases hin : i = n
        · subst i
          rw [newtonWeight_eq_of_mem_support k Γ G θ hi]
          dsimp [newtonWeightOfMemSupport]
          have htop' : coeffValueOfMemSupport k Γ G hi = 0 := by
            simpa using htop
          rw [htop']
          simp
        · have hi_lt : i < n := lt_of_le_of_ne hi_le hin
          have hiS : i ∈ S := Finset.mem_filter.mpr ⟨hi, hi_lt⟩
          have hmin_i : θ ≤ ratio i := by
            dsimp [θ]
            exact hmin i hiS
          have hi_ne : n - i ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hi_lt)
          have hratioi : ratio i = DivisibleBy.div
              (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hiS).1) (n - i) := by
            simp [ratio, dif_pos hiS]
          have hmul : (n - i) • θ ≤
              coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hiS).1 := by
            calc
              (n - i) • θ ≤ (n - i) • ratio i :=
                nsmul_le_nsmul_right hmin_i (n - i)
              _ = _ := by rw [hratioi, DivisibleBy.div_cancel _ hi_ne]
          rw [newtonWeight_eq_of_mem_support k Γ G θ hi]
          have hsplit : n • θ = (n - i) • θ + i • θ := by
            rw [← add_nsmul, Nat.sub_add_cancel hi_lt.le]
          calc
            ((n • θ : Γ) : WithTop Γ) =
                (((n - i) • θ + i • θ : Γ) : WithTop Γ) := by rw [hsplit]
            _ = (((n - i) • θ : Γ) : WithTop Γ) + ((i • θ : Γ) : WithTop Γ) := by
              rw [WithTop.coe_add, WithTop.coe_nsmul]
            _ ≤ ((coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hiS).1 : Γ) :
                  WithTop Γ) + ((i • θ : Γ) : WithTop Γ) := by
              have hmul' :
                  (((n - i) • θ : Γ) : WithTop Γ) ≤
                    (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hiS).1 : WithTop Γ) := by
                exact_mod_cast hmul
              have hmul'' := add_le_add_left hmul' ((i • θ : Γ) : WithTop Γ)
              simpa [add_comm, add_left_comm, add_assoc] using hmul''
            _ = ((coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hiS).1 + i • θ : Γ) :
                  WithTop Γ) := by rw [WithTop.coe_add]
      · rw [newtonWeight_eq_of_mem_support k Γ G θ hi]
        dsimp [newtonWeightOfMemSupport]
        have hnonneg' := hnonneg i hni hi
        have hpow : (n • θ : Γ) ≤ i • θ := by
          exact nsmul_le_nsmul_left (le_of_lt hθpos) (le_of_lt hni)
        exact_mod_cast hpow.trans (le_add_of_nonneg_left hnonneg')
    · rw [newtonWeight_eq_top_of_notMem_support k Γ G θ hi]
      exact le_top
  refine ⟨θ, hθpos, hθlt, hge, ?_⟩
  refine ⟨j₀, (Finset.mem_filter.mp hj₀).2, (Finset.mem_filter.mp hj₀).1, ?_⟩
  have hj₀ne : n - j₀ ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt (Finset.mem_filter.mp hj₀).2)
  have hratio₀ : ratio j₀ = DivisibleBy.div
      (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hj₀).1) (n - j₀) := by
    simp [ratio, dif_pos hj₀]
  have hmul₀eq :
      (n - j₀) • θ =
        coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hj₀).1 := by
    dsimp [θ]
    rw [hratio₀]
    exact DivisibleBy.div_cancel _ hj₀ne
  rw [newtonWeight_eq_of_mem_support k Γ G θ (Finset.mem_filter.mp hj₀).1]
  dsimp [newtonWeightOfMemSupport]
  have hsplit₀ : n • θ = (n - j₀) • θ + j₀ • θ := by
    rw [← add_nsmul, Nat.sub_add_cancel (Finset.mem_filter.mp hj₀).2.le]
  calc
    (coeffValueOfMemSupport k Γ G (Finset.mem_filter.mp hj₀).1 : WithTop Γ) +
        j₀ • (θ : WithTop Γ) =
        (((n - j₀) • θ : Γ) : WithTop Γ) + j₀ • (θ : WithTop Γ) := by
          simp [hmul₀eq]
    _ = (((n - j₀) • θ + j₀ • θ : Γ) : WithTop Γ) := by
          simp only [WithTop.coe_add, WithTop.coe_nsmul]
    _ = ((n • θ : Γ) : WithTop Γ) := by rw [hsplit₀]
    _ = n • (θ : WithTop Γ) := by rw [WithTop.coe_nsmul]

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
theorem exists_root_of_lowerEdge_affine_newton_edge_with_property
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [IsRealClosed k] [Nontrivial Γ] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [DivisibleBy Γ ℕ]
    {G : Polynomial (HahnField k Γ)} {n : ℕ} {δ : Γ}
    (hmain : n ∈ G.support)
    (htop : coeffValueOfMemSupport k Γ G hmain = 0)
    (hm : Odd n)
    (hzero : newtonWeight k Γ G δ 0 =
      ((n • δ : Γ) : WithTop Γ))
    (hlower_pos : ∀ i, i < n → (hisupp : i ∈ G.support) →
      0 < coeffValueOfMemSupport k Γ G hisupp)
    (hbelow : ∃ j, j < n ∧ j ∈ G.support ∧
      newtonWeight k Γ G δ j < (n • δ : Γ))
    (hnonneg : ∀ i, n < i → (hisupp : i ∈ G.support) →
      0 ≤ coeffValueOfMemSupport k Γ G hisupp)
    (P : HahnField k Γ → Prop)
    (hP_add : ∀ (y : HahnField k Γ) (a : k), P y →
      P (y + toLex (HahnSeries.single 0 a)))
    (hP_mul : ∀ (y : HahnField k Γ) (γ : Γ), P y →
      P (hahnMonomial k Γ γ * y))
    (hP_coeff : ∀ {θ μ : Γ} (a : k) (i : ℕ),
      P (((scalePolynomial k Γ G θ μ).comp
        (Polynomial.X + Polynomial.C (toLex (HahnSeries.single 0 a)))).coeff i))
    (hrootBelow : ∀ {H : Polynomial (HahnField k Γ)} {r : ℕ}, r < n →
      KOddClusterHypothesesWithCoeffProperty k Γ P H r →
      ∃ y : HahnField k Γ,
        (0 : WithTop Γ) < addVal k Γ y ∧ P y ∧ H.IsRoot y) :
    ∃ y : HahnField k Γ,
      (0 : WithTop Γ) < addVal k Γ y ∧ P y ∧ G.IsRoot y := by
  rcases lowerEdge_exists_affine_newton_edge (k := k) (Γ := Γ)
      hmain htop hlower_pos hbelow hnonneg with
    ⟨θ, hθpos, hθlt, hge, ⟨j, hjlt, hjsupp, hjweight⟩⟩
  let Q : Polynomial k := newtonInitialPolynomial k Γ G θ (n • θ)
  have hmainmem :
      n ∈ newtonInitialSupport k Γ G θ (n • θ) := by
    rw [mem_newtonInitialSupport]
    refine ⟨hmain, ?_⟩
    rw [newtonWeight_eq_of_mem_support k Γ G θ hmain]
    dsimp [newtonWeightOfMemSupport]
    simp [htop]
  have hhigh :
      ∀ i, n < i → i ∉ newtonInitialSupport k Γ G θ (n • θ) := by
    intro i hi hmem
    have hisupp := (mem_newtonInitialSupport k Γ G θ (n • θ)).mp hmem |>.1
    have hweight_gt :
        ((n • θ : Γ) : WithTop Γ) < newtonWeight k Γ G θ i := by
      rw [newtonWeight_eq_of_mem_support k Γ G θ hisupp]
      dsimp [newtonWeightOfMemSupport]
      have hnonneg' := hnonneg i hi hisupp
      have hpow : n • θ < i • θ := nsmul_lt_nsmul_left hθpos hi
      have hpow' :
          ((n • θ : Γ) : WithTop Γ) < ((i • θ : Γ) : WithTop Γ) := by
        exact_mod_cast hpow
      exact hpow'.trans_le (by exact_mod_cast le_add_of_nonneg_left hnonneg')
    exact (ne_of_gt hweight_gt) ((mem_newtonInitialSupport k Γ G θ (n • θ)).mp hmem).2
  have hQdeg : Q.natDegree = n := by
    dsimp [Q]
    exact natDegree_newtonInitialPolynomial_eq_of_mem_of_high_notMem k Γ hmainmem hhigh
  have hnne : n ≠ 0 := by
    intro hnzero
    exact Nat.not_odd_zero (hnzero ▸ hm)
  have hQne : Q ≠ 0 := by
    intro hzeroQ
    rw [hzeroQ, Polynomial.natDegree_zero] at hQdeg
    exact hnne hQdeg.symm
  have hjmem :
      j ∈ newtonInitialSupport k Γ G θ (n • θ) := by
    rw [mem_newtonInitialSupport]
    exact ⟨hjsupp, hjweight⟩
  have hQj : Q.coeff j ≠ 0 := by
    dsimp [Q]
    rw [coeff_newtonInitialPolynomial]
    exact newtonInitialCoeff_ne_zero_of_mem k Γ G θ (n • θ) hjmem
  have h0not : 0 ∉ newtonInitialSupport k Γ G θ (n • θ) := by
    intro h0
    have hweight0 := (mem_newtonInitialSupport k Γ G θ (n • θ)).mp h0 |>.2
    have hzeroθ :
        newtonWeight k Γ G θ 0 = ((n • δ : Γ) : WithTop Γ) := by
      simpa [newtonWeight] using hzero
    have hlt :
        ((n • θ : Γ) : WithTop Γ) < ((n • δ : Γ) : WithTop Γ) := by
      exact_mod_cast nsmul_lt_nsmul_right hnne hθlt
    have heq :
        ((n • θ : Γ) : WithTop Γ) = ((n • δ : Γ) : WithTop Γ) :=
      hweight0.symm.trans hzeroθ
    exact (ne_of_lt hlt) heq
  have hQ0 : Q.coeff 0 = 0 := by
    dsimp [Q]
    rw [coeff_newtonInitialPolynomial]
    exact newtonInitialCoeff_of_notMem k Γ G θ (n • θ) h0not
  rcases exists_root_odd_rootMultiplicity (p := Q) hQne
      (by simpa [hQdeg] using hm) with ⟨a, hapos, haodd⟩
  have hrootQ : Q.IsRoot a :=
    (Polynomial.rootMultiplicity_pos hQne).mp hapos
  have hrle : Q.rootMultiplicity a ≤ Q.natDegree := by
    have hdvd : (Polynomial.X - Polynomial.C a) ^ Q.rootMultiplicity a ∣ Q :=
      Polynomial.pow_rootMultiplicity_dvd Q a
    have hdeg_le :
        ((Polynomial.X - Polynomial.C a) ^ Q.rootMultiplicity a).natDegree ≤ Q.natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hQne
    simpa [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] using hdeg_le
  have hrlt : Q.rootMultiplicity a < n := by
    have hrle' : Q.rootMultiplicity a ≤ n := by simpa [hQdeg] using hrle
    by_contra hnot
    have hreq : Q.rootMultiplicity a = n :=
      Nat.le_antisymm hrle' (Nat.le_of_not_gt hnot)
    have hroot0 : Q.IsRoot 0 := by
      rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero]
      exact hQ0
    have hroot_eq : a = 0 := by
      rcases lowerEdge_fullMultiplicity_factorization (k := k) hQne
          (by simp [hQdeg]) hreq with ⟨u, hu, hfac⟩
      rw [Polynomial.IsRoot, hfac] at hroot0
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X] at hroot0
      have hsub : 0 - a = 0 := by
        by_contra hne
        exact hu ((mul_eq_zero.mp hroot0).resolve_right (pow_ne_zero _ hne))
      simpa using hsub
    have htrailing : Q.rootMultiplicity 0 = Q.natTrailingDegree :=
      Polynomial.rootMultiplicity_eq_natTrailingDegree'
    have htrail_le : Q.natTrailingDegree ≤ j :=
      Polynomial.natTrailingDegree_le_of_ne_zero hQj
    rw [hroot_eq, htrailing] at hreq
    omega
  have hcluster :
      KOddClusterHypotheses k Γ
        ((scalePolynomial k Γ G θ (n • θ)).comp
          (Polynomial.X + Polynomial.C (toLex (HahnSeries.single 0 a))))
        (Q.rootMultiplicity a) :=
    oddClusterHypotheses_scalePolynomial_comp_single_zero_of_rootMultiplicity
      k Γ G hge rfl hapos haodd
  have hrootScaled :
      ∃ y : HahnField k Γ,
        (0 : WithTop Γ) < addVal k Γ y ∧ P y ∧
          ((scalePolynomial k Γ G θ (n • θ)).comp
            (Polynomial.X + Polynomial.C (toLex (HahnSeries.single 0 a)))).IsRoot y := by
    apply hrootBelow hrlt
    refine ⟨hcluster.pos, hcluster.odd, ?_, hcluster.nonneg, hcluster.lower,
      hcluster.main⟩
    exact fun i => hP_coeff a i
  rcases exists_root_of_scalePolynomial_comp_single_zero_with_property
      (k := k) (Γ := Γ) G a P
      (fun y hy => hP_add y a hy)
      (fun y hy => hP_mul y θ hy)
      hrootScaled with ⟨z, hzlower, hzP, hzroot⟩
  have hδtop : (0 : WithTop Γ) < (θ : WithTop Γ) := by exact_mod_cast hθpos
  exact ⟨z, hδtop.trans_le hzlower, hzP, hzroot⟩

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- Solve a normalized odd Newton problem by descending along a lower Newton edge.

The degree-`n` coefficient has value zero, the constant and main terms lie on the
`δ`-line, every lower coefficient has positive value, and one lower coefficient lies
strictly below that line.  The resulting initial polynomial has a proper odd root
multiplicity, so `h_smaller_roots` solves the scaled-and-translated problem. -/
theorem positiveHahnRoot_of_lowerNewtonEdge
    [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    [IsRealClosed k] [Nontrivial Γ] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [DivisibleBy Γ ℕ]
    {G : Polynomial (HahnField k Γ)} {n : ℕ} {δ : Γ}
    (h_main_mem : n ∈ G.support)
    (h_main_value : coeffValueOfMemSupport k Γ G h_main_mem = 0)
    (h_m_odd : Odd n)
    (h_constant_on_line : newtonWeight k Γ G δ 0 =
      ((n • δ : Γ) : WithTop Γ))
    (h_lower_positive : ∀ i, i < n → (hisupp : i ∈ G.support) →
      0 < coeffValueOfMemSupport k Γ G hisupp)
    (h_lower_below_line : ∃ j, j < n ∧ j ∈ G.support ∧
      newtonWeight k Γ G δ j < (n • δ : Γ))
    (h_higher_nonnegative : ∀ i, n < i → (hisupp : i ∈ G.support) →
      0 ≤ coeffValueOfMemSupport k Γ G hisupp)
    (h_smaller_roots : KOddClusterRootBelow k Γ n) :
    PositiveHahnRoot k Γ G := by
  rcases exists_root_of_lowerEdge_affine_newton_edge_with_property
      (k := k) (Γ := Γ) h_main_mem h_main_value h_m_odd h_constant_on_line
      h_lower_positive h_lower_below_line h_higher_nonnegative
      (fun _ => True)
      (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)
      (fun _ _ => trivial)
      (fun hr hcluster => by
        rcases h_smaller_roots hr
            (KOddClusterHypothesesWithCoeffProperty.cluster
              (k := k) (Γ := Γ) hcluster) with ⟨y, hypos, hyroot⟩
        exact ⟨y, hypos, trivial, hyroot⟩) with
    ⟨y, hypos, _hyP, hyroot⟩
  exact ⟨y, hypos, hyroot⟩

private theorem lowerEdge_positiveHahnRoot_of_affine_newton_edge_of_obstruction
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (O : KSameMultiplicityLowerEdgeObstruction k Γ F m)
    (hrootBelow : KOddClusterRootBelow k Γ m) :
    PositiveHahnRoot k Γ F := by
  let _ : Nontrivial Γ := nontrivial_of_ne (0 : Γ) O.delta (ne_of_lt O.delta_pos)
  let H : Polynomial (valuationSubring k Γ) :=
    O.liftData.lift.comp (Polynomial.X + Polynomial.C O.source)
  let G : Polynomial (HahnField k Γ) :=
    H.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))
  have hunitH : IsUnit (H.coeff m) :=
    isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal
      k Γ O.liftData.unit O.source_mem
  have hcoeff (i : ℕ) :
      G.coeff i = (H.coeff i : HahnField k Γ) := by
    dsimp [G, H]
    exact coeff_map_comp_X_add_C k Γ O.liftData.lift O.source i
  have hGm : G.coeff m ≠ 0 := by
    rw [hcoeff m]
    intro hzero
    apply hunitH.ne_zero
    apply Subtype.ext
    exact hzero
  have hmain : m ∈ G.support := by
    rw [Polynomial.mem_support_iff]
    exact hGm
  have hmainval : addVal k Γ (G.coeff m) = 0 := by
    rw [hcoeff m]
    exact addVal_coeff_eq_zero_of_isUnit k Γ hunitH
  have htop : coeffValueOfMemSupport k Γ G hmain = 0 := by
    have hval' := hmainval
    rw [addVal_coeff_eq_coeffValueOfMemSupport k Γ G hmain] at hval'
    exact WithTop.coe_eq_coe.mp (by simpa using hval')
  have hzero :
      newtonWeight k Γ G O.delta 0 = ((m • O.delta : Γ) : WithTop Γ) := by
    have heval : newtonWeight k Γ G O.delta 0 = (O.gamma : WithTop Γ) := by
      have hcoeff0 :
          G.coeff 0 = ((O.liftData.lift.eval O.source : valuationSubring k Γ) :
            HahnField k Γ) := by
        dsimp [G, H]
        exact coeff_zero_map_comp_X_add_C k Γ O.liftData.lift O.source
      rw [newtonWeight, hcoeff0, O.eval_eq]
      simp
    simpa [O.scale] using heval
  have hlower_pos : ∀ i, i < m → (hisupp : i ∈ G.support) →
      0 < coeffValueOfMemSupport k Γ G hisupp := by
    intro i hi hisupp
    have hmem : H.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
      (O.liftData.translatedCluster k Γ O.source_mem).1 i hi
    have hpos : (0 : WithTop Γ) < addVal k Γ (G.coeff i) := by
      rw [hcoeff i]
      exact (mem_maximalIdeal_iff_pos_addVal k Γ (H.coeff i)).mp hmem
    rw [addVal_coeff_eq_coeffValueOfMemSupport k Γ G hisupp] at hpos
    exact WithTop.coe_lt_coe.mp hpos
  have hbelow :
      ∃ j, j < m ∧ j ∈ G.support ∧
        newtonWeight k Γ G O.delta j < (m • O.delta : Γ) := by
    have hcoeff_ne : H.coeff O.index ≠ 0 := by
      intro hzero
      have hbelow' := O.below
      have hzeroVal :
          addVal k Γ (H.coeff O.index : HahnField k Γ) = ⊤ := by
        rw [hzero]
        exact (addVal k Γ).map_zero
      rw [hzeroVal] at hbelow'
      exact not_top_lt hbelow'
    have hindex_support : O.index ∈ G.support := by
      rw [Polynomial.mem_support_iff]
      rw [hcoeff O.index]
      intro hzero
      apply hcoeff_ne
      apply Subtype.ext
      exact hzero
    refine ⟨O.index, O.index_lt, hindex_support, ?_⟩
    rw [newtonWeight, hcoeff O.index]
    let η : Γ :=
      (addVal k Γ (H.coeff O.index : HahnField k Γ)).untop
        (by simpa [AddValuation.ne_top_iff] using hcoeff_ne)
    have hη :
        addVal k Γ (H.coeff O.index : HahnField k Γ) = (η : WithTop Γ) := by
      dsimp [η]
      exact (WithTop.coe_untop _ _).symm
    have hbelowH :
        addVal k Γ (H.coeff O.index : HahnField k Γ) <
          (((m - O.index) • O.delta : Γ) : WithTop Γ) := by
      simpa [H] using O.below
    have hηlt : η < (m - O.index) • O.delta := by
      exact WithTop.coe_lt_coe.mp (by simpa [hη] using hbelowH)
    have hsumΓ :
        η + O.index • O.delta <
          (m - O.index) • O.delta + O.index • O.delta :=
      add_lt_add_left hηlt _
    have hsum :
        addVal k Γ (H.coeff O.index : HahnField k Γ) +
            O.index • (O.delta : WithTop Γ) <
          (((m - O.index) • O.delta : Γ) : WithTop Γ) +
            O.index • (O.delta : WithTop Γ) := by
      rw [hη]
      exact WithTop.coe_lt_coe.mpr (by
        simpa [WithTop.coe_add, WithTop.coe_nsmul] using hsumΓ)
    calc
      addVal k Γ (H.coeff O.index : HahnField k Γ) +
          O.index • (O.delta : WithTop Γ) <
          (((m - O.index) • O.delta : Γ) : WithTop Γ) +
            O.index • (O.delta : WithTop Γ) := hsum
      _ = ((m • O.delta : Γ) : WithTop Γ) := by
        have hsplit :
            (m - O.index) • O.delta + O.index • O.delta = m • O.delta := by
          rw [← add_nsmul, Nat.sub_add_cancel O.index_lt.le]
        calc
          (((m - O.index) • O.delta : Γ) : WithTop Γ) +
              O.index • (O.delta : WithTop Γ) =
              (((m - O.index) • O.delta : Γ) : WithTop Γ) +
                ((O.index • O.delta : Γ) : WithTop Γ) := by
                  simp only [WithTop.coe_nsmul]
          _ = (((m - O.index) • O.delta + O.index • O.delta : Γ) : WithTop Γ) := by
                rw [WithTop.coe_add]
          _ = ((m • O.delta : Γ) : WithTop Γ) := by rw [hsplit]
  have hnonneg : ∀ i, m < i → (hisupp : i ∈ G.support) →
      0 ≤ coeffValueOfMemSupport k Γ G hisupp := by
    intro i _ hisupp
    have hnonneg' : (0 : WithTop Γ) ≤ addVal k Γ (G.coeff i) := by
      rw [hcoeff i]
      exact (H.coeff i).property
    rw [addVal_coeff_eq_coeffValueOfMemSupport k Γ G hisupp] at hnonneg'
    exact WithTop.coe_le_coe.mp hnonneg'
  have hrootG : PositiveHahnRoot k Γ G :=
    positiveHahnRoot_of_lowerNewtonEdge (k := k) (Γ := Γ)
      hmain htop (KOddClusterHypotheses.odd k Γ O.branch.2.1)
      hzero hlower_pos hbelow hnonneg hrootBelow
  rcases hrootG with ⟨x, hxpos, hxroot⟩
  let z : valuationSubring k Γ := ⟨x, le_of_lt hxpos⟩
  have hzmem : z ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
    (mem_maximalIdeal_iff_pos_addVal k Γ z).mpr (by simpa [z] using hxpos)
  have hsum_mem : z + O.source ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
    (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem hzmem O.source_mem
  have hsum_pos :
      (0 : WithTop Γ) <
        addVal k Γ ((z + O.source : valuationSubring k Γ) : HahnField k Γ) :=
    (mem_maximalIdeal_iff_pos_addVal k Γ (z + O.source)).mp hsum_mem
  have hzroot : G.IsRoot (z : HahnField k Γ) := hxroot
  have hroot_lift :
      (O.liftData.lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).IsRoot
        ((z + O.source : valuationSubring k Γ) : HahnField k Γ) := by
    rw [Polynomial.IsRoot] at hzroot ⊢
    rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) H z] at hzroot
    rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ)
      O.liftData.lift (z + O.source)]
    rw [eval_comp_X_add_C] at hzroot
    exact hzroot
  refine ⟨((z + O.source : valuationSubring k Γ) : HahnField k Γ), hsum_pos, ?_⟩
  simpa [O.liftData.map_eq] using hroot_lift

/-- Lower-edge resolution with the multiplicity-induction input explicit. -/
def KSameMultiplicityLowerEdgeResolutionWithRootBelow
    [IsRealClosed k] [DivisibleBy Γ ℕ] : Prop :=
  ∀ {F : Polynomial (HahnField k Γ)} {m : ℕ},
    KOddClusterRootBelow k Γ m →
      Nonempty (KSameMultiplicityLowerEdgeObstruction k Γ F m) →
        PositiveHahnRoot k Γ F

theorem kSameMultiplicityLowerEdgeResolutionWithRootBelow_of_affineNewtonEdge
    [IsRealClosed k] [DivisibleBy Γ ℕ] :
    KSameMultiplicityLowerEdgeResolutionWithRootBelow k Γ := by
  intro F m hrootBelow hO
  rcases hO with ⟨O⟩
  exact lowerEdge_positiveHahnRoot_of_affine_newton_edge_of_obstruction
    k Γ O hrootBelow

/-- The source-level Newton step needed in the non-below edge case.  This is the intended
replacement for the older strict current-slope condition: equality on the current edge is allowed
and should be handled by the Newton initial polynomial. -/
def KSameMultiplicityEdgeStepHypothesis
    [IsRealClosed k] [DivisibleBy Γ ℕ] : Prop :=
  ∀ {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (_branch : KTranslatedSameMultiplicityZeroBranch k Γ F m)
    (D : KOddClusterLiftData k Γ F m)
    (A : valuationSubring k Γ)
    (_hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    {γ δ : Γ},
      addVal k Γ ((D.lift.eval A : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ) →
      0 < δ → m • δ = γ →
      (∀ j, 0 < j → j < m →
        (((m - j) • δ : Γ) : WithTop Γ) ≤
          addVal k Γ
            ((D.lift.comp (Polynomial.X + Polynomial.C A)).coeff j : HahnField k Γ)) →
      PositiveHahnRoot k Γ F ∨
        ∃ A' : valuationSubring k Γ, OddClusterStep k Γ D.lift m A A'

theorem kSameMultiplicityEdgeStepHypothesis_of_newtonInitial
    [IsRealClosed k] [DivisibleBy Γ ℕ] :
    KSameMultiplicityEdgeStepHypothesis k Γ := by
  intro F m hbranch D A hA γ δ hval hδpos hscale hnotBelow
  right
  have hm_pos : 0 < m := KOddClusterHypotheses.pos k Γ hbranch.branch.1
  have hm_odd : Odd m := KOddClusterHypotheses.odd k Γ hbranch.branch.1
  have hγpos : 0 < γ := by
    rw [← hscale]
    exact nsmul_pos hδpos hm_pos.ne'
  have hunit' : IsUnit ((D.lift.comp (Polynomial.X + Polynomial.C A)).coeff m) :=
    isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal k Γ D.unit hA
  rcases
    exists_nonzero_root_odd_rootMultiplicity_newtonInitialPolynomial_map_comp_X_add_C_of_unit_scale
      k Γ (g := D.lift) (A := A) (m := m) (δ := δ) (γ := γ)
      hm_odd hval hδpos hunit' hscale with
    ⟨c, hc, hmulPos, _hmulOdd, _hmulLe⟩
  let p : Polynomial k :=
    newtonInitialPolynomial k Γ
      ((D.lift.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ
  have hcoeff0 : p.coeff 0 ≠ 0 := by
    dsimp [p]
    exact coeff_newtonInitialPolynomial_ne_zero_of_mem k Γ
      (zero_mem_newtonInitialSupport_map_comp_X_add_C_of_eval_addVal_eq k Γ hval)
  have hpne : p ≠ 0 := by
    intro hp
    exact hcoeff0 (by simp [p, hp])
  have hroot : p.IsRoot c := (Polynomial.rootMultiplicity_pos hpne).mp (by
    simpa [p] using hmulPos)
  have hge :
      ∀ i ∈ Finset.range ((D.lift.comp (Polynomial.X + Polynomial.C A)).natDegree + 1),
        (γ : WithTop Γ) ≤
          newtonWeight k Γ
            ((D.lift.comp (Polynomial.X + Polynomial.C A)).map
              (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ i := by
    intro i _hi
    exact newtonWeight_ge_map_comp_X_add_C_of_unit_scale_nonbelow
      k Γ hval hunit' hδpos hscale hnotBelow i
  exact exists_oddClusterStep_of_current_edge_initial_root
    k Γ hA hval hδpos hγpos hc hscale hge (by simpa [p] using hroot)

/-- Assemble the lower-edge and non-below Newton-edge resolutions into the root-or-step
boundary consumed by the fixed-chain construction. -/
theorem kSameMultiplicityRootOrStepWithRootBelow_of_edgeStep_lowerEdge
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hedge : KSameMultiplicityEdgeStepHypothesis k Γ)
    (hlower : KSameMultiplicityLowerEdgeResolutionWithRootBelow k Γ) :
    KSameMultiplicityRootOrStepWithRootBelow k Γ := by
  classical
  intro F m hbelowRoot hbranch
  rcases exists_KOddClusterLiftData k Γ hbranch.branch.1 with ⟨D⟩
  refine ⟨D, ?_⟩
  intro A hA
  by_cases hroot : D.lift.IsRoot A
  · left
    have hrootMax : RootInMaximalIdeal k Γ D.lift := ⟨A, hA, hroot⟩
    have hpos := RootInMaximalIdeal.positiveHahnRootInMap k Γ hrootMax
    simpa [PositiveHahnRootInMap, D.map_eq] using hpos
  · rcases exists_main_correction_improves_eval_at_of_cluster_with_value
        (k := k) (Γ := Γ) (F := D.lift) (m := m) (y := A)
        (KOddClusterHypotheses.pos k Γ hbranch.branch.1)
        (KOddClusterHypotheses.odd k Γ hbranch.branch.1)
        D.lower D.unit hA (by
          rwa [Polynomial.IsRoot] at hroot) with
      ⟨γ, δ, _c, hδpos, _hγpos, _hcne, hδ, hval, _hmain⟩
    by_cases hnotBelow : ∀ j, 0 < j → j < m →
        (((m - j) • δ : Γ) : WithTop Γ) ≤
          addVal k Γ
            ((D.lift.comp (Polynomial.X + Polynomial.C A)).coeff j : HahnField k Γ)
    · exact hedge hbranch D A hA hval hδpos hδ hnotBelow
    · left
      push Not at hnotBelow
      rcases hnotBelow with ⟨j, hjpos, hjm, hbelow⟩
      exact hlower hbelowRoot ⟨{
        branch := hbranch
        liftData := D
        source := A
        source_mem := hA
        gamma := γ
        delta := δ
        eval_eq := hval
        delta_pos := hδpos
        scale := hδ
        index := j
        index_pos := hjpos
        index_lt := hjm
        below := hbelow }⟩

end HahnField

end

end HahnKaplanskyRealClosedness
