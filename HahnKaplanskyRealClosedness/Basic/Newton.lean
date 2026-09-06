/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Basic.Cluster

/-!
# Local Hahn-Newton step estimates for cluster polynomials
-/

namespace HahnKaplanskyRealClosedness

open Polynomial
open HahnSeries

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- A unit of the valuation subring has valuation zero. -/
theorem addVal_eq_zero_of_isUnit (x : valuationSubring k Γ) (hx : IsUnit x) :
    addVal k Γ (x : HahnField k Γ) = 0 := by
  have hxnonneg : (0 : WithTop Γ) ≤ addVal k Γ (x : HahnField k Γ) := x.property
  by_contra hne
  have hpos : (0 : WithTop Γ) < addVal k Γ (x : HahnField k Γ) :=
    lt_of_le_of_ne hxnonneg (fun h => hne h.symm)
  exact (IsLocalRing.notMem_maximalIdeal.mpr hx)
    ((mem_maximalIdeal_iff_pos_addVal k Γ x).mpr hpos)

/-- For elements of the valuation subring, being a unit is equivalent to having valuation zero. -/
theorem isUnit_iff_addVal_eq_zero (x : valuationSubring k Γ) :
    IsUnit x ↔ addVal k Γ (x : HahnField k Γ) = 0 :=
  ⟨addVal_eq_zero_of_isUnit k Γ x, fun hx => isUnit_of_addVal_eq_zero k Γ hx⟩

/-- A coefficient in the maximal ideal has positive valuation. -/
theorem pos_addVal_coeff_of_mem_maximalIdeal {F : (valuationSubring k Γ)[X]} {i : ℕ}
    (hmem : F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    (0 : WithTop Γ) < addVal k Γ (F.coeff i : HahnField k Γ) :=
  (mem_maximalIdeal_iff_pos_addVal k Γ (F.coeff i)).mp hmem

/-- A unit coefficient has valuation zero. -/
theorem addVal_coeff_eq_zero_of_isUnit {F : (valuationSubring k Γ)[X]} {i : ℕ}
    (hunit : IsUnit (F.coeff i)) :
    addVal k Γ (F.coeff i : HahnField k Γ) = 0 :=
  addVal_eq_zero_of_isUnit k Γ (F.coeff i) hunit

/-- The low-degree part of a cluster polynomial has positive coefficient valuations. -/
theorem pos_addVal_coeff_of_cluster_lt {F : (valuationSubring k Γ)[X]} {m i : ℕ}
    (hsmall : ∀ j, j < m → F.coeff j ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hi : i < m) :
    (0 : WithTop Γ) < addVal k Γ (F.coeff i : HahnField k Γ) :=
  pos_addVal_coeff_of_mem_maximalIdeal k Γ (hsmall i hi)

/-- The constant coefficient of a positive cluster lies in the maximal ideal. -/
theorem coeff_zero_mem_maximalIdeal_of_cluster_pos {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hm : 0 < m) :
    F.coeff 0 ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  hsmall 0 hm

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If every summand has positive valuation, so does the finite sum. -/
theorem addVal_sum_pos_of_forall_pos {ι : Type*} {s : Finset ι}
    {f : ι → HahnField k Γ}
    (hf : ∀ i ∈ s, (0 : WithTop Γ) < addVal k Γ (f i)) :
    (0 : WithTop Γ) < addVal k Γ (∑ i ∈ s, f i) :=
  (addVal k Γ).map_lt_sum' (by simp) hf

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If every summand has valuation strictly above a finite bound, so does the finite sum. -/
theorem addVal_sum_gt_of_forall_gt {ι : Type*} {s : Finset ι}
    {f : ι → HahnField k Γ} {γ : Γ}
    (hf : ∀ i ∈ s, (γ : WithTop Γ) < addVal k Γ (f i)) :
    (γ : WithTop Γ) < addVal k Γ (∑ i ∈ s, f i) :=
  (addVal k Γ).map_lt_sum' (WithTop.coe_lt_top γ) hf

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If two Hahn-field elements both have valuation above a finite bound, so does their sum. -/
theorem addVal_add_gt_of_forall_gt {x y : HahnField k Γ} {γ : Γ}
    (hx : (γ : WithTop Γ) < addVal k Γ x) (hy : (γ : WithTop Γ) < addVal k Γ y) :
    (γ : WithTop Γ) < addVal k Γ (x + y) :=
  (addVal k Γ).map_lt_add hx hy

/-- A positive cluster maps the maximal ideal into itself. -/
theorem eval_mem_maximalIdeal_of_cluster_pos
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hm : 0 < m) (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    F.eval y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [Polynomial.eval_eq_sum_range]
  apply Ideal.sum_mem
  intro i _hi
  by_cases hi0 : i = 0
  · subst i
    simpa using coeff_zero_mem_maximalIdeal_of_cluster_pos k Γ hsmall hm
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    exact (IsLocalRing.maximalIdeal (valuationSubring k Γ)).mul_mem_left (F.coeff i)
      ((IsLocalRing.maximalIdeal (valuationSubring k Γ)).pow_mem_of_mem hy i hipos)

/-- A unit coefficient bounds the polynomial degree from below. -/
theorem le_natDegree_of_unit_coeff {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hunit : IsUnit (F.coeff m)) :
    m ≤ F.natDegree :=
  Polynomial.le_natDegree_of_ne_zero hunit.ne_zero

/-- A Hahn monomial of nonnegative exponent, viewed in the valuation subring. -/
def singleOfNonneg (γ : Γ) (c : k) (hγ : 0 ≤ γ) : valuationSubring k Γ :=
  ⟨toLex (HahnSeries.single γ c), by
    change (0 : WithTop Γ) ≤ addVal k Γ (toLex (HahnSeries.single γ c))
    by_cases hc : c = 0
    · subst c
      simp [HahnSeries.single_eq_zero]
    · rw [addVal_single_of_ne (k := k) (Γ := Γ) hc]
      simpa using hγ⟩

@[simp]
theorem singleOfNonneg_coe (γ : Γ) (c : k) (hγ : 0 ≤ γ) :
    (singleOfNonneg k Γ γ c hγ : HahnField k Γ) =
      toLex (HahnSeries.single γ c) :=
  rfl

/-- The valuation of a nonzero nonnegative Hahn monomial. -/
theorem addVal_singleOfNonneg_of_ne {γ : Γ} {c : k} (hγ : 0 ≤ γ) (hc : c ≠ 0) :
    addVal k Γ (singleOfNonneg k Γ γ c hγ : HahnField k Γ) = (γ : WithTop Γ) := by
  rw [singleOfNonneg_coe, addVal_single_of_ne (k := k) (Γ := Γ) hc]

/-- The valuation of a power of a nonzero nonnegative Hahn monomial. -/
theorem addVal_singleOfNonneg_pow_of_ne {γ : Γ} {c : k} (hγ : 0 ≤ γ) (hc : c ≠ 0)
    (n : ℕ) :
    addVal k Γ ((singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ n) =
      (n • γ : WithTop Γ) := by
  rw [AddValuation.map_pow, addVal_singleOfNonneg_of_ne (k := k) (Γ := Γ) hγ hc]

/-- The valuation of one summand after substituting a nonzero nonnegative Hahn monomial. -/
theorem addVal_coeff_mul_singleOfNonneg_pow_of_ne
    {F : (valuationSubring k Γ)[X]} {γ : Γ} {c : k}
    (hγ : 0 ≤ γ) (hc : c ≠ 0) (i : ℕ) :
    addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i) =
      addVal k Γ (F.coeff i : HahnField k Γ) + (i • γ : WithTop Γ) := by
  rw [AddValuation.map_mul, addVal_singleOfNonneg_pow_of_ne (k := k) (Γ := Γ) hγ hc]

/-- Every positive-degree summand has positive valuation after substituting a nonzero positive
exponent monomial. -/
theorem pos_addVal_coeff_mul_singleOfNonneg_pow_of_pos_index
    {F : (valuationSubring k Γ)[X]} {i : ℕ} {γ : Γ} {c : k}
    (hi : 0 < i) (hγ : 0 < γ) (hc : c ≠ 0) :
    (0 : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ γ c (le_of_lt hγ) : HahnField k Γ) ^ i) := by
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne (k := k) (Γ := Γ) (le_of_lt hγ) hc]
  have hcoeff : (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i : HahnField k Γ) :=
    (F.coeff i).property
  by_cases hzero : (F.coeff i : HahnField k Γ) = 0
  · simp [hzero]
  · let δ : Γ := (addVal k Γ (F.coeff i : HahnField k Γ)).untop
        (by simpa [AddValuation.ne_top_iff] using hzero)
    have hδ :
        addVal k Γ (F.coeff i : HahnField k Γ) = (δ : WithTop Γ) :=
      (WithTop.coe_untop _ _).symm
    have hδ_nonneg : 0 ≤ δ := by
      apply WithTop.coe_le_coe.mp
      simpa [hδ] using hcoeff
    rw [hδ, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    exact WithTop.coe_lt_coe.mpr (add_pos_of_nonneg_of_pos hδ_nonneg (nsmul_pos hγ hi.ne'))

/-- A lower cluster summand has positive valuation after substituting a nonzero nonnegative
Hahn monomial. -/
theorem pos_addVal_cluster_lower_summand_singleOfNonneg
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {γ : Γ} {c : k}
    (hsmall : ∀ j, j < m → F.coeff j ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hi : i < m) (hγ : 0 ≤ γ) (hc : c ≠ 0) :
    (0 : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
    (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i) := by
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne (k := k) (Γ := Γ) hγ hc]
  have hnonneg : (0 : WithTop Γ) ≤ (i • γ : WithTop Γ) := by
    exact_mod_cast (nsmul_nonneg hγ i)
  exact add_pos_of_pos_of_nonneg
    (pos_addVal_coeff_of_cluster_lt k Γ hsmall hi)
    hnonneg

/-- The main cluster summand has valuation `m • γ` after substituting a nonzero nonnegative
Hahn monomial. -/
theorem addVal_cluster_main_summand_singleOfNonneg
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {γ : Γ} {c : k}
    (hunit : IsUnit (F.coeff m)) (hγ : 0 ≤ γ) (hc : c ≠ 0) :
    addVal k Γ ((F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ m) =
      (m • γ : WithTop Γ) := by
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne (k := k) (Γ := Γ) hγ hc,
    addVal_coeff_eq_zero_of_isUnit k Γ hunit, zero_add]

/-- If the substituted exponent is chosen so that `m • δ = γ`, the main cluster summand has
valuation exactly `γ`. -/
theorem addVal_cluster_main_summand_singleOfNonneg_eq_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {δ γ : Γ} {c : k}
    (hunit : IsUnit (F.coeff m)) (hδ_nonneg : 0 ≤ δ) (hc : c ≠ 0)
    (hδ : m • δ = γ) :
    addVal k Γ ((F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m) =
      (γ : WithTop Γ) := by
  rw [addVal_cluster_main_summand_singleOfNonneg (k := k) (Γ := Γ)
    hunit hδ_nonneg hc]
  rw [← WithTop.coe_nsmul, hδ]

/-- The coefficient at the main valuation of the main cluster summand after monomial
substitution. -/
theorem coeff_cluster_main_summand_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {δ γ : Γ} {c : k}
    (hδ_nonneg : 0 ≤ δ) (hδ : m • δ = γ) :
    (ofLex ((F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m)).coeff γ =
      constantCoeffRingHom k Γ (F.coeff m) * c ^ m := by
  change ((ofLex (F.coeff m : HahnField k Γ)) *
      (HahnSeries.single δ c) ^ m).coeff γ =
    constantCoeffRingHom k Γ (F.coeff m) * c ^ m
  rw [HahnSeries.single_pow, hδ, HahnSeries.coeff_mul_single]
  simp [constantCoeffRingHom_apply]

/-- At the target valuation, adding the main correction changes the error coefficient by
`residue(F_m) * c^m`. -/
theorem coeff_error_add_cluster_main_summand_singleOfNonneg
    {e : valuationSubring k Γ} {F : (valuationSubring k Γ)[X]} {m : ℕ}
    {δ γ : Γ} {b c : k}
    (hecoeff : (ofLex (e : HahnField k Γ)).coeff γ = b)
    (hδ_nonneg : 0 ≤ δ) (hδ : m • δ = γ) :
    (ofLex ((e : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m)).coeff γ =
      b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m := by
  change ((ofLex (e : HahnField k Γ)) +
      ofLex ((F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m)).coeff γ =
    b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m
  rw [HahnSeries.coeff_add, hecoeff,
    coeff_cluster_main_summand_singleOfNonneg_of_nsmul_eq (k := k) (Γ := Γ)
      (F := F) (m := m) hδ_nonneg hδ]

/-- If the residue-side cancellation equation holds, the target coefficient of the corrected
leading error is zero. -/
theorem coeff_error_add_cluster_main_summand_singleOfNonneg_eq_zero
    {e : valuationSubring k Γ} {F : (valuationSubring k Γ)[X]} {m : ℕ}
    {δ γ : Γ} {b c : k}
    (hecoeff : (ofLex (e : HahnField k Γ)).coeff γ = b)
    (hδ_nonneg : 0 ≤ δ) (hδ : m • δ = γ)
    (hcancel : b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m = 0) :
    (ofLex ((e : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m)).coeff γ = 0 := by
  rw [coeff_error_add_cluster_main_summand_singleOfNonneg
    (k := k) (Γ := Γ) (F := F) (m := m) hecoeff hδ_nonneg hδ, hcancel]

/-- If the main correction coefficient cancels the leading error coefficient, then the valuation of
`error + main correction` strictly improves. -/
theorem lt_addVal_error_add_cluster_main_summand_singleOfNonneg
    {e : valuationSubring k Γ} {F : (valuationSubring k Γ)[X]} {m : ℕ}
    {δ γ : Γ} {b c : k}
    (heval : addVal k Γ (e : HahnField k Γ) = (γ : WithTop Γ))
    (hecoeff : (ofLex (e : HahnField k Γ)).coeff γ = b)
    (hunit : IsUnit (F.coeff m)) (hδ_nonneg : 0 ≤ δ) (hc : c ≠ 0)
    (hδ : m • δ = γ)
    (hcancel : b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m = 0) :
    (γ : WithTop Γ) <
      addVal k Γ ((e : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c hδ_nonneg : HahnField k Γ) ^ m) := by
  apply lt_addVal_of_le_addVal_of_coeff_eq_zero k Γ
  · apply le_addVal_add_of_le_addVal k Γ
    · exact le_of_eq heval.symm
    · exact le_of_eq (addVal_cluster_main_summand_singleOfNonneg_eq_of_nsmul_eq
        k Γ hunit hδ_nonneg hc hδ).symm
  · exact coeff_error_add_cluster_main_summand_singleOfNonneg_eq_zero
      k Γ hecoeff hδ_nonneg hδ hcancel

/-- Terms above the cluster degree have valuation strictly larger than the target value
`m • δ` when substituting a nonzero positive Hahn monomial of exponent `δ`. -/
theorem lt_addVal_cluster_high_summand_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ) (hmi : m < i) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne
    (k := k) (Γ := Γ) (le_of_lt hδpos) hc]
  rw [← hδ, ← WithTop.coe_nsmul]
  have hcoeff_nonneg :
      (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i : HahnField k Γ) :=
    (F.coeff i).property
  have hpow_lt : (m • δ : WithTop Γ) < (i • δ : WithTop Γ) := by
    exact_mod_cast nsmul_lt_nsmul_left hδpos hmi
  exact lt_of_lt_of_le hpow_lt (le_add_of_nonneg_left hcoeff_nonneg)

/-- Lower cluster terms are also above the target valuation when their coefficients are above the
corresponding first-slope bound. -/
theorem lt_addVal_cluster_lower_summand_singleOfNonneg_of_coeff_bound
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ) (hi : i < m)
    (hcoeff : (((m - i) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff i : HahnField k Γ)) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne
    (k := k) (Γ := Γ) (le_of_lt hδpos) hc]
  by_cases hzero : (F.coeff i : HahnField k Γ) = 0
  · simp [hzero]
  · let η : Γ := (addVal k Γ (F.coeff i : HahnField k Γ)).untop
        (by simpa [AddValuation.ne_top_iff] using hzero)
    have hη :
        addVal k Γ (F.coeff i : HahnField k Γ) = (η : WithTop Γ) :=
      (WithTop.coe_untop _ _).symm
    have hη_gt : (m - i) • δ < η := by
      apply WithTop.coe_lt_coe.mp
      simpa [hη] using hcoeff
    rw [hη, ← hδ, ← WithTop.coe_nsmul, ← WithTop.coe_add]
    apply WithTop.coe_lt_coe.mpr
    have hsplit : m • δ = (m - i) • δ + i • δ := by
      rw [← add_nsmul, Nat.sub_add_cancel hi.le]
    rw [hsplit]
    simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_right hη_gt (i • δ)

/-- Every non-main term is above the target valuation under the lower first-slope bounds. -/
theorem lt_addVal_cluster_nonmain_summand_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff j : HahnField k Γ))
    (hi : i ≠ m) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  rcases lt_or_gt_of_ne hi with him | hmi
  · exact lt_addVal_cluster_lower_summand_singleOfNonneg_of_coeff_bound
      k Γ hδpos hc hδ him (hlower i him)
  · exact lt_addVal_cluster_high_summand_singleOfNonneg_of_nsmul_eq
      k Γ hδpos hc hδ hmi

/-- Every non-constant, non-main term is above the target valuation under the positive-degree
lower first-slope bounds. The constant term is handled together with the current error. -/
theorem lt_addVal_cluster_nonconstant_nonmain_summand_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, 0 < j → j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff j : HahnField k Γ))
    (hi0 : i ≠ 0) (hi : i ≠ m) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  rcases lt_or_gt_of_ne hi with him | hmi
  · exact lt_addVal_cluster_lower_summand_singleOfNonneg_of_coeff_bound
      k Γ hδpos hc hδ him (hlower i (Nat.pos_of_ne_zero hi0) him)
  · exact lt_addVal_cluster_high_summand_singleOfNonneg_of_nsmul_eq
      k Γ hδpos hc hδ hmi

/-- A finite sum of non-constant, non-main cluster correction terms is above the target valuation
under the positive-degree lower first-slope bounds. -/
theorem lt_addVal_sum_cluster_nonconstant_nonmain_summands_singleOfNonneg_of_nsmul_eq
    {F : (valuationSubring k Γ)[X]} {s : Finset ℕ} {m : ℕ} {δ γ : Γ} {c : k}
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, 0 < j → j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff j : HahnField k Γ))
    (hs0 : ∀ i ∈ s, i ≠ 0) (hsm : ∀ i ∈ s, i ≠ m) :
    (γ : WithTop Γ) <
      addVal k Γ (∑ i ∈ s, (F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i) := by
  apply addVal_sum_gt_of_forall_gt k Γ
  intro i hi
  exact lt_addVal_cluster_nonconstant_nonmain_summand_singleOfNonneg_of_nsmul_eq
    k Γ hδpos hc hδ hlower (hs0 i hi) (hsm i hi)

/-- A nonzero Hahn monomial of positive exponent lies in the maximal ideal. -/
theorem singleOfNonneg_mem_maximalIdeal_of_pos {γ : Γ} {c : k}
    (hγ : 0 < γ) (hc : c ≠ 0) :
    singleOfNonneg k Γ γ c (le_of_lt hγ) ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [mem_maximalIdeal_iff_pos_addVal]
  rw [addVal_singleOfNonneg_of_ne (k := k) (Γ := Γ) (le_of_lt hγ) hc]
  simpa using hγ

/-- Adding a nonzero positive Hahn monomial to an element of the maximal ideal stays in the
maximal ideal. -/
theorem add_singleOfNonneg_mem_maximalIdeal_of_mem_of_pos
    {y : valuationSubring k Γ} {γ : Γ} {c : k}
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hγ : 0 < γ) (hc : c ≠ 0) :
    y + singleOfNonneg k Γ γ c (le_of_lt hγ) ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem hy
    (singleOfNonneg_mem_maximalIdeal_of_pos k Γ hγ hc)

/-- A Hahn monomial of positive exponent has zero residue. -/
theorem constantCoeffRingHom_singleOfNonneg_pos {γ : Γ} (hγ : 0 < γ) (c : k) :
    constantCoeffRingHom k Γ (singleOfNonneg k Γ γ c (le_of_lt hγ)) = 0 := by
  rw [constantCoeffRingHom_apply, singleOfNonneg_coe]
  change (HahnSeries.single γ c).coeff 0 = 0
  exact HahnSeries.coeff_single_of_ne (ne_of_lt hγ)

/-- Adding a positive-exponent Hahn monomial does not change the residue. -/
theorem constantCoeffRingHom_add_singleOfNonneg_pos
    (y : valuationSubring k Γ) {γ : Γ} (hγ : 0 < γ) (c : k) :
    constantCoeffRingHom k Γ (y + singleOfNonneg k Γ γ c (le_of_lt hγ)) =
      constantCoeffRingHom k Γ y := by
  rw [map_add, constantCoeffRingHom_singleOfNonneg_pos (k := k) (Γ := Γ) hγ c, add_zero]

/-- Taking the residue of a valuation-subring polynomial evaluation agrees with evaluating the
residue polynomial at the residue of the point. -/
theorem constantCoeffRingHom_eval_eq_eval_map
    (F : (valuationSubring k Γ)[X]) (y : valuationSubring k Γ) :
    constantCoeffRingHom k Γ (F.eval y) =
      (F.map (constantCoeffRingHom k Γ)).eval (constantCoeffRingHom k Γ y) :=
  (Polynomial.eval_map_apply
    (f := constantCoeffRingHom k Γ) (p := F) (x := y)).symm

/-- Evaluating over the valuation subring and then embedding into the Hahn field agrees with
evaluating the mapped polynomial over the Hahn field. -/
theorem eval_map_algebraMap_eq_coe_eval
    (F : (valuationSubring k Γ)[X]) (x : valuationSubring k Γ) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (x : HahnField k Γ) =
      ((F.eval x : valuationSubring k Γ) : HahnField k Γ) := by
  simpa only [Algebra.algebraMap_ofSubsemiring_apply] using Polynomial.eval_map_apply
    (f := algebraMap (valuationSubring k Γ) (HahnField k Γ)) (p := F) (x := x)

/-- Specialization of `eval_map_algebraMap_eq_coe_eval` to nonnegative Hahn monomials. -/
theorem eval_map_algebraMap_singleOfNonneg
    (F : (valuationSubring k Γ)[X]) {γ : Γ} (c : k) (hγ : 0 ≤ γ) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) =
      ((F.eval (singleOfNonneg k Γ γ c hγ) : valuationSubring k Γ) : HahnField k Γ) :=
  eval_map_algebraMap_eq_coe_eval k Γ F (singleOfNonneg k Γ γ c hγ)

/-- Finite-sum expansion of a valuation-subring polynomial evaluated after mapping to the Hahn
field. -/
theorem eval_map_algebraMap_eq_sum_range
    (F : (valuationSubring k Γ)[X]) (x : HahnField k Γ) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval x =
      ∑ i ∈ Finset.range (F.natDegree + 1),
        (F.coeff i : HahnField k Γ) * x ^ i := by
  rw [Polynomial.eval_eq_sum_range,
    Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap (valuationSubring k Γ) (HahnField k Γ)) from
        fun a b h => Subtype.ext h)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.coeff_map]
  change ((F.coeff i : valuationSubring k Γ) : HahnField k Γ) * x ^ i =
    ((F.coeff i : valuationSubring k Γ) : HahnField k Γ) * x ^ i
  rfl

/-- Finite-sum expansion after substituting a nonnegative Hahn monomial. -/
theorem eval_map_algebraMap_singleOfNonneg_eq_sum_range
    (F : (valuationSubring k Γ)[X]) {γ : Γ} (c : k) (hγ : 0 ≤ γ) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) =
      ∑ i ∈ Finset.range (F.natDegree + 1),
        (F.coeff i : HahnField k Γ) *
          (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i :=
  eval_map_algebraMap_eq_sum_range k Γ F (singleOfNonneg k Γ γ c hγ)

/-- Hahn-series expansion of a valuation-subring polynomial evaluated at a nonnegative Hahn
monomial.  This is the general `HahnField k Γ` form of the archived rational-Hahn
single-evaluation expansion. -/
theorem ofLex_eval_map_algebraMap_singleOfNonneg_eq_sum_range
    (F : (valuationSubring k Γ)[X]) {γ : Γ} (c : k) (hγ : 0 ≤ γ) :
    ofLex ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ)) =
      ∑ i ∈ Finset.range (F.natDegree + 1),
        ofLex (F.coeff i : HahnField k Γ) * HahnSeries.single (i • γ) (c ^ i) := by
  have h := congrArg (ofLexRingHom k Γ)
    (eval_map_algebraMap_singleOfNonneg_eq_sum_range k Γ F c hγ)
  simpa [ofLexRingHom_apply, singleOfNonneg_coe, HahnSeries.single_pow] using h

/-- Coefficient formula for evaluating a valuation-subring polynomial at a nonnegative Hahn
monomial.  The `i`-th summand contributes the coefficient of `m - i • γ` of the `i`-th
coefficient, multiplied by `c ^ i`. -/
theorem coeff_eval_map_algebraMap_singleOfNonneg_eq_sum_range
    (F : (valuationSubring k Γ)[X]) {γ : Γ} (m : Γ) (c : k) (hγ : 0 ≤ γ) :
    (ofLex ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ))).coeff m =
      ∑ i ∈ Finset.range (F.natDegree + 1),
        (ofLex (F.coeff i : HahnField k Γ)).coeff (m - i • γ) * c ^ i := by
  rw [ofLex_eval_map_algebraMap_singleOfNonneg_eq_sum_range]
  simp [HahnSeries.coeff_mul_single]

theorem coeff_substitution_summand_eq_zero_of_notMem_initialSupport_of_weight_ge
    (F : (valuationSubring k Γ)[X]) {δ μ : Γ} {i : ℕ}
    (hge :
      (μ : WithTop Γ) ≤
        newtonWeight k Γ
          (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ i)
    (hnot :
      i ∉ newtonInitialSupport k Γ
        (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ μ) :
    (ofLex (F.coeff i : HahnField k Γ)).coeff (μ - i • δ) = 0 := by
  let G : (HahnField k Γ)[X] :=
    F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))
  have hcoeffi : G.coeff i = (F.coeff i : HahnField k Γ) := by
    dsimp [G]
    rw [Polynomial.coeff_map]
    exact Algebra.algebraMap_ofSubsemiring_apply (valuationSubring k Γ) (F.coeff i)
  by_cases hisupp : i ∈ G.support
  · have hweight_ne : newtonWeight k Γ G δ i ≠ (μ : WithTop Γ) := by
      intro hweight
      exact hnot ((mem_newtonInitialSupport k Γ G δ μ).mpr ⟨hisupp, hweight⟩)
    have hgt : (μ : WithTop Γ) < newtonWeight k Γ G δ i :=
      lt_of_le_of_ne hge (fun hEq => hweight_ne hEq.symm)
    let η : Γ := coeffValueOfMemSupport k Γ G hisupp
    have hval : addVal k Γ (G.coeff i) = (η : WithTop Γ) :=
      addVal_coeff_eq_coeffValueOfMemSupport k Γ G hisupp
    have hweight_eq : newtonWeight k Γ G δ i = ((η + i • δ : Γ) : WithTop Γ) := by
      dsimp [η]
      rw [newtonWeight_eq_of_mem_support k Γ G δ hisupp]
      rfl
    have hgtΓ : μ < η + i • δ := by
      exact WithTop.coe_lt_coe.mp (by simpa [hweight_eq] using hgt)
    have hltΓ : μ - i • δ < η := by
      rw [sub_lt_iff_lt_add]
      simpa [add_comm, add_left_comm, add_assoc] using hgtΓ
    have hltTop : ((μ - i • δ : Γ) : WithTop Γ) < addVal k Γ (G.coeff i) := by
      rw [hval]
      exact_mod_cast hltΓ
    have hzero : (ofLex (G.coeff i)).coeff (μ - i • δ) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by simpa [addVal_apply] using hltTop)
    simpa [hcoeffi] using hzero
  · have hGzero : G.coeff i = 0 := Polynomial.notMem_support_iff.mp hisupp
    have hcoeff_zero : ((F.coeff i : valuationSubring k Γ) : HahnField k Γ) = 0 := by
      simpa [hcoeffi] using hGzero
    simp [hcoeff_zero]

theorem coeff_eval_map_singleOfNonneg_eq_newtonInitialPolynomial_eval_of_weight_ge
    (F : (valuationSubring k Γ)[X]) {δ μ : Γ} (c : k) (hδ : 0 ≤ δ)
    (hge :
      ∀ i ∈ Finset.range (F.natDegree + 1),
        (μ : WithTop Γ) ≤
          newtonWeight k Γ
            (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ i) :
    (ofLex ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ δ c hδ : HahnField k Γ))).coeff μ =
      (newtonInitialPolynomial k Γ
        (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ μ).eval c := by
  classical
  let G : (HahnField k Γ)[X] :=
    F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))
  let S : Finset ℕ := newtonInitialSupport k Γ G δ μ
  let R : Finset ℕ := Finset.range (F.natDegree + 1)
  have hGnat : G.natDegree = F.natDegree := by
    dsimp [G]
    exact Polynomial.natDegree_map_eq_of_injective
      (show Function.Injective (algebraMap (valuationSubring k Γ) (HahnField k Γ)) from
        fun a b h => Subtype.ext h)
      F
  have hSsubR : S ⊆ R := by
    intro i hi
    rcases (mem_newtonInitialSupport k Γ G δ μ).mp hi with ⟨hisupp, _hweight⟩
    have hle : i ≤ G.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hisupp)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa [R, hGnat] using hle))
  have hterm :
      ∀ i ∈ R,
        (ofLex (F.coeff i : HahnField k Γ)).coeff (μ - i • δ) * c ^ i =
          if hi : i ∈ S then newtonInitialCoeff k Γ G δ μ i * c ^ i else 0 := by
    intro i hiR
    by_cases hiS : i ∈ S
    · rw [dif_pos hiS, newtonInitialCoeff_of_mem k Γ G δ μ hiS]
      have hcoeffi : G.coeff i = (F.coeff i : HahnField k Γ) := by
        dsimp [G]
        rw [Polynomial.coeff_map]
        exact Algebra.algebraMap_ofSubsemiring_apply (valuationSubring k Γ) (F.coeff i)
      simp [hcoeffi]
    · rw [dif_neg hiS]
      have hzero :
          (ofLex (F.coeff i : HahnField k Γ)).coeff (μ - i • δ) = 0 :=
        coeff_substitution_summand_eq_zero_of_notMem_initialSupport_of_weight_ge
          k Γ F (hge i hiR) (by simpa [G, S] using hiS)
      simp [hzero]
  calc
    (ofLex ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ δ c hδ : HahnField k Γ))).coeff μ
        = ∑ i ∈ R, (ofLex (F.coeff i : HahnField k Γ)).coeff (μ - i • δ) * c ^ i := by
          dsimp [R]
          exact coeff_eval_map_algebraMap_singleOfNonneg_eq_sum_range k Γ F μ c hδ
    _ = ∑ i ∈ R, if hi : i ∈ S then newtonInitialCoeff k Γ G δ μ i * c ^ i else 0 := by
          exact Finset.sum_congr rfl hterm
    _ = ∑ i ∈ R.filter (fun i => i ∈ S), newtonInitialCoeff k Γ G δ μ i * c ^ i := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i hiR
          by_cases hiS : i ∈ S <;> simp [hiS]
    _ = ∑ i ∈ S, newtonInitialCoeff k Γ G δ μ i * c ^ i := by
          have hfilter : R.filter (fun i => i ∈ S) = S := by
            ext i
            constructor
            · intro hi
              exact (Finset.mem_filter.mp hi).2
            · intro hi
              exact Finset.mem_filter.mpr ⟨hSsubR hi, hi⟩
          rw [hfilter]
    _ = (newtonInitialPolynomial k Γ G δ μ).eval c := by
          rw [newtonInitialPolynomial, Polynomial.eval_finsetSum]
          apply Finset.sum_congr rfl
          intro i hiS
          rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- If all substituted Newton weights are at least `μ`, then the substituted evaluation has
valuation at least `μ`. -/
theorem le_addVal_eval_map_singleOfNonneg_of_weight_ge
    (F : (valuationSubring k Γ)[X]) {δ μ : Γ} (c : k) (hδ : 0 ≤ δ) (hc : c ≠ 0)
    (hge :
      ∀ i ∈ Finset.range (F.natDegree + 1),
        (μ : WithTop Γ) ≤
          newtonWeight k Γ
            (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ i) :
    (μ : WithTop Γ) ≤
      addVal k Γ ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ δ c hδ : HahnField k Γ)) := by
  rw [eval_map_algebraMap_singleOfNonneg_eq_sum_range]
  refine (addVal k Γ).map_le_sum ?_
  intro i hi
  rw [addVal_coeff_mul_singleOfNonneg_pow_of_ne (k := k) (Γ := Γ) hδ hc]
  have hcoeffi :
      (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).coeff i =
        (F.coeff i : HahnField k Γ) := by
    rw [Polynomial.coeff_map]
    exact Algebra.algebraMap_ofSubsemiring_apply (valuationSubring k Γ) (F.coeff i)
  simpa [newtonWeight, hcoeffi, ← WithTop.coe_nsmul] using hge i hi

/-- If the current Newton initial polynomial vanishes at the substituted coefficient and all
weights are at least `μ`, then the substituted evaluation improves past `μ`. -/
theorem lt_addVal_eval_map_singleOfNonneg_of_newtonInitialPolynomial_root
    (F : (valuationSubring k Γ)[X]) {δ μ : Γ} {c : k}
    (hδ : 0 ≤ δ) (hc : c ≠ 0)
    (hge :
      ∀ i ∈ Finset.range (F.natDegree + 1),
        (μ : WithTop Γ) ≤
          newtonWeight k Γ
            (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ i)
    (hroot :
      (newtonInitialPolynomial k Γ
        (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ μ).IsRoot c) :
    (μ : WithTop Γ) <
      addVal k Γ ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ δ c hδ : HahnField k Γ)) := by
  apply lt_addVal_of_le_addVal_of_coeff_eq_zero k Γ
  · exact le_addVal_eval_map_singleOfNonneg_of_weight_ge k Γ F c hδ hc hge
  · rw [coeff_eval_map_singleOfNonneg_eq_newtonInitialPolynomial_eval_of_weight_ge
      k Γ F c hδ hge]
    simpa [Polynomial.IsRoot] using hroot

/-- Translated form of
`lt_addVal_eval_map_singleOfNonneg_of_newtonInitialPolynomial_root`.  A root of the current
Newton initial polynomial for `F(X + y)` makes the corrected approximation improve past `μ`. -/
theorem lt_addVal_eval_add_singleOfNonneg_of_newtonInitialPolynomial_root
    (F : (valuationSubring k Γ)[X]) (y : valuationSubring k Γ) {δ μ : Γ} {c : k}
    (hδ : 0 ≤ δ) (hc : c ≠ 0)
    (hge :
      ∀ i ∈ Finset.range ((F.comp (Polynomial.X + Polynomial.C y)).natDegree + 1),
        (μ : WithTop Γ) ≤
          newtonWeight k Γ
            ((F.comp (Polynomial.X + Polynomial.C y)).map
              (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ i)
    (hroot :
      (newtonInitialPolynomial k Γ
        ((F.comp (Polynomial.X + Polynomial.C y)).map
          (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ μ).IsRoot c) :
    (μ : WithTop Γ) <
      addVal k Γ (((F.eval (singleOfNonneg k Γ δ c hδ + y) : valuationSubring k Γ) :
        HahnField k Γ)) := by
  let G : (valuationSubring k Γ)[X] := F.comp (Polynomial.X + Polynomial.C y)
  let t : valuationSubring k Γ := singleOfNonneg k Γ δ c hδ
  have hG : (μ : WithTop Γ) <
      addVal k Γ ((G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (t : HahnField k Γ)) := by
    dsimp [G, t]
    exact lt_addVal_eval_map_singleOfNonneg_of_newtonInitialPolynomial_root
      k Γ (F.comp (Polynomial.X + Polynomial.C y)) hδ hc hge hroot
  have hmap :
      (G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (t : HahnField k Γ) =
        ((G.eval t : valuationSubring k Γ) : HahnField k Γ) :=
    eval_map_algebraMap_eq_coe_eval k Γ G t
  have htranslate : G.eval t = F.eval (t + y) := by
    dsimp [G, t]
    simp [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [hmap, htranslate] at hG
  simpa [t] using hG

/-- Split a monomial substitution evaluation into its constant term, the degree-`m` summand, and
the remaining summands. -/
theorem eval_map_algebraMap_singleOfNonneg_eq_const_add_main_add_nonmain
    (F : (valuationSubring k Γ)[X]) {m : ℕ} {γ : Γ} (c : k) (hγ : 0 ≤ γ)
    (hm_pos : 0 < m) (hmdeg : m ≤ F.natDegree) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ) =
      (F.coeff 0 : HahnField k Γ) +
        ((F.coeff m : HahnField k Γ) *
            (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ m +
          ∑ i ∈ ((Finset.range (F.natDegree + 1)).erase 0).erase m,
            (F.coeff i : HahnField k Γ) *
              (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i) := by
  let s : Finset ℕ := Finset.range (F.natDegree + 1)
  let t : valuationSubring k Γ := singleOfNonneg k Γ γ c hγ
  let f : ℕ → HahnField k Γ := fun i => (F.coeff i : HahnField k Γ) * (t : HahnField k Γ) ^ i
  have h0mem : 0 ∈ s := by
    dsimp [s]
    exact Finset.mem_range.mpr (Nat.succ_pos _)
  have hmmem : m ∈ s.erase 0 := by
    rw [Finset.mem_erase]
    exact ⟨hm_pos.ne', by
      dsimp [s]
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmdeg)⟩
  calc
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c hγ : HahnField k Γ)
        = ∑ i ∈ s, f i := by
          dsimp [s, f, t]
          exact eval_map_algebraMap_singleOfNonneg_eq_sum_range k Γ F c hγ
    _ = f 0 + ∑ i ∈ s.erase 0, f i := by
          exact (Finset.add_sum_erase s f h0mem).symm
    _ = f 0 + (f m + ∑ i ∈ (s.erase 0).erase m, f i) := by
          rw [(Finset.add_sum_erase (s.erase 0) f hmmem).symm]
    _ = (F.coeff 0 : HahnField k Γ) +
        ((F.coeff m : HahnField k Γ) *
            (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ m +
          ∑ i ∈ ((Finset.range (F.natDegree + 1)).erase 0).erase m,
            (F.coeff i : HahnField k Γ) *
              (singleOfNonneg k Γ γ c hγ : HahnField k Γ) ^ i) := by
          simp [s, f, t]

/-- If the constant term plus the main correction improves, and every other correction term is
above the target valuation, then the whole monomial-substitution evaluation improves. -/
theorem lt_addVal_eval_map_singleOfNonneg_of_const_main_improves
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {δ γ : Γ} {c : k}
    (hm_pos : 0 < m) (hunit : IsUnit (F.coeff m))
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, 0 < j → j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ (F.coeff j : HahnField k Γ))
    (hmain : (γ : WithTop Γ) <
      addVal k Γ ((F.coeff 0 : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m)) :
    (γ : WithTop Γ) <
      addVal k Γ ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ)) := by
  let rest : HahnField k Γ :=
    ∑ i ∈ ((Finset.range (F.natDegree + 1)).erase 0).erase m,
      (F.coeff i : HahnField k Γ) *
        (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ i
  have hrest : (γ : WithTop Γ) < addVal k Γ rest := by
    dsimp [rest]
    exact lt_addVal_sum_cluster_nonconstant_nonmain_summands_singleOfNonneg_of_nsmul_eq
      k Γ hδpos hc hδ hlower
      (by
        intro i hi
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1)
      (by
        intro i hi
        exact (Finset.mem_erase.mp hi).1)
  have heval :
      (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) =
        (F.coeff 0 : HahnField k Γ) +
          ((F.coeff m : HahnField k Γ) *
              (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m + rest) := by
    dsimp [rest]
    exact eval_map_algebraMap_singleOfNonneg_eq_const_add_main_add_nonmain
      k Γ F c (le_of_lt hδpos) hm_pos (le_natDegree_of_unit_coeff k Γ hunit)
  rw [heval, ← add_assoc]
  exact addVal_add_gt_of_forall_gt k Γ hmain hrest

/-- A positive cluster evaluates to positive valuation after substituting a nonzero positive
exponent Hahn monomial. -/
theorem pos_addVal_eval_map_algebraMap_singleOfNonneg_of_cluster_pos
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {γ : Γ} {c : k}
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hm : 0 < m) (hγ : 0 < γ) (hc : c ≠ 0) :
    (0 : WithTop Γ) <
      addVal k Γ ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (singleOfNonneg k Γ γ c (le_of_lt hγ) : HahnField k Γ)) := by
  rw [eval_map_algebraMap_singleOfNonneg_eq_sum_range]
  apply addVal_sum_pos_of_forall_pos
  intro i hi
  by_cases him : i < m
  · exact pos_addVal_cluster_lower_summand_singleOfNonneg k Γ
      (F := F) (m := m) (i := i) hsmall him (le_of_lt hγ) hc
  · have hmi : m ≤ i := le_of_not_gt him
    have hi_pos : 0 < i := lt_of_lt_of_le hm hmi
    exact pos_addVal_coeff_mul_singleOfNonneg_pow_of_pos_index k Γ
      (F := F) (i := i) hi_pos hγ hc

/-- A unit in the valuation subring has nonzero residue. -/
theorem constantCoeffRingHom_ne_zero_of_isUnit {x : valuationSubring k Γ} (hx : IsUnit x) :
    constantCoeffRingHom k Γ x ≠ 0 := by
  intro hzero
  have hmem : x ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
    rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ), RingHom.mem_ker]
    exact hzero
  exact (IsLocalRing.notMem_maximalIdeal.mpr hx) hmem

/-- A coefficient whose residue is zero lies in the maximal ideal. -/
theorem coeff_mem_maximalIdeal_of_map_constantCoeff_coeff_eq_zero
    {g : (valuationSubring k Γ)[X]} {n : ℕ}
    (h : (g.map (constantCoeffRingHom k Γ)).coeff n = 0) :
    g.coeff n ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ), RingHom.mem_ker]
  simpa [Polynomial.coeff_map] using h

/-- A coefficient with nonzero residue is a unit. -/
theorem isUnit_coeff_of_map_constantCoeff_coeff_ne_zero
    {g : (valuationSubring k Γ)[X]} {n : ℕ}
    (h : (g.map (constantCoeffRingHom k Γ)).coeff n ≠ 0) :
    IsUnit (g.coeff n) := by
  apply isUnit_of_constantCoeffRingHom_ne_zero k Γ
  simpa [Polynomial.coeff_map] using h

/-- A unit coefficient remains nonzero in the residue polynomial. -/
theorem coeff_map_constantCoeff_ne_zero_of_unit_coeff {g : (valuationSubring k Γ)[X]}
    {n : ℕ} (hunit : IsUnit (g.coeff n)) :
    (g.map (constantCoeffRingHom k Γ)).coeff n ≠ 0 := by
  rw [Polynomial.coeff_map]
  exact constantCoeffRingHom_ne_zero_of_isUnit k Γ hunit

/-- Lower cluster coefficients vanish in the residue polynomial. -/
theorem coeff_map_constantCoeff_eq_zero_of_cluster_lt
    {F : (valuationSubring k Γ)[X]} {m i : ℕ}
    (hsmall : ∀ j, j < m → F.coeff j ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hi : i < m) :
    (F.map (constantCoeffRingHom k Γ)).coeff i = 0 := by
  rw [Polynomial.coeff_map]
  have hmem := hsmall i hi
  rwa [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ), RingHom.mem_ker] at hmem

/-- The main cluster coefficient is nonzero in the residue polynomial. -/
theorem coeff_map_constantCoeff_ne_zero_of_cluster_unit
    {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hunit : IsUnit (F.coeff m)) :
    (F.map (constantCoeffRingHom k Γ)).coeff m ≠ 0 :=
  coeff_map_constantCoeff_ne_zero_of_unit_coeff k Γ hunit

/-- If the target is nonzero, the cluster main coefficient can cancel it with a nonzero odd-power
coefficient. -/
theorem exists_nonzero_cancel_cluster_main_residue_pow_of_odd
    [IsRealClosed k] {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hm : Odd m) (hunit : IsUnit (F.coeff m)) {b : k} (hb : b ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ b + constantCoeffRingHom k Γ (F.coeff m) * c ^ m = 0 :=
  exists_nonzero_cancel_add_mul_pow_of_odd hm
    (constantCoeffRingHom_ne_zero_of_isUnit k Γ hunit) hb

/-- Given a nonzero maximal-ideal error, choose a Hahn monomial main correction together with the
exact valuation of the current error and a strict improvement after correction. -/
theorem exists_main_correction_improves_error_with_value
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {e : valuationSubring k Γ} {F : (valuationSubring k Γ)[X]} {m : ℕ}
    (hm_pos : 0 < m) (hm_odd : Odd m) (hunit : IsUnit (F.coeff m))
    (hemem : e ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hene : e ≠ 0) :
    ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
      ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ m • δ = γ ∧
        addVal k Γ (e : HahnField k Γ) = (γ : WithTop Γ) ∧
          (γ : WithTop Γ) <
            addVal k Γ ((e : HahnField k Γ) + (F.coeff m : HahnField k Γ) *
              (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m) := by
  rcases exists_pos_addVal_leading_coeff_of_mem_maximalIdeal k Γ hemem hene with
    ⟨γ, b, hγpos, hbne, heval, hecoeff⟩
  rcases exists_pos_nsmul_eq (Γ := Γ) hm_pos hγpos with ⟨δ, hδpos, hδ⟩
  rcases exists_nonzero_cancel_cluster_main_residue_pow_of_odd k Γ hm_odd hunit hbne with
    ⟨c, hcne, hcancel⟩
  refine ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, heval, ?_⟩
  exact lt_addVal_error_add_cluster_main_summand_singleOfNonneg
    k Γ heval hecoeff hunit (le_of_lt hδpos) hcne hδ hcancel

/-- Translating a valuation-subring polynomial commutes with passing to the residue polynomial. -/
theorem map_constantCoeff_comp_X_add_C {g : (valuationSubring k Γ)[X]}
    (A : valuationSubring k Γ) :
    ((g.comp (Polynomial.X + Polynomial.C A)).map (constantCoeffRingHom k Γ)) =
      (g.map (constantCoeffRingHom k Γ)).comp
        (Polynomial.X + Polynomial.C (constantCoeffRingHom k Γ A)) := by
  rw [Polynomial.map_comp]
  simp

/-- Coefficient form of `map_constantCoeff_comp_X_add_C`. -/
theorem coeff_map_constantCoeff_comp_X_add_C {g : (valuationSubring k Γ)[X]}
    (A : valuationSubring k Γ) (n : ℕ) :
    ((g.comp (Polynomial.X + Polynomial.C A)).map (constantCoeffRingHom k Γ)).coeff n =
      ((g.map (constantCoeffRingHom k Γ)).comp
        (Polynomial.X + Polynomial.C (constantCoeffRingHom k Γ A))).coeff n := by
  rw [map_constantCoeff_comp_X_add_C]

/-- A root of the translated polynomial `g(X + A)` gives a root of `g`. -/
theorem isRoot_add_of_isRoot_comp_X_add_C
    {g : (valuationSubring k Γ)[X]} {A y : valuationSubring k Γ}
    (hroot : (g.comp (Polynomial.X + Polynomial.C A)).IsRoot y) :
    g.IsRoot (y + A) := by
  rw [Polynomial.IsRoot] at hroot ⊢
  simpa [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    using hroot

/-- Evaluating the translated polynomial `g(X + A)` at `y` is evaluating `g` at `y + A`. -/
theorem eval_comp_X_add_C
    (g : (valuationSubring k Γ)[X]) (A y : valuationSubring k Γ) :
    (g.comp (Polynomial.X + Polynomial.C A)).eval y = g.eval (y + A) := by
  simp [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

theorem coeff_zero_map_comp_X_add_C
    (g : (valuationSubring k Γ)[X]) (A : valuationSubring k Γ) :
    ((g.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))).coeff 0 =
      ((g.eval A : valuationSubring k Γ) : HahnField k Γ) := by
  rw [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, eval_comp_X_add_C]
  simpa using Algebra.algebraMap_ofSubsemiring_apply (valuationSubring k Γ) (g.eval A)

theorem coeff_map_comp_X_add_C
    (g : (valuationSubring k Γ)[X]) (A : valuationSubring k Γ) (i : ℕ) :
    ((g.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))).coeff i =
      (((g.comp (Polynomial.X + Polynomial.C A)).coeff i : valuationSubring k Γ) :
        HahnField k Γ) := by
  rw [Polynomial.coeff_map]
  exact Algebra.algebraMap_ofSubsemiring_apply (valuationSubring k Γ)
    ((g.comp (Polynomial.X + Polynomial.C A)).coeff i)

theorem zero_mem_newtonInitialSupport_map_comp_X_add_C_of_eval_addVal_eq
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {δ γ : Γ}
    (hval :
      addVal k Γ ((g.eval A : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ)) :
    0 ∈ newtonInitialSupport k Γ
      ((g.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ := by
  let G : (HahnField k Γ)[X] :=
    (g.comp (Polynomial.X + Polynomial.C A)).map
      (algebraMap (valuationSubring k Γ) (HahnField k Γ))
  have hcoeff0 :
      G.coeff 0 = ((g.eval A : valuationSubring k Γ) : HahnField k Γ) := by
    dsimp [G]
    exact coeff_zero_map_comp_X_add_C k Γ g A
  rw [mem_newtonInitialSupport]
  constructor
  · rw [Polynomial.mem_support_iff]
    intro hzero
    have htop : addVal k Γ ((g.eval A : valuationSubring k Γ) : HahnField k Γ) = ⊤ := by
      rw [← hcoeff0, hzero, AddValuation.map_zero]
    rw [hval] at htop
    exact (WithTop.coe_ne_top : ((γ : Γ) : WithTop Γ) ≠ ⊤) htop
  · rw [newtonWeight, hcoeff0, hval]
    simp

theorem main_mem_newtonInitialSupport_map_comp_X_add_C_of_unit_scale
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ} {δ γ : Γ}
    (hunit : IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m))
    (hscale : m • δ = γ) :
    m ∈ newtonInitialSupport k Γ
      ((g.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ := by
  let G : (HahnField k Γ)[X] :=
    (g.comp (Polynomial.X + Polynomial.C A)).map
      (algebraMap (valuationSubring k Γ) (HahnField k Γ))
  have hcoeffm :
      G.coeff m =
        (((g.comp (Polynomial.X + Polynomial.C A)).coeff m : valuationSubring k Γ) :
          HahnField k Γ) := by
    dsimp [G]
    exact coeff_map_comp_X_add_C k Γ g A m
  rw [mem_newtonInitialSupport]
  constructor
  · rw [Polynomial.mem_support_iff]
    intro hzero
    have htop :
        addVal k Γ
            ((((g.comp (Polynomial.X + Polynomial.C A)).coeff m : valuationSubring k Γ) :
              HahnField k Γ)) =
          ⊤ := by
      rw [← hcoeffm, hzero, AddValuation.map_zero]
    have hzeroVal :
        addVal k Γ
            ((((g.comp (Polynomial.X + Polynomial.C A)).coeff m : valuationSubring k Γ) :
              HahnField k Γ)) =
          (0 : WithTop Γ) :=
      addVal_eq_zero_of_isUnit k Γ ((g.comp (Polynomial.X + Polynomial.C A)).coeff m)
        hunit
    rw [hzeroVal] at htop
    exact (WithTop.coe_ne_top : ((0 : Γ) : WithTop Γ) ≠ ⊤) htop
  · rw [newtonWeight, hcoeffm]
    have hval :
        addVal k Γ
            ((((g.comp (Polynomial.X + Polynomial.C A)).coeff m : valuationSubring k Γ) :
              HahnField k Γ)) =
          (0 : WithTop Γ) :=
      addVal_eq_zero_of_isUnit k Γ ((g.comp (Polynomial.X + Polynomial.C A)).coeff m)
        hunit
    rw [hval, zero_add, ← WithTop.coe_nsmul, hscale]

theorem high_notMem_newtonInitialSupport_map_comp_X_add_C_of_unit_scale
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m i : ℕ} {δ γ : Γ}
    (hδpos : 0 < δ) (hscale : m • δ = γ) (hmi : m < i) :
    i ∉ newtonInitialSupport k Γ
      ((g.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ := by
  intro hi
  let G : (HahnField k Γ)[X] :=
    (g.comp (Polynomial.X + Polynomial.C A)).map
      (algebraMap (valuationSubring k Γ) (HahnField k Γ))
  rcases (mem_newtonInitialSupport k Γ G δ γ).mp hi with ⟨_hisupp, hweight⟩
  have hcoeffi :
      G.coeff i =
        (((g.comp (Polynomial.X + Polynomial.C A)).coeff i : valuationSubring k Γ) :
          HahnField k Γ) := by
    dsimp [G]
    exact coeff_map_comp_X_add_C k Γ g A i
  have hweight_gt : (γ : WithTop Γ) < newtonWeight k Γ G δ i := by
    rw [newtonWeight, hcoeffi, ← hscale, ← WithTop.coe_nsmul]
    have hcoeff_nonneg :
        (0 : WithTop Γ) ≤
          addVal k Γ
            ((((g.comp (Polynomial.X + Polynomial.C A)).coeff i : valuationSubring k Γ) :
              HahnField k Γ)) :=
      ((g.comp (Polynomial.X + Polynomial.C A)).coeff i).property
    have hpow_lt : (m • δ : WithTop Γ) < (i • δ : WithTop Γ) := by
      exact_mod_cast nsmul_lt_nsmul_left hδpos hmi
    exact lt_of_lt_of_le hpow_lt (le_add_of_nonneg_left hcoeff_nonneg)
  rw [hweight] at hweight_gt
  exact lt_irrefl _ hweight_gt

theorem le_addVal_coeff_scalePolynomial_of_newtonWeight_ge
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ} {i : ℕ}
    (hge : (μ : WithTop Γ) ≤ newtonWeight k Γ G δ i) :
    (0 : WithTop Γ) ≤ addVal k Γ ((scalePolynomial k Γ G δ μ).coeff i) := by
  rw [addVal_coeff_scalePolynomial]
  have h := add_le_add_left hge ((-μ : Γ) : WithTop Γ)
  simpa [newtonWeight, add_comm, add_left_comm, add_assoc] using h

/-- Lift a Hahn-field polynomial with nonnegative coefficient valuations to the natural
valuation subring, coefficient by coefficient. -/
noncomputable def polynomialIntegralLift (S : Polynomial (HahnField k Γ))
    (hS : ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (S.coeff i)) :
    Polynomial (valuationSubring k Γ) :=
  S.support.sum fun i => Polynomial.monomial i ⟨S.coeff i, hS i⟩

theorem polynomialIntegralLift_coeff_coe (S : Polynomial (HahnField k Γ))
    (hS : ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (S.coeff i)) (i : ℕ) :
    ((polynomialIntegralLift k Γ S hS).coeff i : HahnField k Γ) = S.coeff i := by
  by_cases hi : i ∈ S.support
  · rw [polynomialIntegralLift]
    simp [Polynomial.coeff_monomial, hi]
  · rw [polynomialIntegralLift]
    have hzero : S.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
    simp [Polynomial.coeff_monomial, hi, hzero]

theorem polynomialIntegralLift_map_eq (S : Polynomial (HahnField k Γ))
    (hS : ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (S.coeff i)) :
    (polynomialIntegralLift k Γ S hS).map
      (algebraMap (valuationSubring k Γ) (HahnField k Γ)) = S := by
  ext i
  rw [Polynomial.coeff_map]
  exact (Algebra.algebraMap_ofSubsemiring_apply (valuationSubring k Γ)
    ((polynomialIntegralLift k Γ S hS).coeff i)).trans
    (polynomialIntegralLift_coeff_coe k Γ S hS i)

theorem coeff_map_constantCoeff_polynomialIntegralLift_eq_newtonInitial_zero_zero
    (S : Polynomial (HahnField k Γ))
    (hS : ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (S.coeff i)) (i : ℕ) :
    ((polynomialIntegralLift k Γ S hS).map (constantCoeffRingHom k Γ)).coeff i =
      (newtonInitialPolynomial k Γ S 0 0).coeff i := by
  rw [Polynomial.coeff_map, coeff_newtonInitialPolynomial]
  by_cases hi : i ∈ newtonInitialSupport k Γ S 0 0
  · rw [newtonInitialCoeff_of_mem k Γ S 0 0 hi]
    simp only [constantCoeffRingHom_apply, nsmul_zero, sub_zero]
    rw [polynomialIntegralLift_coeff_coe]
  · rw [newtonInitialCoeff_of_notMem k Γ S 0 0 hi]
    have hnot0 : S.coeff i = 0 ∨ (0 : WithTop Γ) < addVal k Γ (S.coeff i) := by
      by_cases hsupp : i ∈ S.support
      · have hweight_ne : newtonWeight k Γ S 0 i ≠ (0 : WithTop Γ) := by
          intro hweight
          exact hi ((mem_newtonInitialSupport k Γ S 0 0).mpr ⟨hsupp, hweight⟩)
        have hweight : newtonWeight k Γ S 0 i = addVal k Γ (S.coeff i) := by
          simp [newtonWeight]
        right
        have hne : addVal k Γ (S.coeff i) ≠ (0 : WithTop Γ) := by
          intro hv
          exact hweight_ne (by simpa [hweight] using hv)
        exact lt_of_le_of_ne (hS i) (fun h => hne h.symm)
      · left
        exact Polynomial.notMem_support_iff.mp hsupp
    rcases hnot0 with hzero | hpos
    · have hcoeff : (polynomialIntegralLift k Γ S hS).coeff i = 0 := by
        apply Subtype.ext
        simp [hzero, polynomialIntegralLift_coeff_coe k Γ S hS i]
      simp [hcoeff]
    · have hcc0 : constantCoeffRingHom k Γ ((polynomialIntegralLift k Γ S hS).coeff i) = 0 := by
        apply (constantCoeffRingHom_eq_zero_iff_pos_addVal k Γ _).mpr
        change (0 : WithTop Γ) <
          (ofLex (((polynomialIntegralLift k Γ S hS).coeff i : valuationSubring k Γ) :
            HahnField k Γ)).orderTop
        rw [polynomialIntegralLift_coeff_coe]
        simpa [addVal_apply] using hpos
      simp [hcc0]

theorem map_constantCoeff_polynomialIntegralLift_eq_newtonInitial_zero_zero
    (S : Polynomial (HahnField k Γ))
    (hS : ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (S.coeff i)) :
    (polynomialIntegralLift k Γ S hS).map (constantCoeffRingHom k Γ) =
      newtonInitialPolynomial k Γ S 0 0 := by
  ext i
  exact coeff_map_constantCoeff_polynomialIntegralLift_eq_newtonInitial_zero_zero k Γ S hS i

theorem addVal_coeff_scalePolynomial_eq_zero_of_newtonWeight_eq
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ} {i : ℕ}
    (hweight : newtonWeight k Γ G δ i = (μ : WithTop Γ)) :
    addVal k Γ ((scalePolynomial k Γ G δ μ).coeff i) = 0 := by
  rw [addVal_coeff_scalePolynomial]
  simpa [newtonWeight, add_comm, add_left_comm, add_assoc] using
    congrArg (fun w => ((-μ : Γ) : WithTop Γ) + w) hweight

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem coeff_zero_scalePolynomial_coeff
    (G : Polynomial (HahnField k Γ)) (δ μ : Γ) (i : ℕ) :
    (ofLex ((scalePolynomial k Γ G δ μ).coeff i)).coeff 0 =
      (ofLex (G.coeff i)).coeff (μ - i • δ) := by
  rw [coeff_scalePolynomial]
  change ((HahnSeries.single (-μ) (1 : k) * ofLex (G.coeff i) *
      (HahnSeries.single δ (1 : k)) ^ i).coeff 0) =
    (ofLex (G.coeff i)).coeff (μ - i • δ)
  rw [HahnSeries.single_pow, HahnSeries.coeff_mul_single]
  rw [HahnSeries.coeff_single_mul]
  simp [sub_eq_add_neg, add_comm]

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem coeff_zero_scalePolynomial_coeff_of_mem_initialSupport
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ} {i : ℕ}
    (hi : i ∈ newtonInitialSupport k Γ G δ μ) :
    (ofLex ((scalePolynomial k Γ G δ μ).coeff i)).coeff 0 =
      newtonInitialCoeff k Γ G δ μ i := by
  rw [newtonInitialCoeff_of_mem k Γ G δ μ hi]
  exact coeff_zero_scalePolynomial_coeff k Γ G δ μ i

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem coeff_zero_scalePolynomial_coeff_eq_zero_of_notMem_initialSupport_of_weight_ge
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ} {i : ℕ}
    (hge : (μ : WithTop Γ) ≤ newtonWeight k Γ G δ i)
    (hnot : i ∉ newtonInitialSupport k Γ G δ μ) :
    (ofLex ((scalePolynomial k Γ G δ μ).coeff i)).coeff 0 = 0 := by
  rw [coeff_zero_scalePolynomial_coeff]
  by_cases hisupp : i ∈ G.support
  · have hweight_ne : newtonWeight k Γ G δ i ≠ (μ : WithTop Γ) := by
      intro hweight
      exact hnot ((mem_newtonInitialSupport k Γ G δ μ).mpr ⟨hisupp, hweight⟩)
    have hgt : (μ : WithTop Γ) < newtonWeight k Γ G δ i :=
      lt_of_le_of_ne hge (fun hEq => hweight_ne hEq.symm)
    let η : Γ := coeffValueOfMemSupport k Γ G hisupp
    have hval : addVal k Γ (G.coeff i) = (η : WithTop Γ) :=
      addVal_coeff_eq_coeffValueOfMemSupport k Γ G hisupp
    have hweight_eq : newtonWeight k Γ G δ i = ((η + i • δ : Γ) : WithTop Γ) := by
      dsimp [η]
      rw [newtonWeight_eq_of_mem_support k Γ G δ hisupp]
      rfl
    have hgtΓ : μ < η + i • δ := by
      exact WithTop.coe_lt_coe.mp (by simpa [hweight_eq] using hgt)
    have hltΓ : μ - i • δ < η := by
      rw [sub_lt_iff_lt_add]
      simpa [add_comm, add_left_comm, add_assoc] using hgtΓ
    have hltTop : ((μ - i • δ : Γ) : WithTop Γ) < addVal k Γ (G.coeff i) := by
      rw [hval]
      exact_mod_cast hltΓ
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop (by simpa [addVal_apply] using hltTop)
  · rw [Polynomial.notMem_support_iff.mp hisupp]
    simp

theorem lt_addVal_coeff_scalePolynomial_of_notMem_initialSupport_of_weight_ge
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ} {i : ℕ}
    (hge : (μ : WithTop Γ) ≤ newtonWeight k Γ G δ i)
    (hnot : i ∉ newtonInitialSupport k Γ G δ μ) :
    (0 : WithTop Γ) < addVal k Γ ((scalePolynomial k Γ G δ μ).coeff i) := by
  apply lt_addVal_of_le_addVal_of_coeff_eq_zero k Γ
  · exact le_addVal_coeff_scalePolynomial_of_newtonWeight_ge k Γ G hge
  · exact coeff_zero_scalePolynomial_coeff_eq_zero_of_notMem_initialSupport_of_weight_ge
      k Γ G hge hnot

theorem coeff_newtonInitialPolynomial_scalePolynomial_zero_zero_of_weight_ge
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ}
    (hge : ∀ i, (μ : WithTop Γ) ≤ newtonWeight k Γ G δ i) (i : ℕ) :
    (newtonInitialPolynomial k Γ (scalePolynomial k Γ G δ μ) 0 0).coeff i =
      (newtonInitialPolynomial k Γ G δ μ).coeff i := by
  rw [coeff_newtonInitialPolynomial, coeff_newtonInitialPolynomial]
  by_cases hi : i ∈ newtonInitialSupport k Γ G δ μ
  · have hweight : newtonWeight k Γ G δ i = (μ : WithTop Γ) :=
      ((mem_newtonInitialSupport k Γ G δ μ).mp hi).2
    have hval0 :
        addVal k Γ ((scalePolynomial k Γ G δ μ).coeff i) = 0 :=
      addVal_coeff_scalePolynomial_eq_zero_of_newtonWeight_eq k Γ G hweight
    have hsupp :
        i ∈ (scalePolynomial k Γ G δ μ).support := by
      rw [Polynomial.mem_support_iff]
      intro hzero
      simp [hzero] at hval0
    have hmem0 :
        i ∈ newtonInitialSupport k Γ (scalePolynomial k Γ G δ μ) 0 0 := by
      rw [mem_newtonInitialSupport]
      refine ⟨hsupp, ?_⟩
      rw [newtonWeight, hval0]
      simp
    rw [newtonInitialCoeff_of_mem k Γ (scalePolynomial k Γ G δ μ) 0 0 hmem0]
    simpa using coeff_zero_scalePolynomial_coeff_of_mem_initialSupport k Γ G hi
  · have hcoeffP :
        newtonInitialCoeff k Γ G δ μ i = 0 :=
      newtonInitialCoeff_of_notMem k Γ G δ μ hi
    rw [hcoeffP]
    have hval_pos :
        (0 : WithTop Γ) < addVal k Γ ((scalePolynomial k Γ G δ μ).coeff i) :=
      lt_addVal_coeff_scalePolynomial_of_notMem_initialSupport_of_weight_ge k Γ G (hge i) hi
    have hnot0 :
        i ∉ newtonInitialSupport k Γ (scalePolynomial k Γ G δ μ) 0 0 := by
      intro hmem0
      rcases (mem_newtonInitialSupport k Γ (scalePolynomial k Γ G δ μ) 0 0).mp hmem0 with
        ⟨_hsupp, hweight0⟩
      have hval0 :
          addVal k Γ ((scalePolynomial k Γ G δ μ).coeff i) = 0 := by
        simpa [newtonWeight] using hweight0
      exact (ne_of_gt hval_pos) hval0
    exact newtonInitialCoeff_of_notMem k Γ (scalePolynomial k Γ G δ μ) 0 0 hnot0

theorem newtonInitialPolynomial_scalePolynomial_zero_zero_of_weight_ge
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ}
    (hge : ∀ i, (μ : WithTop Γ) ≤ newtonWeight k Γ G δ i) :
    newtonInitialPolynomial k Γ (scalePolynomial k Γ G δ μ) 0 0 =
      newtonInitialPolynomial k Γ G δ μ := by
  ext i
  exact coeff_newtonInitialPolynomial_scalePolynomial_zero_zero_of_weight_ge k Γ G hge i

theorem newtonWeight_ge_map_comp_X_add_C_of_unit_scale_nonbelow
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ} {δ γ : Γ}
    (hval :
      addVal k Γ ((g.eval A : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ))
    (hunit : IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m))
    (hδpos : 0 < δ) (hscale : m • δ = γ)
    (hnotBelow :
      ∀ j, 0 < j → j < m →
        (((m - j) • δ : Γ) : WithTop Γ) ≤
          addVal k Γ ((g.comp (Polynomial.X + Polynomial.C A)).coeff j : HahnField k Γ)) :
    ∀ i,
      (γ : WithTop Γ) ≤
        newtonWeight k Γ
          ((g.comp (Polynomial.X + Polynomial.C A)).map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ i := by
  intro i
  let G : (HahnField k Γ)[X] :=
    (g.comp (Polynomial.X + Polynomial.C A)).map
      (algebraMap (valuationSubring k Γ) (HahnField k Γ))
  have hcoeffi :
      G.coeff i =
        (((g.comp (Polynomial.X + Polynomial.C A)).coeff i : valuationSubring k Γ) :
          HahnField k Γ) := by
    dsimp [G]
    exact coeff_map_comp_X_add_C k Γ g A i
  by_cases hi0 : i = 0
  · subst i
    have hcoeff0 : G.coeff 0 = ((g.eval A : valuationSubring k Γ) : HahnField k Γ) := by
      dsimp [G]
      exact coeff_zero_map_comp_X_add_C k Γ g A
    rw [newtonWeight, hcoeff0, hval]
    simp
  · by_cases him : i = m
    · subst i
      rw [newtonWeight, hcoeffi]
      have hvalm :
          addVal k Γ
              ((((g.comp (Polynomial.X + Polynomial.C A)).coeff m : valuationSubring k Γ) :
                HahnField k Γ)) =
            (0 : WithTop Γ) :=
        addVal_eq_zero_of_isUnit k Γ ((g.comp (Polynomial.X + Polynomial.C A)).coeff m)
          hunit
      rw [hvalm, zero_add, ← WithTop.coe_nsmul, hscale]
    · by_cases hlt : i < m
      · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
        have hleCoeff := hnotBelow i hpos hlt
        calc
          (γ : WithTop Γ) =
              (((m - i) • δ + i • δ : Γ) : WithTop Γ) := by
                rw [← add_nsmul, Nat.sub_add_cancel (le_of_lt hlt), hscale]
          _ = (((m - i) • δ : Γ) : WithTop Γ) + (i • (δ : WithTop Γ)) := by
                simp [WithTop.coe_add, ← WithTop.coe_nsmul]
          _ ≤ addVal k Γ
                ((((g.comp (Polynomial.X + Polynomial.C A)).coeff i : valuationSubring k Γ) :
                  HahnField k Γ)) + i • (δ : WithTop Γ) :=
                by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_left hleCoeff (i • (δ : WithTop Γ))
          _ = newtonWeight k Γ G δ i := by
                rw [newtonWeight, hcoeffi]
      · have hmi : m < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm him)
        have hcoeff_nonneg :
            (0 : WithTop Γ) ≤
              addVal k Γ
                ((((g.comp (Polynomial.X + Polynomial.C A)).coeff i : valuationSubring k Γ) :
                  HahnField k Γ)) :=
          ((g.comp (Polynomial.X + Polynomial.C A)).coeff i).property
        have hpow_le : (m • δ : WithTop Γ) ≤ (i • δ : WithTop Γ) := by
          exact_mod_cast nsmul_le_nsmul_left (le_of_lt hδpos) (le_of_lt hmi)
        calc
          (γ : WithTop Γ) = ((m • δ : Γ) : WithTop Γ) := by
            rw [hscale]
          _ = m • (δ : WithTop Γ) := by
            rw [WithTop.coe_nsmul]
          _ ≤ (i • δ : WithTop Γ) := hpow_le
          _ ≤ addVal k Γ
                ((((g.comp (Polynomial.X + Polynomial.C A)).coeff i : valuationSubring k Γ) :
                  HahnField k Γ)) + i • (δ : WithTop Γ) :=
                le_add_of_nonneg_left hcoeff_nonneg
          _ = newtonWeight k Γ G δ i := by
                rw [newtonWeight, hcoeffi]

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem coeff_newtonInitialPolynomial_ne_zero_of_mem
    {G : (HahnField k Γ)[X]} {δ γ : Γ} {i : ℕ}
    (hi : i ∈ newtonInitialSupport k Γ G δ γ) :
    (newtonInitialPolynomial k Γ G δ γ).coeff i ≠ 0 := by
  rw [coeff_newtonInitialPolynomial]
  exact newtonInitialCoeff_ne_zero_of_mem k Γ G δ γ hi

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem le_natDegree_newtonInitialPolynomial_of_mem
    {G : (HahnField k Γ)[X]} {δ γ : Γ} {i : ℕ}
    (hi : i ∈ newtonInitialSupport k Γ G δ γ) :
    i ≤ (newtonInitialPolynomial k Γ G δ γ).natDegree :=
  Polynomial.le_natDegree_of_ne_zero
    (coeff_newtonInitialPolynomial_ne_zero_of_mem k Γ hi)

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem natDegree_newtonInitialPolynomial_eq_of_mem_of_high_notMem
    {G : (HahnField k Γ)[X]} {δ γ : Γ} {m : ℕ}
    (hm : m ∈ newtonInitialSupport k Γ G δ γ)
    (hhigh : ∀ i, m < i → i ∉ newtonInitialSupport k Γ G δ γ) :
    (newtonInitialPolynomial k Γ G δ γ).natDegree = m := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_newtonInitialPolynomial]
    exact newtonInitialCoeff_of_notMem k Γ G δ γ (hhigh i hi)
  · exact le_natDegree_newtonInitialPolynomial_of_mem k Γ hm

theorem natDegree_newtonInitialPolynomial_map_comp_X_add_C_eq_of_unit_scale_high_notMem
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ} {δ γ : Γ}
    (hunit : IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m))
    (hscale : m • δ = γ)
    (hhigh :
      ∀ i, m < i →
        i ∉ newtonInitialSupport k Γ
          ((g.comp (Polynomial.X + Polynomial.C A)).map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ) :
    (newtonInitialPolynomial k Γ
      ((g.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).natDegree = m :=
  natDegree_newtonInitialPolynomial_eq_of_mem_of_high_notMem k Γ
    (main_mem_newtonInitialSupport_map_comp_X_add_C_of_unit_scale k Γ hunit hscale)
    hhigh

theorem natDegree_newtonInitialPolynomial_map_comp_X_add_C_eq_of_unit_scale
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ} {δ γ : Γ}
    (hδpos : 0 < δ)
    (hunit : IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m))
    (hscale : m • δ = γ) :
    (newtonInitialPolynomial k Γ
      ((g.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).natDegree = m :=
  natDegree_newtonInitialPolynomial_map_comp_X_add_C_eq_of_unit_scale_high_notMem
    k Γ hunit hscale
    (fun i hi =>
      high_notMem_newtonInitialSupport_map_comp_X_add_C_of_unit_scale
        (i := i) k Γ hδpos hscale hi)

theorem odd_natDegree_newtonInitialPolynomial_map_comp_X_add_C_of_unit_scale_high_notMem
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ} {δ γ : Γ}
    (hodd : Odd m)
    (hunit : IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m))
    (hscale : m • δ = γ)
    (hhigh :
      ∀ i, m < i →
        i ∉ newtonInitialSupport k Γ
          ((g.comp (Polynomial.X + Polynomial.C A)).map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ) :
    Odd (newtonInitialPolynomial k Γ
      ((g.comp (Polynomial.X + Polynomial.C A)).map
        (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).natDegree := by
  rw [natDegree_newtonInitialPolynomial_map_comp_X_add_C_eq_of_unit_scale_high_notMem
    k Γ hunit hscale hhigh]
  exact hodd

theorem exists_nonzero_root_odd_rootMultiplicity_newtonInitialPolynomial_map_comp_X_add_C
    [IsRealClosed k]
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ} {δ γ : Γ}
    (hodd : Odd m)
    (hval :
      addVal k Γ ((g.eval A : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ))
    (hunit : IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m))
    (hscale : m • δ = γ)
    (hhigh :
      ∀ i, m < i →
        i ∉ newtonInitialSupport k Γ
          ((g.comp (Polynomial.X + Polynomial.C A)).map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ) :
    ∃ a : k, a ≠ 0 ∧
      0 < (newtonInitialPolynomial k Γ
        ((g.comp (Polynomial.X + Polynomial.C A)).map
          (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).rootMultiplicity a ∧
        Odd ((newtonInitialPolynomial k Γ
          ((g.comp (Polynomial.X + Polynomial.C A)).map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).rootMultiplicity a) ∧
          (newtonInitialPolynomial k Γ
            ((g.comp (Polynomial.X + Polynomial.C A)).map
              (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).rootMultiplicity a ≤
            (newtonInitialPolynomial k Γ
              ((g.comp (Polynomial.X + Polynomial.C A)).map
                (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).natDegree := by
  let G : (HahnField k Γ)[X] :=
    (g.comp (Polynomial.X + Polynomial.C A)).map
      (algebraMap (valuationSubring k Γ) (HahnField k Γ))
  let p : k[X] := newtonInitialPolynomial k Γ G δ γ
  have hoddNat : Odd (newtonInitialPolynomial k Γ G δ γ).natDegree := by
    dsimp [G]
    exact odd_natDegree_newtonInitialPolynomial_map_comp_X_add_C_of_unit_scale_high_notMem
      k Γ hodd hunit hscale hhigh
  have hcoeff0 : p.coeff 0 ≠ 0 := by
    dsimp [p, G]
    exact coeff_newtonInitialPolynomial_ne_zero_of_mem k Γ
      (zero_mem_newtonInitialSupport_map_comp_X_add_C_of_eval_addVal_eq k Γ hval)
  simpa [p] using
    (exists_nonzero_root_odd_rootMultiplicity_le_natDegree hcoeff0 hoddNat)

theorem
    exists_nonzero_root_odd_rootMultiplicity_newtonInitialPolynomial_map_comp_X_add_C_of_unit_scale
    [IsRealClosed k]
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ} {δ γ : Γ}
    (hodd : Odd m)
    (hval :
      addVal k Γ ((g.eval A : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ))
    (hδpos : 0 < δ)
    (hunit : IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m))
    (hscale : m • δ = γ) :
    ∃ a : k, a ≠ 0 ∧
      0 < (newtonInitialPolynomial k Γ
        ((g.comp (Polynomial.X + Polynomial.C A)).map
          (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).rootMultiplicity a ∧
        Odd ((newtonInitialPolynomial k Γ
          ((g.comp (Polynomial.X + Polynomial.C A)).map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).rootMultiplicity a) ∧
          (newtonInitialPolynomial k Γ
            ((g.comp (Polynomial.X + Polynomial.C A)).map
              (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).rootMultiplicity a ≤
            (newtonInitialPolynomial k Γ
              ((g.comp (Polynomial.X + Polynomial.C A)).map
                (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).natDegree :=
  exists_nonzero_root_odd_rootMultiplicity_newtonInitialPolynomial_map_comp_X_add_C
    k Γ hodd hval hunit hscale
    (fun i hi =>
      high_notMem_newtonInitialSupport_map_comp_X_add_C_of_unit_scale
        (i := i) k Γ hδpos hscale hi)

/-- If a residue root has multiplicity `m`, then after lifting the root and translating, lower
coefficients lie in the maximal ideal. -/
theorem coeff_comp_X_add_C_mem_maximalIdeal_of_lt_rootMultiplicity
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m i : ℕ}
    (hm : (g.map (constantCoeffRingHom k Γ)).rootMultiplicity
      (constantCoeffRingHom k Γ A) = m)
    (hi : i < m) :
    (g.comp (Polynomial.X + Polynomial.C A)).coeff i ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  apply coeff_mem_maximalIdeal_of_map_constantCoeff_coeff_eq_zero k Γ
  rw [coeff_map_constantCoeff_comp_X_add_C]
  exact coeff_comp_X_add_C_eq_zero_of_lt_rootMultiplicity hm hi

/-- If a residue root has multiplicity `m`, then after lifting the root and translating, the
coefficient of degree `m` is a unit. -/
theorem isUnit_coeff_comp_X_add_C_of_rootMultiplicity_eq
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ}
    (hg : g.map (constantCoeffRingHom k Γ) ≠ 0)
    (hm : (g.map (constantCoeffRingHom k Γ)).rootMultiplicity
      (constantCoeffRingHom k Γ A) = m) :
    IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m) := by
  apply isUnit_coeff_of_map_constantCoeff_coeff_ne_zero k Γ
  rw [coeff_map_constantCoeff_comp_X_add_C]
  exact coeff_comp_X_add_C_ne_zero_of_rootMultiplicity_eq hg hm

/-- A residue root multiplicity becomes the cluster coefficient conditions after translating the
root to zero. -/
theorem cluster_coeffs_comp_X_add_C_of_rootMultiplicity_eq
    {g : (valuationSubring k Γ)[X]} {A : valuationSubring k Γ} {m : ℕ}
    (hg : g.map (constantCoeffRingHom k Γ) ≠ 0)
    (hm : (g.map (constantCoeffRingHom k Γ)).rootMultiplicity
      (constantCoeffRingHom k Γ A) = m) :
    (∀ i, i < m → (g.comp (Polynomial.X + Polynomial.C A)).coeff i ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ)) ∧
      IsUnit ((g.comp (Polynomial.X + Polynomial.C A)).coeff m) := by
  constructor
  · intro i hi
    exact coeff_comp_X_add_C_mem_maximalIdeal_of_lt_rootMultiplicity
      k Γ hm hi
  · exact isUnit_coeff_comp_X_add_C_of_rootMultiplicity_eq k Γ hg hm

/-- Scaling an integral Newton edge and translating by an odd-multiplicity residue root produces
an honest lower odd cluster.  This is the generic residue bridge used by both lower-edge and
plateau-reset continuations. -/
theorem oddClusterHypotheses_scalePolynomial_comp_single_zero_of_rootMultiplicity
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ}
    (hge : ∀ i, (μ : WithTop Γ) ≤ newtonWeight k Γ G δ i)
    {a : k} {r : ℕ}
    (hmul : (newtonInitialPolynomial k Γ G δ μ).rootMultiplicity a = r)
    (hrpos : 0 < r) (hrodd : Odd r) :
    KOddClusterHypotheses k Γ
      ((scalePolynomial k Γ G δ μ).comp
        (Polynomial.X + Polynomial.C (toLex (HahnSeries.single 0 a)))) r := by
  let S := scalePolynomial k Γ G δ μ
  have hS : ∀ i, (0 : WithTop Γ) ≤ addVal k Γ (S.coeff i) := by
    intro i
    exact le_addVal_coeff_scalePolynomial_of_newtonWeight_ge k Γ G (hge i)
  let T := polynomialIntegralLift k Γ S hS
  let A : valuationSubring k Γ := ⟨toLex (HahnSeries.single 0 a), by
    change (0 : WithTop Γ) ≤ addVal k Γ (toLex (HahnSeries.single 0 a))
    by_cases ha : a = 0
    · simp [ha]
    · rw [addVal_single_of_ne (k := k) (Γ := Γ) ha]
      exact le_rfl⟩
  have hTmap :
      T.map (algebraMap (valuationSubring k Γ) (HahnField k Γ)) = S :=
    polynomialIntegralLift_map_eq k Γ S hS
  have hTres :
      T.map (constantCoeffRingHom k Γ) = newtonInitialPolynomial k Γ G δ μ := by
    rw [map_constantCoeff_polynomialIntegralLift_eq_newtonInitial_zero_zero]
    exact newtonInitialPolynomial_scalePolynomial_zero_zero_of_weight_ge k Γ G hge
  have hAres : constantCoeffRingHom k Γ A = a := by
    dsimp [A]
    simp
  have hmT :
      (T.map (constantCoeffRingHom k Γ)).rootMultiplicity
        (constantCoeffRingHom k Γ A) = r := by
    rw [hTres, hAres]
    exact hmul
  have hPne : newtonInitialPolynomial k Γ G δ μ ≠ 0 := by
    intro hzero
    rw [hzero] at hmul
    simp at hmul
    omega
  have hTne : T.map (constantCoeffRingHom k Γ) ≠ 0 := by
    rw [hTres]
    exact hPne
  rcases cluster_coeffs_comp_X_add_C_of_rootMultiplicity_eq k Γ (g := T) (A := A)
      hTne hmT with ⟨hlowerT, hunitT⟩
  have hcomp :
      (T.comp (Polynomial.X + Polynomial.C A)).map
          (algebraMap (valuationSubring k Γ) (HahnField k Γ)) =
        S.comp (Polynomial.X + Polynomial.C (toLex (HahnSeries.single 0 a))) := by
    rw [Polynomial.map_comp, hTmap]
    have hAmap :
        algebraMap (valuationSubring k Γ) (HahnField k Γ) A =
          toLex (HahnSeries.single 0 a) := by
      change ((A : valuationSubring k Γ) : HahnField k Γ) =
        toLex (HahnSeries.single 0 a)
      rfl
    have hXCA :
        Polynomial.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))
            (Polynomial.X + Polynomial.C A) =
          Polynomial.X + Polynomial.C (toLex (HahnSeries.single 0 a)) := by
      ext n
      simp [hAmap]
    rw [hXCA]
  refine ⟨hrpos, hrodd, ?_, ?_, ?_⟩
  · intro i
    rw [← hcomp, Polynomial.coeff_map]
    change (0 : WithTop Γ) ≤ addVal k Γ
      (((T.comp (Polynomial.X + Polynomial.C A)).coeff i : valuationSubring k Γ) :
        HahnField k Γ)
    exact ((T.comp (Polynomial.X + Polynomial.C A)).coeff i).property
  · intro i hi
    rw [← hcomp]
    have hmem := hlowerT i hi
    rw [mem_maximalIdeal_iff_pos_addVal] at hmem
    simpa [coeff_map_comp_X_add_C, Algebra.algebraMap_ofSubsemiring_apply] using hmem
  · rw [← hcomp]
    have hval := addVal_coeff_eq_zero_of_isUnit k Γ hunitT
    simpa [coeff_map_comp_X_add_C, Algebra.algebraMap_ofSubsemiring_apply] using hval

/-- A Newton-scaled root transports back while preserving an arbitrary property stable under
translation by the residue term and multiplication by the Newton monomial. -/
theorem exists_root_of_scalePolynomial_comp_single_zero_with_property
    (G : Polynomial (HahnField k Γ)) {δ μ : Γ} (a : k)
    (P : HahnField k Γ → Prop)
    (hP_add : ∀ y, P y → P (y + toLex (HahnSeries.single 0 a)))
    (hP_mul : ∀ y, P y → P (hahnMonomial k Γ δ * y))
    (hroot : ∃ y : HahnField k Γ,
      (0 : WithTop Γ) < addVal k Γ y ∧
        P y ∧
          ((scalePolynomial k Γ G δ μ).comp
            (Polynomial.X + Polynomial.C (toLex (HahnSeries.single 0 a)))).IsRoot y) :
    ∃ z : HahnField k Γ,
      (δ : WithTop Γ) ≤ addVal k Γ z ∧ P z ∧ G.IsRoot z := by
  rcases hroot with ⟨y, hypos, hyP, hyroot⟩
  let aH : HahnField k Γ := toLex (HahnSeries.single 0 a)
  let yA : HahnField k Γ := y + aH
  have ha_nonneg : (0 : WithTop Γ) ≤ addVal k Γ aH := by
    by_cases ha : a = 0
    · simp [aH, ha]
    · rw [show aH = toLex (HahnSeries.single (0 : Γ) a) by rfl,
        addVal_single_of_ne (k := k) (Γ := Γ) ha]
      exact le_rfl
  have hyA_nonneg : (0 : WithTop Γ) ≤ addVal k Γ yA :=
    le_addVal_add_of_le_addVal k Γ (le_of_lt hypos) ha_nonneg
  have hyAroot : (scalePolynomial k Γ G δ μ).IsRoot yA := by
    rw [Polynomial.IsRoot] at hyroot ⊢
    simpa [yA, aH, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C] using hyroot
  let z : HahnField k Γ := hahnMonomial k Γ δ * yA
  have hzlower : (δ : WithTop Γ) ≤ addVal k Γ z := by
    rw [show z = hahnMonomial k Γ δ * yA by rfl, AddValuation.map_mul,
      addVal_hahnMonomial]
    exact le_add_of_nonneg_right hyA_nonneg
  have hzP : P z := by
    exact hP_mul yA (by simpa [yA, aH] using hP_add y hyP)
  exact ⟨z, hzlower, hzP, isRoot_of_scalePolynomial_isRoot k Γ hyAroot⟩

/-- Translating a cluster by a maximal-ideal element preserves the lower coefficient condition. -/
theorem coeff_comp_X_add_C_mem_maximalIdeal_of_cluster_of_mem_maximalIdeal
    {F : (valuationSubring k Γ)[X]} {m i : ℕ} {y : valuationSubring k Γ}
    (hsmall : ∀ j, j < m → F.coeff j ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hi : i < m) :
    (F.comp (Polynomial.X + Polynomial.C y)).coeff i ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  apply coeff_mem_maximalIdeal_of_map_constantCoeff_coeff_eq_zero k Γ
  rw [coeff_map_constantCoeff_comp_X_add_C]
  have hy0 : constantCoeffRingHom k Γ y = 0 := by
    rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ)] at hy
    exact RingHom.mem_ker.mp hy
  simpa [hy0] using coeff_map_constantCoeff_eq_zero_of_cluster_lt k Γ hsmall hi

/-- Translating a cluster by a maximal-ideal element preserves the unit main coefficient. -/
theorem isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    (hunit : IsUnit (F.coeff m))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m) := by
  apply isUnit_coeff_of_map_constantCoeff_coeff_ne_zero k Γ
  rw [coeff_map_constantCoeff_comp_X_add_C]
  have hy0 : constantCoeffRingHom k Γ y = 0 := by
    rw [← constantCoeffRingHom_ker_eq_maximalIdeal (k := k) (Γ := Γ)] at hy
    exact RingHom.mem_ker.mp hy
  simpa [hy0] using coeff_map_constantCoeff_ne_zero_of_cluster_unit k Γ hunit

/-- Translating a cluster by a maximal-ideal element preserves the cluster coefficient
conditions. -/
theorem cluster_coeffs_comp_X_add_C_of_mem_maximalIdeal
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff m))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    (∀ i, i < m → (F.comp (Polynomial.X + Polynomial.C y)).coeff i ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ)) ∧
      IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m) := by
  constructor
  · intro i hi
    exact coeff_comp_X_add_C_mem_maximalIdeal_of_cluster_of_mem_maximalIdeal
      k Γ hsmall hy hi
  · exact isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal k Γ hunit hy

/-- At a non-root maximal-ideal approximation, choose the main cluster correction together with
the exact current evaluation valuation and the resulting strict main-term improvement. -/
theorem exists_main_correction_improves_eval_at_of_cluster_with_value
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    (hm_pos : 0 < m) (hm_odd : Odd m)
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff m))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hne : F.eval y ≠ 0) :
    ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
      ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ m • δ = γ ∧
        addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
          (γ : WithTop Γ) ∧
          (γ : WithTop Γ) <
            addVal k Γ (((F.eval y : valuationSubring k Γ) : HahnField k Γ) +
              ((F.comp (Polynomial.X + Polynomial.C y)).coeff m : HahnField k Γ) *
                (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m) := by
  have hunit' : IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m) :=
    isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal k Γ hunit hy
  have hemem : F.eval y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
    eval_mem_maximalIdeal_of_cluster_pos k Γ hsmall hm_pos hy
  exact exists_main_correction_improves_error_with_value
    k Γ (F := F.comp (Polynomial.X + Polynomial.C y)) (e := F.eval y)
    hm_pos hm_odd hunit' hemem hne

/-- Version of the one-step estimate around a maximal-ideal approximation `y`, expressed back in
the original polynomial. The hypotheses on lower coefficients are for the translated polynomial
`F(X + y)`. -/
theorem lt_addVal_eval_add_singleOfNonneg_of_translated_const_main_improves
    {F : (valuationSubring k Γ)[X]} {m : ℕ} {y : valuationSubring k Γ}
    {δ γ : Γ} {c : k}
    (hm_pos : 0 < m)
    (hunit : IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff m))
    (hδpos : 0 < δ) (hc : c ≠ 0) (hδ : m • δ = γ)
    (hlower : ∀ j, 0 < j → j < m → (((m - j) • δ : Γ) : WithTop Γ) <
      addVal k Γ ((F.comp (Polynomial.X + Polynomial.C y)).coeff j : HahnField k Γ))
    (hmain : (γ : WithTop Γ) <
      addVal k Γ (((F.eval y : valuationSubring k Γ) : HahnField k Γ) +
        ((F.comp (Polynomial.X + Polynomial.C y)).coeff m : HahnField k Γ) *
          (singleOfNonneg k Γ δ c (le_of_lt hδpos) : HahnField k Γ) ^ m)) :
    (γ : WithTop Γ) <
      addVal k Γ (((F.eval (singleOfNonneg k Γ δ c (le_of_lt hδpos) + y) :
        valuationSubring k Γ) : HahnField k Γ)) := by
  let G : (valuationSubring k Γ)[X] := F.comp (Polynomial.X + Polynomial.C y)
  let t : valuationSubring k Γ := singleOfNonneg k Γ δ c (le_of_lt hδpos)
  have hcoeff0 : G.coeff 0 = F.eval y := by
    dsimp [G]
    rw [Polynomial.coeff_zero_eq_eval_zero, eval_comp_X_add_C]
    simp
  have hcoeff0' : (F.comp (Polynomial.X + Polynomial.C y)).coeff 0 = F.eval y := by
    simpa [G] using hcoeff0
  have hmain' : (γ : WithTop Γ) <
      addVal k Γ ((G.coeff 0 : HahnField k Γ) + (G.coeff m : HahnField k Γ) *
        (t : HahnField k Γ) ^ m) := by
    dsimp [G, t]
    simpa [hcoeff0'] using hmain
  have hG : (γ : WithTop Γ) <
      addVal k Γ ((G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
        (t : HahnField k Γ)) := by
    exact lt_addVal_eval_map_singleOfNonneg_of_const_main_improves
      k Γ (F := G) (m := m) (δ := δ) (γ := γ) (c := c)
      hm_pos hunit hδpos hc hδ (by
        intro j hjpos hjm
        dsimp [G] at hlower ⊢
        exact hlower j hjpos hjm) hmain'
  have hmap :
      (G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (t : HahnField k Γ) =
        ((G.eval t : valuationSubring k Γ) : HahnField k Γ) :=
    eval_map_algebraMap_eq_coe_eval k Γ G t
  have htranslate : G.eval t = F.eval (t + y) := by
    dsimp [G, t]
    exact eval_comp_X_add_C k Γ F y (singleOfNonneg k Γ δ c (le_of_lt hδpos))
  rw [hmap, htranslate] at hG
  simpa [t] using hG

/-- In the simple-cluster case, choose a one-term correction together with the exact current
evaluation valuation and the resulting strict improvement. -/
theorem exists_correction_improves_eval_at_of_one_cluster_with_value
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : (valuationSubring k Γ)[X]} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hne : F.eval y ≠ 0) :
    ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
      ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ δ = γ ∧
        addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
          (γ : WithTop Γ) ∧
          (γ : WithTop Γ) <
            addVal k Γ (((F.eval (singleOfNonneg k Γ δ c (le_of_lt hδpos) + y) :
              valuationSubring k Γ) : HahnField k Γ)) := by
  rcases exists_main_correction_improves_eval_at_of_cluster_with_value
    (k := k) (Γ := Γ) (F := F) (m := 1) (y := y)
    (by norm_num) (by norm_num) hsmall hunit hy hne with
    ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, hval, hmain⟩
  have hunit' : IsUnit ((F.comp (Polynomial.X + Polynomial.C y)).coeff 1) :=
    isUnit_coeff_comp_X_add_C_of_cluster_unit_of_mem_maximalIdeal k Γ hunit hy
  have himprove : (γ : WithTop Γ) <
      addVal k Γ (((F.eval (singleOfNonneg k Γ δ c (le_of_lt hδpos) + y) :
        valuationSubring k Γ) : HahnField k Γ)) := by
    exact lt_addVal_eval_add_singleOfNonneg_of_translated_const_main_improves
      (k := k) (Γ := Γ) (F := F) (m := 1) (y := y)
      (by norm_num) hunit' hδpos hcne hδ (by
        intro j hjpos hjlt
        omega) hmain
  refine ⟨γ, δ, c, hδpos, hγpos, hcne, ?_, hval, himprove⟩
  simpa using hδ

/-- A non-root simple-cluster approximation has a corrected maximal-ideal approximation together
with the current evaluation value and the valuation of the correction step. -/
theorem exists_next_approx_improves_eval_at_of_one_cluster_with_values
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : (valuationSubring k Γ)[X]} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hne : F.eval y ≠ 0) :
    ∃ y' : valuationSubring k Γ,
      y' ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
        ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
          ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ δ = γ ∧
            y' = singleOfNonneg k Γ δ c (le_of_lt hδpos) + y ∧
              addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
                (γ : WithTop Γ) ∧
                addVal k Γ ((y' - y : valuationSubring k Γ) : HahnField k Γ) =
                  (δ : WithTop Γ) ∧
                  (γ : WithTop Γ) <
                    addVal k Γ (((F.eval y' : valuationSubring k Γ) : HahnField k Γ)) := by
  rcases exists_correction_improves_eval_at_of_one_cluster_with_value
    k Γ hsmall hunit hy hne with
    ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, hval, himprove⟩
  let y' : valuationSubring k Γ := singleOfNonneg k Γ δ c (le_of_lt hδpos) + y
  have hy' : y' ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
    dsimp [y']
    simpa [add_comm] using add_singleOfNonneg_mem_maximalIdeal_of_mem_of_pos
      k Γ hy hδpos hcne
  have hstep : addVal k Γ ((y' - y : valuationSubring k Γ) : HahnField k Γ) =
      (δ : WithTop Γ) := by
    have hsub : (y' - y : valuationSubring k Γ) =
        singleOfNonneg k Γ δ c (le_of_lt hδpos) := by
      dsimp [y']
      abel
    rw [hsub]
    exact addVal_singleOfNonneg_of_ne k Γ (le_of_lt hδpos) hcne
  refine ⟨y', hy', γ, δ, c, hδpos, hγpos, hcne, hδ, rfl, hval, hstep, ?_⟩
  simpa [y'] using himprove

end HahnField

end

end HahnKaplanskyRealClosedness
