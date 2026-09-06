/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.SimpleCluster.Fixed.ShiftState

/-!
# Generic support and polynomial-evaluation tools for ordinal prefixes

This module contains the reusable Hahn-series support, summable-power, and coefficient-finiteness
lemmas used by the fixed-lift ordinal-prefix proof.  It deliberately does not depend on a terminal
state or on the root-producing endpoint.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

namespace OrdinalSupport

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem iUnion_hahnSeries_support_isPWO_of_pairwise_ordered
    {I : Type*} [LinearOrder I] [WellFoundedLT I]
    (B : I → HahnSeries Γ k)
    (hordered : ∀ {i j : I}, i < j → ∀ {γ δ : Γ},
      γ ∈ (B i).support → δ ∈ (B j).support → γ < δ) :
    (⋃ i : I, (B i).support).IsPWO := by
  classical
  let U : Set Γ := ⋃ i : I, (B i).support
  rw [Set.isPWO_iff_isWF]
  change U.IsWF
  rw [Set.IsWF, Set.wellFoundedOn_iff, WellFounded.wellFounded_iff_has_min]
  intro t ht
  by_cases hUt : (U ∩ t).Nonempty
  · let Iset : Set I := {i | ∃ γ : Γ, γ ∈ t ∧ γ ∈ (B i).support}
    have hInon : Iset.Nonempty := by
      rcases hUt with ⟨γ, hγU, hγt⟩
      rcases Set.mem_iUnion.mp hγU with ⟨i, hi⟩
      exact ⟨i, ⟨γ, hγt, hi⟩⟩
    let hIwf : Iset.IsWF := Set.IsWF.of_wellFoundedLT Iset
    let i₀ : I := hIwf.min hInon
    have hi₀mem : i₀ ∈ Iset := hIwf.min_mem hInon
    rcases hi₀mem with ⟨γ₀, hγ₀t, hγ₀supp⟩
    let fiber : Set Γ := (B i₀).support ∩ t
    have hfiberWF : fiber.IsWF := (B i₀).isPWO_support.isWF.mono (by
      intro γ hγ
      exact hγ.1)
    have hfiberNonempty : fiber.Nonempty := ⟨γ₀, hγ₀supp, hγ₀t⟩
    let μ : Γ := hfiberWF.min hfiberNonempty
    have hμFiber : μ ∈ fiber := hfiberWF.min_mem hfiberNonempty
    refine ⟨μ, hμFiber.2, ?_⟩
    intro x hxt hx
    rcases hx with ⟨hxμ, hxU, _hμU⟩
    rcases Set.mem_iUnion.mp hxU with ⟨j, hxj⟩
    have hjmem : j ∈ Iset := ⟨x, hxt, hxj⟩
    rcases lt_trichotomy j i₀ with hji | rfl | hij
    · exact (hIwf.not_lt_min hInon hjmem) hji
    · exact (hfiberWF.not_lt_min hfiberNonempty ⟨hxj, hxt⟩) hxμ
    · exact (lt_asymm hxμ (hordered hij hμFiber.1 hxj)).elim
  · rcases ht with ⟨μ, hμt⟩
    refine ⟨μ, hμt, ?_⟩
    intro _x _hxt hx
    exact hUt ⟨μ, hx.2.2, hμt⟩

inductive HahnSummablePowerIndex (I : Type u) : ℕ → Type u
  | nil : HahnSummablePowerIndex I 0
  | cons : I → HahnSummablePowerIndex I n → HahnSummablePowerIndex I (n + 1)

def HahnSummablePowerIndex.consEquiv (I : Type u) (n : ℕ) :
    I × HahnSummablePowerIndex I n ≃ HahnSummablePowerIndex I (n + 1) where
  toFun i := .cons i.1 i.2
  invFun i := match i with | .cons a t => (a, t)
  left_inv _ := rfl
  right_inv i := by cases i; rfl

@[simp] theorem HahnSummablePowerIndex.consEquiv_symm_cons
    (a : I) (t : HahnSummablePowerIndex I n) :
    (HahnSummablePowerIndex.consEquiv I n).symm
        (HahnSummablePowerIndex.cons a t) = (a, t) :=
  rfl

noncomputable def HahnSummablePowerIndex.components
    {I : Type*} : HahnSummablePowerIndex (Option I) n → Finset I
  | .nil => ∅
  | .cons none t => t.components
  | .cons (some a) t => by
      classical
      exact insert a t.components

/-- The summable product family whose sum is the corresponding power of the original `hsum`. -/
noncomputable def HahnSummablePowerFamily
  {I : Type*} (A : HahnSeries.SummableFamily Γ k I) :
    (n : ℕ) → HahnSeries.SummableFamily Γ k (HahnSummablePowerIndex I n)
  | 0 => by
      classical
      exact HahnSeries.SummableFamily.single HahnSummablePowerIndex.nil 1
  | n + 1 =>
      (A.mul (HahnSummablePowerFamily A n)).Equiv
        (HahnSummablePowerIndex.consEquiv I n)

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem HahnSummablePowerFamily_hsum
    {I : Type*} (A : HahnSeries.SummableFamily Γ k I) (n : ℕ) :
    (HahnSummablePowerFamily (k := k) (Γ := Γ) A n).hsum = A.hsum ^ n := by
  induction n with
  | zero => simp [HahnSummablePowerFamily]
  | succ n ih =>
      rw [HahnSummablePowerFamily, HahnSeries.SummableFamily.hsum_equiv,
        HahnSeries.SummableFamily.hsum_mul, ih, pow_succ']

noncomputable def HahnSummablePowerTrunc
    {I : Type*} (A : HahnSeries.SummableFamily Γ k (Option I)) (p : I → Prop)
    [DecidablePred p] :
    HahnSeries.SummableFamily Γ k (Option I) := by
  classical
  exact HahnSeries.SummableFamily.smulFamily
    (fun i => if i.elim True p then (1 : k) else 0) A

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem HahnSummablePowerFamily_predTrunc_apply
    {I : Type*} (A : HahnSeries.SummableFamily Γ k (Option I)) (p : I → Prop)
    [DecidablePred p]
    (n : ℕ) (i : HahnSummablePowerIndex (Option I) n) :
    HahnSummablePowerFamily (k := k) (Γ := Γ)
        (HahnSummablePowerTrunc (k := k) (Γ := Γ) A p) n i =
      if ∀ a ∈ i.components, p a then
        HahnSummablePowerFamily (k := k) (Γ := Γ) A n i else 0 := by
  classical
  induction n with
  | zero =>
      cases i
      simp [HahnSummablePowerFamily, HahnSummablePowerIndex.components]
  | succ n ih =>
      cases i with
      | cons a t =>
          rw [HahnSummablePowerFamily, HahnSummablePowerFamily]
          simp only [HahnSeries.SummableFamily.Equiv_toFun,
            HahnSummablePowerIndex.consEquiv_symm_cons,
            HahnSeries.SummableFamily.mul_toFun]
          rw [ih t]
          cases a with
          | none =>
              simp [HahnSummablePowerTrunc,
                HahnSummablePowerIndex.components]
              rfl
          | some a =>
              by_cases ht : ∀ b ∈ t.components, p b
              · by_cases ha : p a <;>
                  simp [HahnSummablePowerTrunc,
                    HahnSummablePowerIndex.components, ha]
              · simp [HahnSummablePowerTrunc,
                  HahnSummablePowerIndex.components, ht]

noncomputable def HahnSummablePowerCoeffSupport
    {I : Type*} (A : HahnSeries.SummableFamily Γ k (Option I))
    (c : HahnSeries Γ k) (n : ℕ) (γ : Γ) : Finset I :=
  by
    classical
    let C : HahnSeries.SummableFamily Γ k Unit :=
      HahnSeries.SummableFamily.single () c
    let P := HahnSummablePowerFamily (k := k) (Γ := Γ) A n
    let Q := C.mul P
    exact (Q.coeff γ).support.biUnion (fun u => u.2.components)

noncomputable def HahnSummableEvalCoeffSupport
    {I : Type*} (A : HahnSeries.SummableFamily Γ k (Option I))
    (F : Polynomial (HahnSeries Γ k)) (γ : Γ) : Finset I :=
  by
    classical
    exact (Finset.range (F.natDegree + 1)).biUnion
      (fun i => HahnSummablePowerCoeffSupport (k := k) (Γ := Γ) A
        (F.coeff i) i γ)

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem HahnSummableFamily.mul_pow_coeff_eq_predTrunc_of_support
    {I : Type*} (A : HahnSeries.SummableFamily Γ k (Option I)) (p : I → Prop)
    [DecidablePred p]
    (c : HahnSeries Γ k) (n : ℕ) (γ : Γ)
    (hU : ∀ a ∈ HahnSummablePowerCoeffSupport (k := k) (Γ := Γ) A c n γ, p a) :
      (c * A.hsum ^ n).coeff γ =
        (c * (HahnSummablePowerTrunc (k := k) (Γ := Γ) A p).hsum ^ n).coeff γ := by
  classical
  let C : HahnSeries.SummableFamily Γ k Unit :=
    HahnSeries.SummableFamily.single () c
  let P := HahnSummablePowerFamily (k := k) (Γ := Γ) A n
  let Q := C.mul P
  rw [← HahnSeries.SummableFamily.hsum_single () c,
    ← HahnSummablePowerFamily_hsum (k := k) (Γ := Γ) A n,
    ← HahnSeries.SummableFamily.hsum_mul,
    ← HahnSeries.SummableFamily.hsum_single () c,
    ← HahnSummablePowerFamily_hsum (k := k) (Γ := Γ)
      (HahnSummablePowerTrunc (k := k) (Γ := Γ) A p) n,
    ← HahnSeries.SummableFamily.hsum_mul]
  simp only [HahnSeries.SummableFamily.coeff_hsum]
  apply finsum_congr
  rintro ⟨u, i⟩
  simp only [HahnSeries.SummableFamily.mul_toFun]
  rw [HahnSummablePowerFamily_predTrunc_apply (k := k) (Γ := Γ)]
  by_cases hi : ∀ a ∈ i.components, p a
  · rw [if_pos hi]
  · have hbad : ∃ a ∈ i.components, ¬p a := by
      push Not at hi
      exact hi
    have hzero : (C u * P i).coeff γ = 0 := by
      by_contra hne
      have himem : (u, i) ∈ (Q.coeff γ).support := by
        simpa [HahnSeries.SummableFamily.coeff_def, Q] using hne
      rcases hbad with ⟨a, ha, hpa⟩
      exact hpa (hU a (by
        simpa [HahnSummablePowerCoeffSupport, C, P, Q] using
          (Finset.mem_biUnion.mpr
            (show ∃ x ∈ (Q.coeff γ).support, a ∈ x.2.components from
              ⟨(u, i), himem, ha⟩))))
    simpa [hi, C, P] using hzero

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem HahnSummableFamily.eval_coeff_eq_predTrunc_of_support
    {I : Type*} (A : HahnSeries.SummableFamily Γ k (Option I)) (p : I → Prop)
    [DecidablePred p]
    (F : Polynomial (HahnSeries Γ k)) (γ : Γ)
    (hU : ∀ a ∈ HahnSummableEvalCoeffSupport (k := k) (Γ := Γ) A F γ, p a) :
      (F.eval A.hsum).coeff γ =
        (F.eval
          (HahnSummablePowerTrunc (k := k) (Γ := Γ) A p).hsum).coeff γ := by
  classical
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range,
    HahnSeries.coeff_sum, HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply HahnSummableFamily.mul_pow_coeff_eq_predTrunc_of_support
    (k := k) (Γ := Γ) A p (F.coeff i) i γ
  intro a ha
  exact hU a (by
    simpa [HahnSummableEvalCoeffSupport] using
      (Finset.mem_biUnion.mpr ⟨i, hi, ha⟩))

/-- The canonical ring homomorphism from the Hahn field to its Hahn-series representation. -/
def ofLexRingHom : HahnField k Γ →+* HahnSeries Γ k where
  toFun := ofLex
  map_zero' := ofLex_zero
  map_one' := ofLex_one
  map_add' := ofLex_add
  map_mul' := ofLex_mul

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem ofLexRingHom_eval (F : Polynomial (HahnField k Γ)) (x : HahnField k Γ) :
    (F.map (ofLexRingHom (k := k) (Γ := Γ))).eval (ofLex x) = ofLex (F.eval x) := by
  rw [Polynomial.eval_map]
  change F.eval₂ (ofLexRingHom (k := k) (Γ := Γ))
      (ofLexRingHom (k := k) (Γ := Γ) x) =
    ofLexRingHom (k := k) (Γ := Γ) (F.eval x)
  exact Polynomial.eval₂_at_apply (ofLexRingHom (k := k) (Γ := Γ)) x

end OrdinalSupport

end HahnField

end

end HahnKaplanskyRealClosedness
