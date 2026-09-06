/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# Real closedness of the real numbers

This module supplies the `IsRealClosed` instance for `ℝ` used by the concrete
Puiseux smoke test.  The odd-degree root property is proved directly from the
eventual signs of a real polynomial at the two ends of the real line.
-/

namespace HahnKaplanskyRealClosedness

open Filter Polynomial Set

private theorem real_exists_isRoot_of_odd_natDegree {f : ℝ[X]} (hf : Odd f.natDegree) :
    ∃ x, f.IsRoot x := by
  have hnat : 0 < f.natDegree := hf.pos
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hnat
  have hcompdeg : 0 < (f.comp (-X)).degree := by
    rw [← natDegree_pos_iff_degree_pos]
    simpa [natDegree_comp] using hnat
  have hcomp_lc : (f.comp (-X)).leadingCoeff = -f.leadingCoeff := by
    rw [comp_neg_X_leadingCoeff_eq, hf.neg_one_pow]
    simp
  have hcomp_eval (x : ℝ) : (f.comp (-X)).eval x = f.eval (-x) := by
    simp
  rcases lt_or_ge f.leadingCoeff 0 with hlc | hlc
  · have hneg : ∀ᶠ x : ℝ in atTop, f.eval x < 0 :=
      (f.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlc.le).eventually_lt_atBot 0
    have hcomp_pos : ∀ᶠ x : ℝ in atTop, 0 < (f.comp (-X)).eval x :=
      ((f.comp (-X)).tendsto_atTop_of_leadingCoeff_nonneg hcompdeg
        (by rw [hcomp_lc]; exact neg_nonneg.mpr hlc.le)).eventually_gt_atTop 0
    obtain ⟨xn, hn⟩ := hneg.exists_forall_of_atTop
    obtain ⟨xp, hp⟩ := hcomp_pos.exists_forall_of_atTop
    let x := max (max xn xp) 0
    have hxn : xn ≤ x := by
      dsimp [x]
      exact (le_max_left _ _).trans (le_max_left _ _)
    have hxp : xp ≤ x := by
      dsimp [x]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have hx0 : 0 ≤ x := by
      dsimp [x]
      exact le_max_right _ _
    have hleft : 0 < f.eval (-x) := by
      rw [← hcomp_eval]
      exact hp x hxp
    have hright : f.eval x < 0 := hn x hxn
    obtain ⟨y, hy⟩ := (Set.mem_image ..).mp
      (intermediate_value_Icc' (neg_le_self hx0) f.continuous.continuousOn
        (show 0 ∈ Icc (f.eval x) (f.eval (-x)) by grind))
    exact ⟨y, hy.2⟩
  · have hpos : ∀ᶠ x : ℝ in atTop, 0 < f.eval x :=
      (f.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc).eventually_gt_atTop 0
    have hcomp_neg : ∀ᶠ x : ℝ in atTop, (f.comp (-X)).eval x < 0 :=
      ((f.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos hcompdeg
        (by rw [hcomp_lc]; exact neg_nonpos.mpr hlc)).eventually_lt_atBot 0
    obtain ⟨xp, hp⟩ := hpos.exists_forall_of_atTop
    obtain ⟨xn, hn⟩ := hcomp_neg.exists_forall_of_atTop
    let x := max (max xp xn) 0
    have hxp : xp ≤ x := by
      dsimp [x]
      exact (le_max_left _ _).trans (le_max_left _ _)
    have hxn : xn ≤ x := by
      dsimp [x]
      exact (le_max_right _ _).trans (le_max_left _ _)
    have hx0 : 0 ≤ x := by
      dsimp [x]
      exact le_max_right _ _
    have hleft : f.eval (-x) < 0 := by
      rw [← hcomp_eval]
      exact hn x hxn
    have hright : 0 < f.eval x := hp x hxp
    obtain ⟨y, hy⟩ := (Set.mem_image ..).mp
      (intermediate_value_Icc (neg_le_self hx0) f.continuous.continuousOn
        (show 0 ∈ Icc (f.eval (-x)) (f.eval x) by grind))
    exact ⟨y, hy.2⟩

noncomputable instance instIsRealClosedReal : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField (fun hx => (Real.isSquare_iff).2 hx)
    real_exists_isRoot_of_odd_natDegree

end HahnKaplanskyRealClosedness
