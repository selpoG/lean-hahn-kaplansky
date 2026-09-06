/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux.Support.Base

/-!
# Fixed-denominator Puiseux levels

This file packages the finite Puiseux levels `k((t^(1/n)))` as subfields of the ambient rational
Hahn field.  These levels are the pieces whose directed union is `Puiseux.Series k`.
-/

namespace HahnKaplanskyRealClosedness

namespace Puiseux

noncomputable section

variable (k : Type*) [Field k]

/-- The subring of Hahn series whose support lies in the fixed denominator lattice `(1 / n)ℤ`. -/
def fixedDenominatorSubring (n : ℕ+) : Subring (HahnField k ℚ) where
  carrier := {x | HasDenominatorSupport k n x}
  zero_mem' := hasDenominatorSupport_zero k n
  one_mem' := hasDenominatorSupport_one k n
  add_mem' := by
    intro x y hx hy
    exact hasDenominatorSupport_add k hx hy
  mul_mem' := by
    intro x y hx hy
    exact hasDenominatorSupport_mul k hx hy
  neg_mem' := by
    intro x hx
    exact hasDenominatorSupport_neg k hx

/-- The subfield of Hahn series whose support lies in the fixed denominator lattice `(1 / n)ℤ`. -/
def fixedDenominatorSubfield (n : ℕ+) : Subfield (HahnField k ℚ) where
  __ := fixedDenominatorSubring k n
  inv_mem' := by
    intro x hx
    exact hasDenominatorSupport_inv k hx

/-- The `n`-th finite Puiseux level, represented as a fixed-denominator subfield. -/
abbrev FixedDenominatorSeries (n : ℕ+) :=
  fixedDenominatorSubfield k n

theorem fixedDenominatorSubfield_le_subfield (n : ℕ+) :
    fixedDenominatorSubfield k n ≤ subfield k := by
  intro x hx
  exact ⟨n, hx⟩

theorem fixedDenominatorSubfield_le_mul_right (n n' : ℕ+) :
    fixedDenominatorSubfield k n ≤ fixedDenominatorSubfield k (n * n') := by
  intro x hx
  exact hasDenominatorSupport_mono_den k
    (fun q hq => hasDenominator_mul_right (n' := n') hq) hx

/-- Include a fixed-denominator level into the full Puiseux field. -/
def fixedDenominatorToSeries (n : ℕ+) :
    FixedDenominatorSeries k n →+* Series k :=
  Subfield.inclusion (fixedDenominatorSubfield_le_subfield k n)

/-- A finite family of Puiseux series has a common denominator for all supports. -/
theorem exists_common_denominator_finset {α : Type*} (s : Finset α) (f : α → Series k) :
    ∃ n : ℕ+,
      ∀ a ∈ s, ∀ q ∈ (ofLex (f a : HahnField k ℚ)).support, HasDenominator n q := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · refine ⟨1, ?_⟩
    intro a ha
    simp at ha
  · intro a s has ih
    rcases hasBoundedDenominatorSupport_coe k (f a) with ⟨na, hna⟩
    rcases ih with ⟨ns, hns⟩
    refine ⟨na * ns, ?_⟩
    intro b hb q hq
    rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact hasDenominator_mul_right (n' := ns) (hna q hq)
    · simpa [mul_comm] using
        (hasDenominator_mul_right (n' := na) (hns b hb q hq))

/-- A finite family of Puiseux series is contained in one fixed-denominator level. -/
theorem exists_fixedDenominatorSubfield_finset {α : Type*} (s : Finset α)
    (f : α → Series k) :
    ∃ n : ℕ+, ∀ a ∈ s, (f a : HahnField k ℚ) ∈ fixedDenominatorSubfield k n :=
  exists_common_denominator_finset k s f

/-- A finite family of bounded-denominator Hahn series has a common denominator. -/
theorem exists_common_denominatorSupport_finset_of_boundedSupport {α : Type*}
    (s : Finset α) {f : α → HahnField k ℚ}
    (hf : ∀ a ∈ s, HasBoundedDenominatorSupport k (f a)) :
    ∃ n : ℕ+, ∀ a ∈ s, HasDenominatorSupport k n (f a) := by
  classical
  revert f
  refine Finset.induction_on s ?empty ?insert
  · intro hf
    refine ⟨1, ?_⟩
    intro a ha
    simp at ha
  · intro a s has ih hf
    rcases hf a (by simp) with ⟨na, hna⟩
    rcases ih (by
      intro b hb
      exact hf b (by simp [hb])) with ⟨ns, hns⟩
    refine ⟨na * ns, ?_⟩
    intro b hb
    rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact hasDenominatorSupport_mono_den k
        (fun q hq => hasDenominator_mul_right (n' := ns) hq) hna
    · exact hasDenominatorSupport_mono_den k
        (fun q hq => by
          simpa [mul_comm] using (hasDenominator_mul_right (n' := na) hq)) (hns b hb)

theorem exists_common_denominatorSupport_polynomial_coeff_of_boundedSupport
    (P : Polynomial (HahnField k ℚ))
    (hP : ∀ i : ℕ, HasBoundedDenominatorSupport k (P.coeff i)) :
    ∃ n : ℕ+, ∀ i : ℕ, HasDenominatorSupport k n (P.coeff i) := by
  classical
  rcases exists_common_denominatorSupport_finset_of_boundedSupport
      k P.support (f := P.coeff) (by
        intro i _hi
        exact hP i) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro i
  by_cases hi : i ∈ P.support
  · exact hn i hi
  · have hcoeff : P.coeff i = 0 := Polynomial.notMem_support_iff.mp hi
    rw [hcoeff]
    exact hasDenominatorSupport_zero k n

end

end Puiseux

end HahnKaplanskyRealClosedness
