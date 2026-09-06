/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.SimpleCluster.Fixed.Chain.Core

/-!
# Terminal obstruction and same-multiplicity consumers
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The bounded fixed-step obstruction left after the unbounded fixed correction branch has
been closed.  This is the above-one analogue of an omega terminal obstruction, but expressed in
the coherent fixed-lift step chain used for `m > 1`. -/
structure KOddClusterFixedStepTerminalObstructionAboveOneData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (F : Polynomial (HahnField k Γ)) (m : ℕ) where
  chain : KOddClusterFixedStepChainFromData k Γ F m 0
  bddAbove_stepValue : BddAbove (Set.range (chain.stepValue k Γ))

noncomputable def KOddClusterFixedStepTerminalObstructionAboveOneData.tailFrom
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (T : KOddClusterFixedStepTerminalObstructionAboveOneData k Γ F m) (n : ℕ) :
    KOddClusterFixedStepTerminalFromData k Γ F m (T.chain.source n).1 where
  chain := T.chain.tailFrom k Γ n
  bddAbove_stepValue := by
    rcases T.bddAbove_stepValue with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    rintro δ ⟨j, rfl⟩
    rw [T.chain.tailFrom_stepValue k Γ n j]
    exact hγ ⟨n + j, rfl⟩

noncomputable def KOddClusterFixedStepTerminalFromData.toShiftedTerminalObstructionAboveOneData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (T : KOddClusterFixedStepTerminalFromData k Γ F m start) :
    KOddClusterFixedStepTerminalObstructionAboveOneData k Γ
      (F.comp (Polynomial.X +
        Polynomial.C (algebraMap (valuationSubring k Γ) (HahnField k Γ) start))) m :=
  { chain := T.chain.toShiftedChainData k Γ
    bddAbove_stepValue := by
      rcases T.bddAbove_stepValue with ⟨γ, hγ⟩
      refine ⟨γ, ?_⟩
      intro δ hδ
      rcases hδ with ⟨n, rfl⟩
      rw [T.chain.toShiftedChainData_stepValue k Γ n]
      exact hγ ⟨n, rfl⟩ }

structure KSameMultiplicityFixedStepTerminalObstructionData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (F : Polynomial (HahnField k Γ)) (m : ℕ) where
  branch : KTranslatedSameMultiplicityZeroBranch k Γ F m
  terminal : KOddClusterFixedStepTerminalObstructionAboveOneData k Γ F m

theorem exists_sameTerminalObstruction_of_withRootBelow_no_positiveRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (hstep : KSameMultiplicityRootOrStepWithRootBelow k Γ)
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (hbelow : KOddClusterRootBelow k Γ m)
    (hno : ¬ PositiveHahnRoot k Γ F)
    (hbranch : KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    Nonempty (KSameMultiplicityFixedStepTerminalObstructionData k Γ F m) := by
  rcases hstep hbelow hbranch with ⟨D, hD⟩
  let U : ℕ →
      {A : valuationSubring k Γ // A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)} :=
    Nat.rec
      ⟨0, Ideal.zero_mem (IsLocalRing.maximalIdeal (valuationSubring k Γ))⟩
      (fun _ S =>
        let hnext : ∃ A' : valuationSubring k Γ, OddClusterStep k Γ D.lift m S.1 A' := by
          rcases hD S.1 S.2 with hroot | hnext
          · exact False.elim (hno hroot)
          · exact hnext
        ⟨Classical.choose hnext, (Classical.choose_spec hnext).mem_maximalIdeal⟩)
  let C : KOddClusterFixedStepChainFromData k Γ F m 0 :=
    { one_lt := hbranch.one_lt
      liftData := D
      source := U
      start_source := rfl
      step := by
        intro n
        dsimp [U]
        exact Classical.choose_spec _ }
  rcases C.candidate_isRoot_map_or_bddAbove_stepValue k Γ with hroot | hbdd
  · exact False.elim (hno (C.positiveHahnRoot_of_candidate_isRoot_map k Γ hroot))
  · exact ⟨
      { branch := hbranch
        terminal := { chain := C, bddAbove_stepValue := hbdd } }⟩

end HahnField

end

end HahnKaplanskyRealClosedness
