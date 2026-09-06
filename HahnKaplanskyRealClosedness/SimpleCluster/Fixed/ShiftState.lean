/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.SimpleCluster.Fixed.Chain.Terminal

/-!
# Finite terminal shifts and states
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

noncomputable def KOddClusterFixedStepTerminalFromData.toShiftedSameTerminalObstructionData
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ} {start : valuationSubring k Γ}
    (T : KOddClusterFixedStepTerminalFromData k Γ F m start)
    (hbranch : KTranslatedSameMultiplicityZeroBranch k Γ F m) :
    KSameMultiplicityFixedStepTerminalObstructionData k Γ
      (F.comp (Polynomial.X +
        Polynomial.C (algebraMap (valuationSubring k Γ) (HahnField k Γ) start))) m :=
  { branch := hbranch.comp_X_add_C k Γ start (T.chain.start_mem k Γ)
    terminal := T.toShiftedTerminalObstructionAboveOneData k Γ }

namespace KSameMultiplicityFixedStepTerminalObstructionData

/-- A terminal obstruction reached after finitely many shifts, together with the transport that
returns any root of the current shifted polynomial to a root of the original polynomial. -/
structure KSameMultiplicityFixedStepTerminalShiftState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (F0 : Polynomial (HahnField k Γ)) (m : ℕ) where
  current : Polynomial (HahnField k Γ)
  shift : valuationSubring k Γ
  shift_mem : shift ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)
  current_eq :
    current =
      F0.comp (Polynomial.X + Polynomial.C
        (algebraMap (valuationSubring k Γ) (HahnField k Γ) shift))
  terminal : KSameMultiplicityFixedStepTerminalObstructionData k Γ current m
  root_transport : PositiveHahnRoot k Γ current → PositiveHahnRoot k Γ F0

noncomputable def KSameMultiplicityFixedStepTerminalShiftState.initial
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ F m where
  current := F
  shift := 0
  shift_mem := Ideal.zero_mem (IsLocalRing.maximalIdeal (valuationSubring k Γ))
  current_eq := by simp
  terminal := T
  root_transport := id

noncomputable def advanceFirstSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ F m where
  current := F.comp (Polynomial.X + Polynomial.C
    (algebraMap (valuationSubring k Γ) (HahnField k Γ)
      (T.terminal.chain.source 1).1))
  shift := (T.terminal.chain.source 1).1
  shift_mem := (T.terminal.chain.source 1).2
  current_eq := rfl
  terminal :=
    (T.terminal.tailFrom k Γ 1).toShiftedSameTerminalObstructionData k Γ T.branch
  root_transport := PositiveHahnRoot.of_comp_X_add_C k Γ
    (T.terminal.chain.source 1).2

@[simp] theorem advanceFirstSource_shift
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m) :
    (T.advanceFirstSource k Γ).shift = (T.terminal.chain.source 1).1 :=
  rfl

theorem advanceFirstSource_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m) :
    (T.advanceFirstSource k Γ).terminal.terminal.chain.stepValue k Γ 0 =
      T.terminal.chain.stepValue k Γ 1 := by
  change
    ((T.terminal.tailFrom k Γ 1).chain.toShiftedChainData k Γ).stepValue k Γ 0 = _
  rw [KOddClusterFixedStepChainFromData.toShiftedChainData_stepValue]
  exact T.terminal.chain.tailFrom_stepValue k Γ 1 0

theorem firstStep_lt_advanceFirstSource_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (T : KSameMultiplicityFixedStepTerminalObstructionData k Γ F m) :
    T.terminal.chain.stepValue k Γ 0 <
      (T.advanceFirstSource k Γ).terminal.terminal.chain.stepValue k Γ 0 := by
  rw [T.advanceFirstSource_firstStep k Γ]
  simpa using T.terminal.chain.stepValue_lt_succ k Γ 0

/-- Compose a terminal shift state over `F0` with a terminal shift state over its current
polynomial.  This is the data-level operation used by iterated flattened-tail continuation. -/
noncomputable def KSameMultiplicityFixedStepTerminalShiftState.trans
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (R : KSameMultiplicityFixedStepTerminalShiftState k Γ S.current m) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m := by
  cases S with
  | mk current shift shift_mem current_eq terminal root_transport =>
      cases current_eq
      cases R with
      | mk currentR shiftR shiftR_mem currentR_eq terminalR root_transportR =>
          refine {
            current := currentR
            shift := shift + shiftR
            shift_mem :=
              (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem
                shift_mem shiftR_mem
            current_eq := ?_
            terminal := terminalR
            root_transport := fun hroot => root_transport (root_transportR hroot) }
          rw [currentR_eq, Polynomial.comp_assoc]
          congr 1
          ext i
          simp [add_comm, add_left_comm]

theorem KSameMultiplicityFixedStepTerminalShiftState.trans_terminal_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (R : KSameMultiplicityFixedStepTerminalShiftState k Γ S.current m) (n : ℕ) :
    (S.trans k Γ R).terminal.terminal.chain.stepValue k Γ n =
      R.terminal.terminal.chain.stepValue k Γ n := by
  cases S with
  | mk current shift shift_mem current_eq terminal root_transport =>
      cases current_eq
      cases R with
      | mk currentR shiftR shiftR_mem currentR_eq terminalR root_transportR =>
          cases currentR_eq
          rfl

theorem KSameMultiplicityFixedStepTerminalShiftState.trans_shift
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (R : KSameMultiplicityFixedStepTerminalShiftState k Γ S.current m) :
    (S.trans k Γ R).shift = S.shift + R.shift := by
  cases S with
  | mk current shift shift_mem current_eq terminal root_transport =>
      cases current_eq
      cases R
      simp [KSameMultiplicityFixedStepTerminalShiftState.trans]

noncomputable def KSameMultiplicityFixedStepTerminalShiftState.advanceFirstSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m) :
    KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m :=
  S.trans k Γ (S.terminal.advanceFirstSource k Γ)

theorem KSameMultiplicityFixedStepTerminalShiftState.firstStep_lt_advanceFirstSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m) :
    S.terminal.terminal.chain.stepValue k Γ 0 <
      (S.advanceFirstSource k Γ).terminal.terminal.chain.stepValue k Γ 0 := by
  rw [KSameMultiplicityFixedStepTerminalShiftState.advanceFirstSource,
    S.trans_terminal_stepValue k Γ]
  exact S.terminal.firstStep_lt_advanceFirstSource_firstStep k Γ

theorem KSameMultiplicityFixedStepTerminalShiftState.lift_eval_eq_current_eval
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (x : valuationSubring k Γ) :
    ((S.terminal.terminal.chain.liftData.lift.eval x : valuationSubring k Γ) :
        HahnField k Γ) =
      S.current.eval (x : HahnField k Γ) := by
  calc
    ((S.terminal.terminal.chain.liftData.lift.eval x : valuationSubring k Γ) :
        HahnField k Γ) =
        (S.terminal.terminal.chain.liftData.lift.map
          (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            (x : HahnField k Γ) := by
      rw [eval_map_algebraMap_eq_coe_eval]
    _ = S.current.eval (x : HahnField k Γ) := by
      rw [S.terminal.terminal.chain.liftData.map_eq]

theorem KSameMultiplicityFixedStepTerminalShiftState.current_eval_eq_original_shift_eval
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (x : valuationSubring k Γ) :
    S.current.eval (x : HahnField k Γ) =
      F0.eval ((x : HahnField k Γ) +
        algebraMap (valuationSubring k Γ) (HahnField k Γ) S.shift) := by
  rw [S.current_eq]
  simp [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

theorem KSameMultiplicityFixedStepTerminalShiftState.lift_eval_eq_original_shift_eval
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (x : valuationSubring k Γ) :
    ((S.terminal.terminal.chain.liftData.lift.eval x : valuationSubring k Γ) :
        HahnField k Γ) =
      F0.eval ((x : HahnField k Γ) +
        algebraMap (valuationSubring k Γ) (HahnField k Γ) S.shift) := by
  rw [S.lift_eval_eq_current_eval k Γ x]
  exact S.current_eval_eq_original_shift_eval k Γ x

theorem KSameMultiplicityFixedStepTerminalShiftState.shift_eval_addVal_eq_nsmul_firstStep
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m) :
    addVal k Γ (F0.eval (S.shift : HahnField k Γ)) =
      (m • S.terminal.terminal.chain.stepValue k Γ 0 : WithTop Γ) := by
  let C := S.terminal.terminal.chain
  have hsource := C.source_eval_addVal_eq_nsmul_stepValue k Γ 0
  have horig :
      addVal k Γ
          ((C.liftData.lift.map
            (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
              ((C.source 0).1 : HahnField k Γ)) =
        addVal k Γ
          (F0.eval (((C.source 0).1 : HahnField k Γ) +
            algebraMap (valuationSubring k Γ) (HahnField k Γ) S.shift)) := by
    rw [eval_map_algebraMap_eq_coe_eval]
    exact congrArg (addVal k Γ)
      (S.lift_eval_eq_original_shift_eval k Γ (C.source 0).1)
  rw [horig] at hsource
  simpa [C.start_source, Algebra.algebraMap_ofSubsemiring_apply] using hsource

theorem KSameMultiplicityFixedStepTerminalShiftState.no_positiveRoot_current
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F0 : Polynomial (HahnField k Γ)} {m : ℕ}
    (S : KSameMultiplicityFixedStepTerminalShiftState k Γ F0 m)
    (hno : ¬ PositiveHahnRoot k Γ F0) :
    ¬ PositiveHahnRoot k Γ S.current :=
  fun hroot => hno (S.root_transport hroot)

end KSameMultiplicityFixedStepTerminalObstructionData

end HahnField

end

end HahnKaplanskyRealClosedness
