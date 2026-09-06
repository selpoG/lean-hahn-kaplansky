/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.SimpleCluster.Core

/-!
# Bounded omega blocks for simple-cluster correction chains
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- One bounded omega-block in the simple-cluster process, starting at `A` and ending at `A'`.
The block first runs the natural correction process for the translated polynomial `F(X + A)`.
If the natural block has bounded step values and its omega limit is still not a root, one more
packaged `SimpleClusterStep` for `F` moves from that omega limit to `A'`. -/
def SimpleClusterOmegaBlock
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (F : Polynomial (valuationSubring k Γ)) (A A' : valuationSubring k Γ) : Prop :=
  A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
    ∃ hsmallA : ∀ i, i < 1 →
        (F.comp (Polynomial.X + Polynomial.C A)).coeff i ∈
          IsLocalRing.maximalIdeal (valuationSubring k Γ),
      ∃ hunitA : IsUnit ((F.comp (Polynomial.X + Polynomial.C A)).coeff 1),
        ∃ hnoroot : ∀ n : ℕ,
            ¬ (F.comp (Polynomial.X + Polynomial.C A)).IsRoot
              (simpleClusterApproxOfOneCluster k Γ hsmallA hunitA n),
          BddAbove
            (Set.range
              (simpleClusterApproxStepValueOfNoRoot k Γ hsmallA hunitA hnoroot)) ∧
            SimpleClusterStep k Γ F
              (simpleClusterCorrectionValuationSubringOfNoRoot
                k Γ hsmallA hunitA hnoroot + A) A'

theorem SimpleClusterOmegaBlock.mem_end
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    A' ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rcases hblock.2 with ⟨hsmallA, hunitA, hnoroot, hbdd, hstep⟩
  exact hstep.1

theorem SimpleClusterOmegaBlock.translatedSmall
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    ∀ i, i < 1 →
      (F.comp (Polynomial.X + Polynomial.C A)).coeff i ∈
        IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  Classical.choose hblock.2

theorem SimpleClusterOmegaBlock.translatedUnit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    IsUnit ((F.comp (Polynomial.X + Polynomial.C A)).coeff 1) :=
  Classical.choose (Classical.choose_spec hblock.2)

theorem SimpleClusterOmegaBlock.translatedNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    ∀ n : ℕ,
      ¬ (F.comp (Polynomial.X + Polynomial.C A)).IsRoot
        (simpleClusterApproxOfOneCluster k Γ
          (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
          (SimpleClusterOmegaBlock.translatedUnit k Γ hblock) n) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec hblock.2))

/-- The explicit omega-limit source inside a bounded omega-block. -/
noncomputable def SimpleClusterOmegaBlock.limitSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    valuationSubring k Γ :=
  simpleClusterCorrectionValuationSubringOfNoRoot k Γ
    (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
    (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
    (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock) + A

theorem SimpleClusterOmegaBlock.limitSource_mem
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    SimpleClusterOmegaBlock.limitSource k Γ hblock ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  exact (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem
    (simpleClusterCorrectionValuationSubringOfNoRoot_mem_maximalIdeal
      k Γ
      (SimpleClusterOmegaBlock.translatedSmall k Γ hblock)
      (SimpleClusterOmegaBlock.translatedUnit k Γ hblock)
      (SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock))
    hblock.1

theorem SimpleClusterOmegaBlock.limitSource_step
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    SimpleClusterStep k Γ F (SimpleClusterOmegaBlock.limitSource k Γ hblock) A' :=
  (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec hblock.2))).2

/-- The omega-limit source of a bounded block is a rootless state, so it can start the next
block-level successor step. -/
noncomputable def SimpleClusterOmegaBlock.limitSourceState
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    OneClusterState k Γ F where
  source := SimpleClusterOmegaBlock.limitSource k Γ hblock
  source_mem := SimpleClusterOmegaBlock.limitSource_mem k Γ hblock
  not_root := (SimpleClusterOmegaBlock.limitSource_step k Γ hblock).source_not_root

theorem SimpleClusterOmegaBlock.addVal_eval_start_le_limitSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    addVal k Γ ((F.eval A : valuationSubring k Γ) : HahnField k Γ) ≤
      addVal k Γ
        ((F.eval (SimpleClusterOmegaBlock.limitSource k Γ hblock) :
          valuationSubring k Γ) : HahnField k Γ) := by
  let G : Polynomial (valuationSubring k Γ) := F.comp (Polynomial.X + Polynomial.C A)
  let hsmallA := SimpleClusterOmegaBlock.translatedSmall k Γ hblock
  let hunitA := SimpleClusterOmegaBlock.translatedUnit k Γ hblock
  let hnoroot := SimpleClusterOmegaBlock.translatedNoRoot k Γ hblock
  have hstart :
      addVal k Γ ((F.eval A : valuationSubring k Γ) : HahnField k Γ) =
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmallA hunitA hnoroot 0 :
          WithTop Γ) := by
    have hG :
        addVal k Γ ((G.eval (0 : valuationSubring k Γ) : valuationSubring k Γ) :
            HahnField k Γ) =
          (simpleClusterApproxStepValueOfNoRoot k Γ hsmallA hunitA hnoroot 0 :
            WithTop Γ) := by
      have hG' := simpleClusterApprox_addVal_eval_eq_evalValue_of_no_root
        k Γ hsmallA hunitA hnoroot 0
      rw [← simpleClusterApprox_stepValue_eq_evalValue_of_no_root
        k Γ hsmallA hunitA hnoroot 0] at hG'
      simpa [G, simpleClusterApproxOfOneCluster] using hG'
    simpa [G, eval_comp_X_add_C] using hG
  have hlimit :
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmallA hunitA hnoroot 0 :
        WithTop Γ) ≤
        addVal k Γ
          ((F.eval (SimpleClusterOmegaBlock.limitSource k Γ hblock) :
            valuationSubring k Γ) : HahnField k Γ) := by
    have hG :
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmallA hunitA hnoroot 0 :
          WithTop Γ) ≤
          addVal k Γ
            ((G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
              (simpleClusterCorrectionValuationSubringOfNoRoot
                k Γ hsmallA hunitA hnoroot : HahnField k Γ)) := by
      simpa [G] using
        simpleClusterCorrection_eval_addVal_ge_stepValue
          k Γ hsmallA hunitA hnoroot 0
    rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) G
      (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmallA hunitA hnoroot)] at hG
    simpa [G, SimpleClusterOmegaBlock.limitSource, hsmallA, hunitA, hnoroot,
      eval_comp_X_add_C] using hG
  exact hstart.trans_le hlimit

theorem SimpleClusterOmegaBlock.exists_terminal_step
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {A A' : valuationSubring k Γ}
    (hblock : SimpleClusterOmegaBlock k Γ F A A') :
    ∃ L : valuationSubring k Γ,
      L ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
        SimpleClusterStep k Γ F L A' := by
  rcases hblock with ⟨hA, hsmallA, hunitA, hnoroot, hbdd, hstep⟩
  refine ⟨simpleClusterCorrectionValuationSubringOfNoRoot
    k Γ hsmallA hunitA hnoroot + A, ?_, hstep⟩
  exact (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem
    (simpleClusterCorrectionValuationSubringOfNoRoot_mem_maximalIdeal
      k Γ hsmallA hunitA hnoroot) hA

theorem exists_maximalIdeal_root_or_exists_simpleClusterOmegaBlock_at_start
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) {A : valuationSubring k Γ}
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    (∃ y : valuationSubring k Γ,
      y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y) ∨
      ∃ A' : valuationSubring k Γ,
        SimpleClusterOmegaBlock k Γ F A A' := by
  rcases exists_maximalIdeal_root_or_bddAbove_step_at_start
      k Γ hsmall hunit hA with hroot | hblock
  · left
    exact hroot
  · right
    rcases hblock with ⟨hsmallA, hunitA, hnoroot, hbdd, A', hstep⟩
    exact ⟨A', hA, hsmallA, hunitA, hnoroot, hbdd, hstep⟩

/-- A natural-number chain of bounded omega-blocks. This is not yet the final transfinite
iteration, but it isolates the successor invariant that the ordinal version will reuse. -/
def SimpleClusterOmegaChain
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    (F : Polynomial (valuationSubring k Γ)) (U : ℕ → valuationSubring k Γ) : Prop :=
  U 0 ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
    ∀ n : ℕ, SimpleClusterOmegaBlock k Γ F (U n) (U (n + 1))

theorem SimpleClusterOmegaChain.mem_zero
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) :
    U 0 ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  hchain.1

theorem SimpleClusterOmegaChain.block
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    SimpleClusterOmegaBlock k Γ F (U n) (U (n + 1)) :=
  hchain.2 n

theorem SimpleClusterOmegaChain.addVal_eval_le_limitSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    addVal k Γ ((F.eval (U n) : valuationSubring k Γ) : HahnField k Γ) ≤
      addVal k Γ
        ((F.eval (SimpleClusterOmegaBlock.limitSource k Γ
          (SimpleClusterOmegaChain.block k Γ hchain n)) :
          valuationSubring k Γ) : HahnField k Γ) :=
  SimpleClusterOmegaBlock.addVal_eval_start_le_limitSource k Γ
    (SimpleClusterOmegaChain.block k Γ hchain n)

noncomputable def SimpleClusterOmegaChain.limitSource
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    valuationSubring k Γ :=
  SimpleClusterOmegaBlock.limitSource k Γ (SimpleClusterOmegaChain.block k Γ hchain n)

theorem SimpleClusterOmegaChain.limitSource_mem
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    SimpleClusterOmegaChain.limitSource k Γ hchain n ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  SimpleClusterOmegaBlock.limitSource_mem k Γ (SimpleClusterOmegaChain.block k Γ hchain n)

theorem SimpleClusterOmegaChain.limitSource_step
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    SimpleClusterStep k Γ F
      (SimpleClusterOmegaChain.limitSource k Γ hchain n) (U (n + 1)) :=
  SimpleClusterOmegaBlock.limitSource_step k Γ (SimpleClusterOmegaChain.block k Γ hchain n)

theorem SimpleClusterOmegaChain.exists_limitSource_stepDiff_eq_singleOfNonneg
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    ∃ δ : Γ, ∃ c : k, ∃ hδpos : 0 < δ,
      c ≠ 0 ∧
        U (n + 1) - SimpleClusterOmegaChain.limitSource k Γ hchain n =
          singleOfNonneg k Γ δ c (le_of_lt hδpos) ∧
          addVal k Γ
              ((U (n + 1) - SimpleClusterOmegaChain.limitSource k Γ hchain n :
                valuationSubring k Γ) : HahnField k Γ) =
            (δ : WithTop Γ) :=
  OddClusterStep.exists_stepDiff_eq_singleOfNonneg k Γ
    (SimpleClusterOmegaChain.limitSource_step k Γ hchain n)

noncomputable def SimpleClusterOmegaChain.limitStepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) : Γ :=
  Classical.choose
    (SimpleClusterOmegaChain.exists_limitSource_stepDiff_eq_singleOfNonneg k Γ hchain n)

noncomputable def SimpleClusterOmegaChain.limitStepCoeff
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) : k :=
  Classical.choose (Classical.choose_spec
    (SimpleClusterOmegaChain.exists_limitSource_stepDiff_eq_singleOfNonneg k Γ hchain n))

theorem SimpleClusterOmegaChain.addVal_eval_limitSource_eq_limitStepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    addVal k Γ
        ((F.eval (SimpleClusterOmegaChain.limitSource k Γ hchain n) :
          valuationSubring k Γ) : HahnField k Γ) =
      (SimpleClusterOmegaChain.limitStepValue k Γ hchain n : WithTop Γ) :=
  by
    rcases OddClusterStep.exists_step_value_scales_to_eval_value k Γ
        (SimpleClusterOmegaChain.limitSource_step k Γ hchain n) with
      ⟨γ, δ, hval, hstep, hδγ⟩
    let hdiff :=
      SimpleClusterOmegaChain.exists_limitSource_stepDiff_eq_singleOfNonneg k Γ hchain n
    have hstep' :
        addVal k Γ
            ((U (n + 1) - SimpleClusterOmegaChain.limitSource k Γ hchain n :
              valuationSubring k Γ) : HahnField k Γ) =
          (SimpleClusterOmegaChain.limitStepValue k Γ hchain n : WithTop Γ) :=
      (Classical.choose_spec (Classical.choose_spec hdiff)).2.2.2
    rw [hstep] at hstep'
    have hδ : δ = SimpleClusterOmegaChain.limitStepValue k Γ hchain n :=
      WithTop.coe_injective hstep'
    rw [hval, ← hδγ, hδ, one_nsmul]

theorem SimpleClusterOmegaChain.limitStepValue_lt_eval_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    (SimpleClusterOmegaChain.limitStepValue k Γ hchain n : WithTop Γ) <
      addVal k Γ (((F.eval (U (n + 1)) : valuationSubring k Γ) : HahnField k Γ)) := by
  rcases OddClusterStep.exists_eval_value_lt_next k Γ
      (SimpleClusterOmegaChain.limitSource_step k Γ hchain n) with
    ⟨γ, hval, himprove⟩
  rw [SimpleClusterOmegaChain.addVal_eval_limitSource_eq_limitStepValue
    k Γ hchain n] at hval
  exact hval.symm ▸ himprove

theorem SimpleClusterOmegaChain.limitStepValue_lt_succ_limitStepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    SimpleClusterOmegaChain.limitStepValue k Γ hchain n <
      SimpleClusterOmegaChain.limitStepValue k Γ hchain (n + 1) := by
  apply WithTop.coe_lt_coe.mp
  exact lt_of_lt_of_le
    (SimpleClusterOmegaChain.limitStepValue_lt_eval_succ k Γ hchain n)
    (by
      have hle := SimpleClusterOmegaChain.addVal_eval_le_limitSource k Γ hchain (n + 1)
      have hle' :
          addVal k Γ ((F.eval (U (n + 1)) : valuationSubring k Γ) : HahnField k Γ) ≤
            addVal k Γ
              ((F.eval (SimpleClusterOmegaChain.limitSource k Γ hchain (n + 1)) :
                valuationSubring k Γ) : HahnField k Γ) := by
        simpa [SimpleClusterOmegaChain.limitSource] using hle
      rw [SimpleClusterOmegaChain.addVal_eval_limitSource_eq_limitStepValue
        k Γ hchain (n + 1)] at hle'
      exact hle')

theorem SimpleClusterOmegaChain.limitStepValue_strictMono
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) :
    StrictMono (SimpleClusterOmegaChain.limitStepValue k Γ hchain) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  exact SimpleClusterOmegaChain.limitStepValue_lt_succ_limitStepValue k Γ hchain n

def SimpleClusterOmegaChain.limitCorrectionFamily
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) :
    HahnSeries.SummableFamily Γ k ℕ :=
  singleStrictMonoSummableFamily k Γ
    (SimpleClusterOmegaChain.limitStepValue k Γ hchain)
    (SimpleClusterOmegaChain.limitStepCoeff k Γ hchain)
    (SimpleClusterOmegaChain.limitStepValue_strictMono k Γ hchain)

theorem SimpleClusterOmegaChain.mem_succ
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    U (n + 1) ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  SimpleClusterOmegaBlock.mem_end k Γ
    (SimpleClusterOmegaChain.block k Γ hchain n)

theorem SimpleClusterOmegaChain.mem
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) :
    ∀ n : ℕ, U n ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)
  | 0 => SimpleClusterOmegaChain.mem_zero k Γ hchain
  | n + 1 => SimpleClusterOmegaChain.mem_succ k Γ hchain n

theorem SimpleClusterOmegaChain.exists_terminal_step
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {U : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterOmegaChain k Γ F U) (n : ℕ) :
    ∃ L : valuationSubring k Γ,
      L ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
        SimpleClusterStep k Γ F L (U (n + 1)) :=
  SimpleClusterOmegaBlock.exists_terminal_step k Γ
    (SimpleClusterOmegaChain.block k Γ hchain n)

end HahnField

end

end HahnKaplanskyRealClosedness
