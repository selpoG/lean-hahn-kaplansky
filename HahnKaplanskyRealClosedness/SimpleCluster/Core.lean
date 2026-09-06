/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Basic.ClusterProperty
import HahnKaplanskyRealClosedness.Basic.ValuationClusterProperty
import HahnKaplanskyRealClosedness.Basic.Newton
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Simple-cluster correction chains

This file collects lightweight infrastructure for iterating the simple-cluster correction step.
The heavy valuation estimates live in `Basic`; transfinite and Hahn-support bookkeeping is kept in
the fixed ordinal-prefix modules so changes do not repeatedly touch this foundational file.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The range of a strictly increasing map from a well-founded linear order is well-founded. -/
theorem isWF_range_of_strictMono
    {I α : Type*} [LinearOrder I] [WellFoundedLT I] [LinearOrder α]
    {f : I → α} (hf : StrictMono f) : (Set.range f).IsWF := by
  rw [Set.IsWF, Set.wellFoundedOn_range]
  exact Subrelation.wf (fun {i j} h => hf.lt_iff_lt.mp h)
    (inferInstance : WellFoundedLT I).wf

/-- The range of a strictly increasing sequence indexed by `ℕ` is partially well-ordered in a
linear order. -/
theorem isPWO_range_of_strictMono_nat {α : Type*} [LinearOrder α] {f : ℕ → α}
    (hf : StrictMono f) : (Set.range f).IsPWO :=
  (isWF_range_of_strictMono hf).isPWO

/-- A root of `F` inside the maximal ideal of the Hahn valuation subring.  This is the result
the simple-cluster construction ultimately tries to produce. -/
def RootInMaximalIdeal
    (F : Polynomial (valuationSubring k Γ)) : Prop :=
  ∃ y : valuationSubring k Γ,
    y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y

noncomputable def RootInMaximalIdeal.some {F : Polynomial (valuationSubring k Γ)}
    (h : RootInMaximalIdeal k Γ F) : valuationSubring k Γ :=
  Classical.choose h

theorem RootInMaximalIdeal.mem {F : Polynomial (valuationSubring k Γ)}
    (h : RootInMaximalIdeal k Γ F) :
    RootInMaximalIdeal.some k Γ h ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  (Classical.choose_spec h).1

theorem RootInMaximalIdeal.isRoot {F : Polynomial (valuationSubring k Γ)}
    (h : RootInMaximalIdeal k Γ F) :
    F.IsRoot (RootInMaximalIdeal.some k Γ h) :=
  (Classical.choose_spec h).2

theorem RootInMaximalIdeal.positiveHahnRootInMap
    {F : Polynomial (valuationSubring k Γ)}
    (h : RootInMaximalIdeal k Γ F) :
    PositiveHahnRootInMap k Γ F := by
  refine ⟨RootInMaximalIdeal.some k Γ h, ?_, ?_⟩
  · exact (mem_maximalIdeal_iff_pos_addVal k Γ _).mp (RootInMaximalIdeal.mem k Γ h)
  · exact Polynomial.IsRoot.map
      (f := algebraMap (valuationSubring k Γ) (HahnField k Γ))
      (RootInMaximalIdeal.isRoot k Γ h)

/-- A valuation-subring lift of a `K[X]` odd cluster, retaining the lower-coefficient and main
unit conditions needed by the local Newton machinery. -/
structure KOddClusterLiftData
    (F : Polynomial (HahnField k Γ)) (m : ℕ) where
  lift : Polynomial (valuationSubring k Γ)
  map_eq : lift.map (algebraMap (valuationSubring k Γ) (HahnField k Γ)) = F
  lower :
    ∀ i, i < m → lift.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)
  unit : IsUnit (lift.coeff m)

theorem KOddClusterLiftData.translatedCluster
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (D : KOddClusterLiftData k Γ F m) {A : valuationSubring k Γ}
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    (∀ i, i < m →
        (D.lift.comp (Polynomial.X + Polynomial.C A)).coeff i ∈
          IsLocalRing.maximalIdeal (valuationSubring k Γ)) ∧
      IsUnit ((D.lift.comp (Polynomial.X + Polynomial.C A)).coeff m) :=
  cluster_coeffs_comp_X_add_C_of_mem_maximalIdeal k Γ D.lower D.unit hA

noncomputable def KOddClusterLiftData.comp_X_add_C
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (D : KOddClusterLiftData k Γ F m) (A : valuationSubring k Γ)
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    KOddClusterLiftData k Γ
      (F.comp (Polynomial.X +
        Polynomial.C (algebraMap (valuationSubring k Γ) (HahnField k Γ) A))) m :=
  { lift := D.lift.comp (Polynomial.X + Polynomial.C A)
    map_eq := by
      rw [Polynomial.map_comp, D.map_eq]
      simp
    lower := (D.translatedCluster k Γ hA).1
    unit := (D.translatedCluster k Γ hA).2 }

theorem exists_KOddClusterLiftData
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    Nonempty (KOddClusterLiftData k Γ F m) := by
  have hlifts :
      F ∈ Polynomial.lifts (algebraMap (valuationSubring k Γ) (HahnField k Γ)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine ⟨⟨F.coeff i, ?_⟩, rfl⟩
    exact KOddClusterHypotheses.nonneg (k := k) (Γ := Γ) h i
  rcases (Polynomial.mem_lifts (f := algebraMap (valuationSubring k Γ) (HahnField k Γ))
      F).mp hlifts with ⟨G, hG⟩
  refine ⟨{ lift := G, map_eq := hG, lower := ?_, unit := ?_ }⟩
  · intro i hi
    rw [mem_maximalIdeal_iff_pos_addVal]
    have hcoeff : ((G.coeff i : valuationSubring k Γ) : HahnField k Γ) = F.coeff i := by
      calc
        ((G.coeff i : valuationSubring k Γ) : HahnField k Γ) =
            algebraMap (valuationSubring k Γ) (HahnField k Γ) (G.coeff i) :=
          (Algebra.algebraMap_ofSubsemiring_apply (valuationSubring k Γ) (G.coeff i)).symm
        _ = (G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).coeff i := by
          rw [Polynomial.coeff_map]
        _ = F.coeff i := congrArg (fun P : Polynomial (HahnField k Γ) => P.coeff i) hG
    change (0 : WithTop Γ) < addVal k Γ ((G.coeff i : valuationSubring k Γ) : HahnField k Γ)
    simpa [hcoeff] using KOddClusterHypotheses.lower (k := k) (Γ := Γ) h i hi
  · rw [isUnit_iff_addVal_eq_zero]
    have hcoeff : ((G.coeff m : valuationSubring k Γ) : HahnField k Γ) = F.coeff m := by
      calc
        ((G.coeff m : valuationSubring k Γ) : HahnField k Γ) =
            algebraMap (valuationSubring k Γ) (HahnField k Γ) (G.coeff m) :=
          (Algebra.algebraMap_ofSubsemiring_apply (valuationSubring k Γ) (G.coeff m)).symm
        _ = (G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).coeff m := by
          rw [Polynomial.coeff_map]
        _ = F.coeff m := congrArg (fun P : Polynomial (HahnField k Γ) => P.coeff m) hG
    change addVal k Γ ((G.coeff m : valuationSubring k Γ) : HahnField k Γ) = 0
    simpa [hcoeff] using KOddClusterHypotheses.main (k := k) (Γ := Γ) h

theorem exists_lift_of_KOddClusterHypotheses
    {F : Polynomial (HahnField k Γ)} {m : ℕ}
    (h : KOddClusterHypotheses k Γ F m) :
    ∃ G : Polynomial (valuationSubring k Γ),
      G.map (algebraMap (valuationSubring k Γ) (HahnField k Γ)) = F ∧
        (∀ i, i < m → G.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) ∧
          IsUnit (G.coeff m) := by
  rcases exists_KOddClusterLiftData k Γ h with ⟨D⟩
  exact ⟨D.lift, D.map_eq, D.lower, D.unit⟩

/-- A rootless maximal-ideal approximation, used as the state of the block-level cluster
iteration. -/
structure OneClusterState
    (F : Polynomial (valuationSubring k Γ)) where
  source : valuationSubring k Γ
  source_mem : source ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)
  not_root : ¬ F.IsRoot source

namespace OneClusterState

theorem eval_ne_zero {F : Polynomial (valuationSubring k Γ)}
    (S : OneClusterState k Γ F) :
    F.eval S.source ≠ 0 := by
  intro hzero
  exact S.not_root (by simpa [Polynomial.IsRoot] using hzero)

theorem eval_coe_ne_zero {F : Polynomial (valuationSubring k Γ)}
    (S : OneClusterState k Γ F) :
    ((F.eval S.source : valuationSubring k Γ) : HahnField k Γ) ≠ 0 := by
  intro hzero
  have hsub : F.eval S.source = 0 := Subtype.ext hzero
  exact OneClusterState.eval_ne_zero k Γ S hsub

/-- The finite residual valuation at a rootless state. -/
noncomputable def val {F : Polynomial (valuationSubring k Γ)}
    (S : OneClusterState k Γ F) : Γ :=
  (addVal k Γ ((F.eval S.source : valuationSubring k Γ) : HahnField k Γ)).untop
    (by simpa [AddValuation.ne_top_iff] using S.eval_coe_ne_zero)

theorem val_spec {F : Polynomial (valuationSubring k Γ)}
    (S : OneClusterState k Γ F) :
    addVal k Γ ((F.eval S.source : valuationSubring k Γ) : HahnField k Γ) =
      (S.val k Γ : WithTop Γ) :=
  (WithTop.coe_untop _ _).symm

theorem val_pos_of_cluster_pos {F : Polynomial (valuationSubring k Γ)}
    (S : OneClusterState k Γ F) {m : ℕ}
    (hsmall : ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hm : 0 < m) :
    0 < S.val k Γ := by
  have hmem :
      F.eval S.source ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
    eval_mem_maximalIdeal_of_cluster_pos k Γ hsmall hm S.source_mem
  have hpos :
      (0 : WithTop Γ) <
        addVal k Γ ((F.eval S.source : valuationSubring k Γ) : HahnField k Γ) :=
    (mem_maximalIdeal_iff_pos_addVal k Γ (F.eval S.source)).mp hmem
  rw [S.val_spec k Γ] at hpos
  exact WithTop.coe_lt_coe.mp hpos

end OneClusterState

/-- A block-level successor: one bounded omega block has moved from `S.source` to
`next.source`, strictly improving the residual value and keeping the total block correction
inside the interval between the old and new residual values. -/
structure OneClusterBlockSuccessor
    {F : Polynomial (valuationSubring k Γ)} (S : OneClusterState k Γ F) where
  next : OneClusterState k Γ F
  val_lt : S.val k Γ < next.val k Γ
  support_sub_Ico :
    (ofLex ((next.source - S.source : valuationSubring k Γ) : HahnField k Γ)).support ⊆
      Set.Ico (S.val k Γ) (next.val k Γ)

namespace OneClusterBlockSuccessor

/-- The Hahn-series difference contributed by one block successor. -/
def diffHahnSeries {F : Polynomial (valuationSubring k Γ)} {S : OneClusterState k Γ F}
    (B : OneClusterBlockSuccessor k Γ S) : HahnSeries Γ k :=
  ofLex ((B.next.source - S.source : valuationSubring k Γ) : HahnField k Γ)

theorem diffHahnSeries_support_subset_Ico
    {F : Polynomial (valuationSubring k Γ)} {S : OneClusterState k Γ F}
    (B : OneClusterBlockSuccessor k Γ S) :
    (B.diffHahnSeries k Γ).support ⊆ Set.Ico (S.val k Γ) (B.next.val k Γ) :=
  B.support_sub_Ico

end OneClusterBlockSuccessor

/-- The initial state is either already a maximal-ideal root at `0`, or the rootless state with
source `0`. -/
theorem rootInMaximalIdeal_or_initialState
    (F : Polynomial (valuationSubring k Γ)) :
    RootInMaximalIdeal k Γ F ∨ Nonempty (OneClusterState k Γ F) := by
  by_cases hroot : F.IsRoot (0 : valuationSubring k Γ)
  · exact Or.inl ⟨0, Ideal.zero_mem _, hroot⟩
  · exact Or.inr ⟨{
      source := 0
      source_mem := Ideal.zero_mem _
      not_root := hroot
    }⟩

/-- One odd-cluster Newton correction step at multiplicity `m`, where the correction exponent
satisfies `m • δ = γ` and `γ` is the current evaluation valuation. -/
def OddClusterStep
    (F : Polynomial (valuationSubring k Γ)) (m : ℕ)
    (y y' : valuationSubring k Γ) : Prop :=
  y' ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
    ∃ γ : Γ, ∃ δ : Γ, ∃ c : k,
      ∃ hδpos : 0 < δ, 0 < γ ∧ c ≠ 0 ∧ m • δ = γ ∧
        y' = singleOfNonneg k Γ δ c (le_of_lt hδpos) + y ∧
          addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
            (γ : WithTop Γ) ∧
            addVal k Γ ((y' - y : valuationSubring k Γ) : HahnField k Γ) =
              (δ : WithTop Γ) ∧
              (γ : WithTop Γ) <
                addVal k Γ (((F.eval y' : valuationSubring k Γ) : HahnField k Γ))

/-- A simple-cluster Newton correction step is the multiplicity-one specialization of an
odd-cluster step. -/
abbrev SimpleClusterStep
    (F : Polynomial (valuationSubring k Γ)) (y y' : valuationSubring k Γ) : Prop :=
  OddClusterStep k Γ F 1 y y'

/-- A non-root simple-cluster maximal-ideal approximation admits a packaged correction step. -/
theorem exists_simpleClusterStep_of_one_cluster
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)} {y : valuationSubring k Γ}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) (hne : F.eval y ≠ 0) :
    ∃ y' : valuationSubring k Γ, SimpleClusterStep k Γ F y y' := by
  rcases exists_next_approx_improves_eval_at_of_one_cluster_with_values
    k Γ hsmall hunit hy hne with
    ⟨y', hy', γ, δ, c, hδpos, hγpos, hcne, hδ, hy'eq, hval, hstep, himprove⟩
  refine ⟨y', hy', γ, δ, c, hδpos, hγpos, hcne, ?_, hy'eq, hval, hstep, himprove⟩
  simpa using hδ

/-- A root of the current translated Newton initial polynomial gives a packaged odd-cluster
correction step, provided all translated Newton weights are at least the current evaluation
value. -/
theorem exists_oddClusterStep_of_current_edge_initial_root
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ} {y : valuationSubring k Γ}
    {γ δ : Γ} {c : k}
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hval : addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
      (γ : WithTop Γ))
    (hδpos : 0 < δ) (hγpos : 0 < γ) (hc : c ≠ 0) (hscale : m • δ = γ)
    (hge :
      ∀ i ∈ Finset.range ((F.comp (Polynomial.X + Polynomial.C y)).natDegree + 1),
        (γ : WithTop Γ) ≤
          newtonWeight k Γ
            ((F.comp (Polynomial.X + Polynomial.C y)).map
              (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ i)
    (hroot :
      (newtonInitialPolynomial k Γ
        ((F.comp (Polynomial.X + Polynomial.C y)).map
          (algebraMap (valuationSubring k Γ) (HahnField k Γ))) δ γ).IsRoot c) :
    ∃ y' : valuationSubring k Γ, OddClusterStep k Γ F m y y' := by
  let y' : valuationSubring k Γ := singleOfNonneg k Γ δ c (le_of_lt hδpos) + y
  have hy' : y' ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
    dsimp [y']
    simpa [add_comm] using add_singleOfNonneg_mem_maximalIdeal_of_mem_of_pos
      k Γ hy hδpos hc
  have hstep : addVal k Γ ((y' - y : valuationSubring k Γ) : HahnField k Γ) =
      (δ : WithTop Γ) := by
    have hsub : (y' - y : valuationSubring k Γ) =
        singleOfNonneg k Γ δ c (le_of_lt hδpos) := by
      dsimp [y']
      abel
    rw [hsub]
    exact addVal_singleOfNonneg_of_ne k Γ (le_of_lt hδpos) hc
  have himprove : (γ : WithTop Γ) <
      addVal k Γ (((F.eval y' : valuationSubring k Γ) : HahnField k Γ)) := by
    dsimp [y']
    exact lt_addVal_eval_add_singleOfNonneg_of_newtonInitialPolynomial_root
      k Γ F y (le_of_lt hδpos) hc hge hroot
  exact ⟨y', hy', γ, δ, c, hδpos, hγpos, hc, hscale, rfl, hval, hstep, himprove⟩

/-- The target of a packaged odd-cluster step remains in the maximal ideal. -/
theorem OddClusterStep.mem_maximalIdeal
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ} {y y' : valuationSubring k Γ}
    (hstep : OddClusterStep k Γ F m y y') :
    y' ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  hstep.1

/-- A packaged odd-cluster step strictly improves the evaluation valuation. -/
theorem OddClusterStep.exists_eval_value_lt_next
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ} {y y' : valuationSubring k Γ}
    (hstep : OddClusterStep k Γ F m y y') :
    ∃ γ : Γ,
      addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ) ∧
        (γ : WithTop Γ) <
          addVal k Γ (((F.eval y' : valuationSubring k Γ) : HahnField k Γ)) := by
  rcases hstep.2 with
    ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, hy'eq, hval, hstepVal, himprove⟩
  exact ⟨γ, hval, himprove⟩

/-- The source of a packaged odd-cluster correction step is not already a root. -/
theorem OddClusterStep.source_not_root
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ} {y y' : valuationSubring k Γ}
    (hstep : OddClusterStep k Γ F m y y') :
    ¬ F.IsRoot y := by
  rcases hstep.exists_eval_value_lt_next with ⟨γ, hval, _⟩
  intro hroot
  rw [Polynomial.IsRoot] at hroot
  rw [hroot] at hval
  have htop :
      addVal k Γ (((0 : valuationSubring k Γ) : HahnField k Γ)) = ⊤ := by
    simp
  rw [htop] at hval
  exact (WithTop.coe_ne_top : ((γ : Γ) : WithTop Γ) ≠ ⊤) hval.symm

/-- A packaged odd-cluster step records that the correction valuation `δ` scales to the current
evaluation valuation `γ` by `m • δ = γ`. -/
theorem OddClusterStep.exists_step_value_scales_to_eval_value
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ} {y y' : valuationSubring k Γ}
    (hstep : OddClusterStep k Γ F m y y') :
    ∃ γ : Γ, ∃ δ : Γ,
      addVal k Γ ((F.eval y : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ) ∧
        addVal k Γ ((y' - y : valuationSubring k Γ) : HahnField k Γ) =
          (δ : WithTop Γ) ∧
          m • δ = γ := by
  rcases hstep.2 with
    ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, hy'eq, hval, hstepVal, himprove⟩
  exact ⟨γ, δ, hval, hstepVal, hδ⟩

/-- A packaged odd-cluster step has a correction difference which is literally a positive
single-term Hahn series in the valuation subring. -/
theorem OddClusterStep.exists_stepDiff_eq_singleOfNonneg
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ} {y y' : valuationSubring k Γ}
    (hstep : OddClusterStep k Γ F m y y') :
    ∃ δ : Γ, ∃ c : k, ∃ hδpos : 0 < δ,
      c ≠ 0 ∧
        y' - y = singleOfNonneg k Γ δ c (le_of_lt hδpos) ∧
          addVal k Γ ((y' - y : valuationSubring k Γ) : HahnField k Γ) =
            (δ : WithTop Γ) := by
  rcases hstep.2 with
    ⟨γ, δ, c, hδpos, hγpos, hcne, hδ, hy'eq, hval, hstepVal, himprove⟩
  refine ⟨δ, c, hδpos, hcne, ?_, hstepVal⟩
  rw [hy'eq]
  abel

/-- Transport a packaged odd-cluster step for `F(X + A)` back to a packaged step for `F`. -/
theorem OddClusterStep.of_comp_X_add_C
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ}
    {A z z' : valuationSubring k Γ}
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hstep : OddClusterStep k Γ (F.comp (Polynomial.X + Polynomial.C A)) m z z') :
    OddClusterStep k Γ F m (z + A) (z' + A) := by
  rcases hstep with
    ⟨hz', γ, δ, c, hδpos, hγpos, hcne, hδ, hz'eq, hval, hstepVal, himprove⟩
  refine ⟨?_, γ, δ, c, hδpos, hγpos, hcne, hδ, ?_, ?_, ?_, ?_⟩
  · exact (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem hz' hA
  · rw [hz'eq]
    abel
  · rw [← eval_comp_X_add_C k Γ F A z]
    exact hval
  · have hsub : z' + A - (z + A) = z' - z := by
      abel
    rw [hsub]
    exact hstepVal
  · rw [← eval_comp_X_add_C k Γ F A z']
    exact himprove

/-- Translate a packaged odd-cluster step for `F` to one for `F(X + A)`. -/
theorem OddClusterStep.to_comp_X_add_C
    {F : Polynomial (valuationSubring k Γ)} {m : ℕ}
    {A z z' : valuationSubring k Γ}
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hstep : OddClusterStep k Γ F m (z + A) (z' + A)) :
    OddClusterStep k Γ (F.comp (Polynomial.X + Polynomial.C A)) m z z' := by
  rcases hstep with
    ⟨hy', γ, δ, c, hδpos, hγpos, hcne, hδ, hy'eq, hval, hstepVal, himprove⟩
  refine ⟨?_, γ, δ, c, hδpos, hγpos, hcne, hδ, ?_, ?_, ?_, ?_⟩
  · have hz' : z' = (z' + A) - A := by
      abel
    rw [hz']
    exact (IsLocalRing.maximalIdeal (valuationSubring k Γ)).sub_mem hy' hA
  · calc
      z' = (z' + A) - A := by abel
      _ = (singleOfNonneg k Γ δ c (le_of_lt hδpos) + (z + A)) - A := by
        rw [hy'eq]
      _ = singleOfNonneg k Γ δ c (le_of_lt hδpos) + z := by abel
  · rw [eval_comp_X_add_C k Γ F A z]
    exact hval
  · have hsub : z' - z = (z' + A) - (z + A) := by
      abel
    rw [hsub]
    exact hstepVal
  · rw [eval_comp_X_add_C k Γ F A z']
    exact himprove

/-- Transport a maximal-ideal root of `F(X + A)` back to a maximal-ideal root of `F`. -/
theorem exists_maximalIdeal_root_of_comp_X_add_C
    {F : Polynomial (valuationSubring k Γ)} {A : valuationSubring k Γ}
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hroot : ∃ z : valuationSubring k Γ,
      z ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
        (F.comp (Polynomial.X + Polynomial.C A)).IsRoot z) :
    ∃ y : valuationSubring k Γ,
      y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y := by
  rcases hroot with ⟨z, hz, hzroot⟩
  exact ⟨z + A,
    (IsLocalRing.maximalIdeal (valuationSubring k Γ)).add_mem hz hA,
    isRoot_add_of_isRoot_comp_X_add_C k Γ hzroot⟩

theorem PositiveHahnRoot.of_comp_X_add_C
    {F : Polynomial (HahnField k Γ)} {A : valuationSubring k Γ}
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hroot : PositiveHahnRoot k Γ
      (F.comp (Polynomial.X +
        Polynomial.C (algebraMap (valuationSubring k Γ) (HahnField k Γ) A)))) :
    PositiveHahnRoot k Γ F := by
  rcases hroot with ⟨z, hzpos, hzroot⟩
  refine ⟨z + algebraMap (valuationSubring k Γ) (HahnField k Γ) A, ?_, ?_⟩
  · have hApos :
        (0 : WithTop Γ) <
          addVal k Γ (algebraMap (valuationSubring k Γ) (HahnField k Γ) A) := by
      simpa only [Algebra.algebraMap_ofSubsemiring_apply] using
        (mem_maximalIdeal_iff_pos_addVal k Γ A).mp hA
    exact (addVal k Γ).map_lt_add hzpos hApos
  · rw [Polynomial.IsRoot] at hzroot ⊢
    simpa [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      using hzroot

/-- A simple-cluster correction chain starts in the maximal ideal and at each natural stage either
has already reached a root or takes one packaged simple-cluster correction step. -/
def SimpleClusterChain
    (F : Polynomial (valuationSubring k Γ)) (u : ℕ → valuationSubring k Γ) : Prop :=
  u 0 ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧
    ∀ n : ℕ, F.IsRoot (u n) ∨ SimpleClusterStep k Γ F (u n) (u (n + 1))

theorem SimpleClusterChain.mem_zero
    {F : Polynomial (valuationSubring k Γ)} {u : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterChain k Γ F u) :
    u 0 ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) :=
  hchain.1

theorem SimpleClusterChain.root_or_step
    {F : Polynomial (valuationSubring k Γ)} {u : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterChain k Γ F u) (n : ℕ) :
    F.IsRoot (u n) ∨ SimpleClusterStep k Γ F (u n) (u (n + 1)) :=
  hchain.2 n

theorem SimpleClusterChain.exists_eval_value_lt_succ_of_not_root
    {F : Polynomial (valuationSubring k Γ)} {u : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterChain k Γ F u) {n : ℕ}
    (hn : ¬ F.IsRoot (u n)) :
    ∃ γ : Γ,
      addVal k Γ ((F.eval (u n) : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ) ∧
        (γ : WithTop Γ) <
          addVal k Γ (((F.eval (u (n + 1)) : valuationSubring k Γ) : HahnField k Γ)) := by
  rcases SimpleClusterChain.root_or_step k Γ hchain n with hroot | hstep
  · exact False.elim (hn hroot)
  · exact hstep.exists_eval_value_lt_next

/-- The correction added at stage `n` of a simple-cluster chain. -/
def SimpleClusterChain.stepDiff
    (u : ℕ → valuationSubring k Γ) (n : ℕ) : valuationSubring k Γ :=
  u (n + 1) - u n

theorem SimpleClusterChain.add_stepDiff
    (u : ℕ → valuationSubring k Γ) (n : ℕ) :
    u n + SimpleClusterChain.stepDiff k Γ u n = u (n + 1) := by
  dsimp [SimpleClusterChain.stepDiff]
  abel

/-- Finite simple-cluster approximations are partial sums of their correction differences. -/
theorem SimpleClusterChain.sum_stepDiff_range_add_zero
    (u : ℕ → valuationSubring k Γ) :
    ∀ n : ℕ,
      (Finset.range n).sum (fun i => SimpleClusterChain.stepDiff k Γ u i) + u 0 = u n
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ]
      calc
        ((Finset.range n).sum (fun i => SimpleClusterChain.stepDiff k Γ u i) +
            SimpleClusterChain.stepDiff k Γ u n) + u 0
            = SimpleClusterChain.stepDiff k Γ u n +
              ((Finset.range n).sum (fun i => SimpleClusterChain.stepDiff k Γ u i) +
                u 0) := by
                abel
        _ = SimpleClusterChain.stepDiff k Γ u n + u n := by
                rw [SimpleClusterChain.sum_stepDiff_range_add_zero u n]
        _ = u (n + 1) := by
          rw [add_comm]
          exact SimpleClusterChain.add_stepDiff k Γ u n

theorem SimpleClusterChain.exists_stepDiff_value_eq_eval_value_of_not_root
    {F : Polynomial (valuationSubring k Γ)} {u : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterChain k Γ F u) {n : ℕ}
    (hn : ¬ F.IsRoot (u n)) :
    ∃ γ : Γ, ∃ δ : Γ,
      addVal k Γ ((F.eval (u n) : valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ) ∧
        addVal k Γ
          ((SimpleClusterChain.stepDiff k Γ u n : valuationSubring k Γ) : HahnField k Γ) =
          (δ : WithTop Γ) ∧
          δ = γ := by
  rcases SimpleClusterChain.root_or_step k Γ hchain n with hroot | hstep
  · exact False.elim (hn hroot)
  · simpa only [SimpleClusterChain.stepDiff, one_nsmul] using
      hstep.exists_step_value_scales_to_eval_value k Γ

theorem SimpleClusterChain.exists_stepDiff_eq_singleOfNonneg_of_not_root
    {F : Polynomial (valuationSubring k Γ)} {u : ℕ → valuationSubring k Γ}
    (hchain : SimpleClusterChain k Γ F u) {n : ℕ}
    (hn : ¬ F.IsRoot (u n)) :
    ∃ δ : Γ, ∃ c : k, ∃ hδpos : 0 < δ,
      c ≠ 0 ∧
        SimpleClusterChain.stepDiff k Γ u n =
          singleOfNonneg k Γ δ c (le_of_lt hδpos) ∧
          addVal k Γ
            ((SimpleClusterChain.stepDiff k Γ u n : valuationSubring k Γ) : HahnField k Γ) =
            (δ : WithTop Γ) := by
  rcases SimpleClusterChain.root_or_step k Γ hchain n with hroot | hstep
  · exact False.elim (hn hroot)
  · simpa [SimpleClusterChain.stepDiff] using hstep.exists_stepDiff_eq_singleOfNonneg

/-- One deterministic choice of the next simple-cluster approximation. If the current point is
already a root, it stays fixed; otherwise it chooses one packaged correction step. -/
def nextApproxOfOneCluster
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) (y : valuationSubring k Γ) :
    valuationSubring k Γ := by
  classical
  exact
    if hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) then
      if hroot : F.IsRoot y then
        y
      else
        Classical.choose
          (exists_simpleClusterStep_of_one_cluster k Γ hsmall hunit hy
            (by simpa [Polynomial.IsRoot] using hroot))
    else
      y

theorem nextApprox_root_or_step_of_one_cluster
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) {y : valuationSubring k Γ}
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    F.IsRoot y ∨
      SimpleClusterStep k Γ F y
        (nextApproxOfOneCluster (k := k) (Γ := Γ) hsmall hunit y) := by
  classical
  by_cases hroot : F.IsRoot y
  · left
    exact hroot
  · right
    dsimp [nextApproxOfOneCluster]
    rw [dif_pos hy, dif_neg hroot]
    exact Classical.choose_spec
      (exists_simpleClusterStep_of_one_cluster k Γ hsmall hunit hy
        (by simpa [Polynomial.IsRoot] using hroot))

theorem nextApprox_mem_maximalIdeal_of_one_cluster
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) {y : valuationSubring k Γ}
    (hy : y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    nextApproxOfOneCluster (k := k) (Γ := Γ) hsmall hunit y ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  classical
  rcases nextApprox_root_or_step_of_one_cluster k Γ hsmall hunit hy with hroot | hstep
  · dsimp [nextApproxOfOneCluster]
    rw [dif_pos hy, dif_pos hroot]
    exact hy
  · exact hstep.mem_maximalIdeal

/-- The natural sequence obtained by iterating `nextApproxOfOneCluster` from `0`. -/
def simpleClusterApproxOfOneCluster
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) : ℕ → valuationSubring k Γ
  | 0 => 0
  | n + 1 =>
      nextApproxOfOneCluster (k := k) (Γ := Γ) hsmall hunit
        (simpleClusterApproxOfOneCluster hsmall hunit n)

theorem simpleClusterApprox_mem_maximalIdeal_of_one_cluster
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) :
    ∀ n : ℕ,
      simpleClusterApproxOfOneCluster k Γ hsmall hunit n ∈
        IsLocalRing.maximalIdeal (valuationSubring k Γ)
  | 0 => by
      simp [simpleClusterApproxOfOneCluster]
  | n + 1 => by
      exact nextApprox_mem_maximalIdeal_of_one_cluster k Γ hsmall hunit
        (simpleClusterApprox_mem_maximalIdeal_of_one_cluster hsmall hunit n)

theorem simpleClusterApprox_is_chain_of_one_cluster
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) :
    SimpleClusterChain k Γ F
      (simpleClusterApproxOfOneCluster k Γ hsmall hunit) := by
  constructor
  · exact simpleClusterApprox_mem_maximalIdeal_of_one_cluster k Γ hsmall hunit 0
  · intro n
    dsimp [simpleClusterApproxOfOneCluster]
    exact nextApprox_root_or_step_of_one_cluster k Γ hsmall hunit
      (simpleClusterApprox_mem_maximalIdeal_of_one_cluster k Γ hsmall hunit n)

theorem simpleClusterApprox_succ_eq_of_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) {n : ℕ}
    (hroot : F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + 1) =
      simpleClusterApproxOfOneCluster k Γ hsmall hunit n := by
  classical
  dsimp [simpleClusterApproxOfOneCluster, nextApproxOfOneCluster]
  rw [dif_pos (simpleClusterApprox_mem_maximalIdeal_of_one_cluster k Γ hsmall hunit n),
    dif_pos hroot]

theorem simpleClusterApprox_add_eq_of_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) {n : ℕ}
    (hroot : F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    ∀ r : ℕ,
      simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + r) =
        simpleClusterApproxOfOneCluster k Γ hsmall hunit n
  | 0 => by simp
  | r + 1 => by
      have hprev :
          simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + r) =
            simpleClusterApproxOfOneCluster k Γ hsmall hunit n :=
        simpleClusterApprox_add_eq_of_root hsmall hunit hroot r
      have hroot_prev :
          F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + r)) := by
        rwa [hprev]
      calc
        simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + (r + 1))
            = simpleClusterApproxOfOneCluster k Γ hsmall hunit ((n + r) + 1) := by
                rw [Nat.add_succ]
        _ = simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + r) :=
                simpleClusterApprox_succ_eq_of_root k Γ hsmall hunit hroot_prev
        _ = simpleClusterApproxOfOneCluster k Γ hsmall hunit n := hprev

theorem simpleClusterApprox_sum_stepDiff_range_eq
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) (n : ℕ) :
    (Finset.range n).sum
      (fun i =>
        SimpleClusterChain.stepDiff k Γ (simpleClusterApproxOfOneCluster k Γ hsmall hunit) i) =
      simpleClusterApproxOfOneCluster k Γ hsmall hunit n := by
  have hsum := SimpleClusterChain.sum_stepDiff_range_add_zero k Γ
    (simpleClusterApproxOfOneCluster k Γ hsmall hunit) n
  simpa [simpleClusterApproxOfOneCluster] using hsum

theorem exists_maximalIdeal_root_of_simpleClusterApprox_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hroot : ∃ n : ℕ, F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    ∃ y : valuationSubring k Γ,
      y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y := by
  rcases hroot with ⟨n, hn⟩
  exact ⟨simpleClusterApproxOfOneCluster k Γ hsmall hunit n,
    simpleClusterApprox_mem_maximalIdeal_of_one_cluster k Γ hsmall hunit n, hn⟩

theorem simpleClusterApprox_exists_stepDiff_value_eq_eval_value_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    ∀ n : ℕ, ∃ γ : Γ, ∃ δ : Γ,
      addVal k Γ
          ((F.eval (simpleClusterApproxOfOneCluster k Γ hsmall hunit n) :
            valuationSubring k Γ) : HahnField k Γ) =
        (γ : WithTop Γ) ∧
        addVal k Γ
          ((SimpleClusterChain.stepDiff k Γ
            (simpleClusterApproxOfOneCluster k Γ hsmall hunit) n :
            valuationSubring k Γ) : HahnField k Γ) =
          (δ : WithTop Γ) ∧
          δ = γ := by
  intro n
  exact SimpleClusterChain.exists_stepDiff_value_eq_eval_value_of_not_root k Γ
    (simpleClusterApprox_is_chain_of_one_cluster k Γ hsmall hunit) (hnoroot n)

/-- The finite value of the evaluation at the `n`th simple-cluster approximation, in the
non-stopping branch. -/
def simpleClusterApproxEvalValueOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) : Γ :=
  Classical.choose
    (simpleClusterApprox_exists_stepDiff_value_eq_eval_value_of_no_root
      k Γ hsmall hunit hnoroot n)

/-- The finite value of the `n`th correction difference, in the non-stopping branch. -/
def simpleClusterApproxStepValueOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) : Γ :=
  Classical.choose
    (Classical.choose_spec
      (simpleClusterApprox_exists_stepDiff_value_eq_eval_value_of_no_root
        k Γ hsmall hunit hnoroot n))

theorem simpleClusterApprox_addVal_eval_eq_evalValue_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    addVal k Γ
        ((F.eval (simpleClusterApproxOfOneCluster k Γ hsmall hunit n) :
          valuationSubring k Γ) : HahnField k Γ) =
      (simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) := by
  dsimp [simpleClusterApproxEvalValueOfNoRoot, simpleClusterApproxStepValueOfNoRoot]
  exact (Classical.choose_spec
    (Classical.choose_spec
      (simpleClusterApprox_exists_stepDiff_value_eq_eval_value_of_no_root
        k Γ hsmall hunit hnoroot n))).1

theorem simpleClusterApprox_addVal_stepDiff_eq_stepValue_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    addVal k Γ
        ((SimpleClusterChain.stepDiff k Γ
          (simpleClusterApproxOfOneCluster k Γ hsmall hunit) n :
          valuationSubring k Γ) : HahnField k Γ) =
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) := by
  dsimp [simpleClusterApproxEvalValueOfNoRoot, simpleClusterApproxStepValueOfNoRoot]
  exact (Classical.choose_spec
    (Classical.choose_spec
      (simpleClusterApprox_exists_stepDiff_value_eq_eval_value_of_no_root
        k Γ hsmall hunit hnoroot n))).2.1

theorem simpleClusterApprox_stepValue_eq_evalValue_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n =
      simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot n := by
  dsimp [simpleClusterApproxEvalValueOfNoRoot, simpleClusterApproxStepValueOfNoRoot]
  exact (Classical.choose_spec
    (Classical.choose_spec
      (simpleClusterApprox_exists_stepDiff_value_eq_eval_value_of_no_root
        k Γ hsmall hunit hnoroot n))).2.2

theorem simpleClusterApprox_evalValue_lt_succ_evalValue_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot n <
      simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot (n + 1) := by
  rcases SimpleClusterChain.exists_eval_value_lt_succ_of_not_root k Γ
      (simpleClusterApprox_is_chain_of_one_cluster k Γ hsmall hunit) (hnoroot n) with
    ⟨γ, hγ, hlt⟩
  have hcurrent :
      (γ : WithTop Γ) =
        (simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) := by
    exact hγ.symm.trans
      (simpleClusterApprox_addVal_eval_eq_evalValue_of_no_root
        k Γ hsmall hunit hnoroot n)
  have hnext :
      addVal k Γ
          (((F.eval (simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + 1)) :
            valuationSubring k Γ) : HahnField k Γ)) =
        (simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot (n + 1) :
          WithTop Γ) :=
    simpleClusterApprox_addVal_eval_eq_evalValue_of_no_root
      k Γ hsmall hunit hnoroot (n + 1)
  apply WithTop.coe_lt_coe.mp
  rw [hcurrent] at hlt
  rw [hnext] at hlt
  exact hlt

theorem simpleClusterApprox_evalValue_strictMono_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    StrictMono (simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  exact simpleClusterApprox_evalValue_lt_succ_evalValue_of_no_root
    k Γ hsmall hunit hnoroot n

theorem simpleClusterApprox_evalValue_lt_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    {m n : ℕ} (hmn : m < n) :
    simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot m <
      simpleClusterApproxEvalValueOfNoRoot k Γ hsmall hunit hnoroot n :=
  simpleClusterApprox_evalValue_strictMono_of_no_root k Γ hsmall hunit hnoroot hmn

theorem simpleClusterApprox_exists_stepDiff_eq_singleOfNonneg_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    ∃ δ : Γ, ∃ c : k, ∃ hδpos : 0 < δ,
      c ≠ 0 ∧
        SimpleClusterChain.stepDiff k Γ
            (simpleClusterApproxOfOneCluster k Γ hsmall hunit) n =
          singleOfNonneg k Γ δ c (le_of_lt hδpos) ∧
          addVal k Γ
            ((SimpleClusterChain.stepDiff k Γ
              (simpleClusterApproxOfOneCluster k Γ hsmall hunit) n :
              valuationSubring k Γ) : HahnField k Γ) =
            (δ : WithTop Γ) :=
  SimpleClusterChain.exists_stepDiff_eq_singleOfNonneg_of_not_root k Γ
    (simpleClusterApprox_is_chain_of_one_cluster k Γ hsmall hunit) (hnoroot n)

theorem simpleClusterApprox_stepValue_pos_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    0 < simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n := by
  rcases simpleClusterApprox_exists_stepDiff_eq_singleOfNonneg_of_no_root
      k Γ hsmall hunit hnoroot n with
    ⟨δ, c, hδpos, hcne, hdiff, hval⟩
  have hstepVal :=
    simpleClusterApprox_addVal_stepDiff_eq_stepValue_of_no_root
      k Γ hsmall hunit hnoroot n
  have hδ :
      δ = simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n :=
    WithTop.coe_inj.mp (hval.symm.trans hstepVal)
  rwa [← hδ]

theorem simpleClusterApprox_exists_stepCoeff_for_stepValue_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    ∃ c : k,
      c ≠ 0 ∧
        SimpleClusterChain.stepDiff k Γ
            (simpleClusterApproxOfOneCluster k Γ hsmall hunit) n =
          singleOfNonneg k Γ
            (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n) c
            (le_of_lt
              (simpleClusterApprox_stepValue_pos_of_no_root k Γ hsmall hunit hnoroot n)) := by
  rcases simpleClusterApprox_exists_stepDiff_eq_singleOfNonneg_of_no_root
      k Γ hsmall hunit hnoroot n with
    ⟨δ, c, hδpos, hcne, hdiff, hval⟩
  have hstepVal :=
    simpleClusterApprox_addVal_stepDiff_eq_stepValue_of_no_root
      k Γ hsmall hunit hnoroot n
  have hδ :
      δ = simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n :=
    WithTop.coe_inj.mp (hval.symm.trans hstepVal)
  subst δ
  refine ⟨c, hcne, hdiff.trans ?_⟩
  apply Subtype.ext
  simp [singleOfNonneg_coe]

/-- The coefficient of the `n`th simple-cluster correction monomial in the non-stopping branch. -/
def simpleClusterApproxStepCoeffOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) : k :=
  Classical.choose
    (simpleClusterApprox_exists_stepCoeff_for_stepValue_of_no_root
      k Γ hsmall hunit hnoroot n)

theorem simpleClusterApprox_stepDiff_eq_single_stepValue_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    SimpleClusterChain.stepDiff k Γ
        (simpleClusterApproxOfOneCluster k Γ hsmall hunit) n =
      singleOfNonneg k Γ
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n)
        (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot n)
        (le_of_lt
          (simpleClusterApprox_stepValue_pos_of_no_root k Γ hsmall hunit hnoroot n)) :=
  (Classical.choose_spec
    (simpleClusterApprox_exists_stepCoeff_for_stepValue_of_no_root
      k Γ hsmall hunit hnoroot n)).2

theorem simpleClusterApprox_stepValue_strictMono_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    StrictMono (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot) := by
  intro m n hmn
  rw [simpleClusterApprox_stepValue_eq_evalValue_of_no_root k Γ hsmall hunit hnoroot m,
    simpleClusterApprox_stepValue_eq_evalValue_of_no_root k Γ hsmall hunit hnoroot n]
  exact simpleClusterApprox_evalValue_lt_of_no_root k Γ hsmall hunit hnoroot hmn

theorem simpleClusterApprox_stepValue_range_isPWO_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot)).IsPWO :=
  isPWO_range_of_strictMono_nat
    (simpleClusterApprox_stepValue_strictMono_of_no_root k Γ hsmall hunit hnoroot)

theorem finite_preimage_eq_of_strictMono_nat {α : Type*} [LinearOrder α] {f : ℕ → α}
    (hf : StrictMono f) (a : α) : {n : ℕ | f n = a}.Finite := by
  by_cases h : ∃ n : ℕ, f n = a
  · rcases h with ⟨n, hn⟩
    refine Set.Finite.subset (Set.finite_singleton n) ?_
    intro m hm
    exact hf.injective (hm.trans hn.symm)
  · have hempty : {n : ℕ | f n = a} = ∅ := by
      ext n
      constructor
      · intro hn
        exact False.elim (h ⟨n, hn⟩)
      · intro hn
        exact False.elim hn
    rw [hempty]
    exact Set.finite_empty

/-- A family of single Hahn monomials with injective exponents in a PWO range is summable. -/
noncomputable def singleInjectivePWOSummableFamily
    {I : Type*} (ν : I → Γ) (a : I → k) (hinj : Function.Injective ν)
    (hPWO : (Set.range ν).IsPWO) :
    HahnSeries.SummableFamily Γ k I where
  toFun i := HahnSeries.single (ν i) (a i)
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono hPWO ?_
    intro γ hγ
    rcases Set.mem_iUnion.mp hγ with ⟨i, hi⟩
    exact ⟨i, (HahnSeries.eq_of_mem_support_single hi).symm⟩
  finite_co_support' := by
    intro γ
    have hpre : (ν ⁻¹' ({γ} : Set Γ)).Finite :=
      (Set.finite_singleton γ).preimage (fun _ _ _ _ h => hinj h)
    refine hpre.subset ?_
    intro i hi
    change (HahnSeries.single (ν i) (a i)).coeff γ ≠ 0 at hi
    change ν i = γ
    by_contra hne
    exact hi (HahnSeries.coeff_single_of_ne (fun hγ => hne hγ.symm))

/-- A family of single Hahn monomials indexed by a strictly increasing natural sequence of
exponents is summable. -/
noncomputable def singleStrictMonoSummableFamily
    (ν : ℕ → Γ) (a : ℕ → k) (hν : StrictMono ν) :
    HahnSeries.SummableFamily Γ k ℕ :=
  singleInjectivePWOSummableFamily k Γ ν a hν.injective
      (isPWO_range_of_strictMono_nat hν)

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
@[simp]
theorem singleStrictMonoSummableFamily_apply
    (ν : ℕ → Γ) (a : ℕ → k) (hν : StrictMono ν) (n : ℕ) :
    (singleStrictMonoSummableFamily k Γ ν a hν : ℕ → HahnSeries Γ k) n =
      HahnSeries.single (ν n) (a n) :=
  rfl

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem singleStrictMonoSummableFamily_support_subset_range
    (ν : ℕ → Γ) (a : ℕ → k) (hν : StrictMono ν) :
    (singleStrictMonoSummableFamily k Γ ν a hν).hsum.support ⊆ Set.range ν := by
  intro γ hγ
  have hmem :
      γ ∈ ⋃ n : ℕ, (singleStrictMonoSummableFamily k Γ ν a hν n).support :=
    HahnSeries.SummableFamily.support_hsum_subset hγ
  rcases Set.mem_iUnion.mp hmem with ⟨n, hn⟩
  have hsingle : γ ∈ (HahnSeries.single (ν n) (a n)).support := by
    simpa [singleStrictMonoSummableFamily_apply] using hn
  exact ⟨n, (HahnSeries.eq_of_mem_support_single hsingle).symm⟩

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem support_property_of_subset_range
    {I : Type*} {P : Γ → Prop} {s : HahnSeries Γ k} {ν : I → Γ}
    (hsupport : s.support ⊆ Set.range ν) (hP : ∀ i, P (ν i)) :
    ∀ γ, γ ∈ s.support → P γ := by
  intro γ hγ
  rcases hsupport hγ with ⟨i, rfl⟩
  exact hP i

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem hsum_support_property
    {I : Type*} {P : Γ → Prop} (s : HahnSeries.SummableFamily Γ k I)
    (hP : ∀ i, ∀ γ ∈ (s i).support, P γ) :
    ∀ γ, γ ∈ s.hsum.support → P γ := by
  intro γ hγ
  rcases Set.mem_iUnion.mp (HahnSeries.SummableFamily.support_hsum_subset hγ) with
    ⟨i, hi⟩
  exact hP i γ hi

theorem simpleClusterApprox_stepValue_finite_preimage_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (γ : Γ) :
    {n : ℕ | simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n = γ}.Finite :=
  finite_preimage_eq_of_strictMono_nat
    (simpleClusterApprox_stepValue_strictMono_of_no_root k Γ hsmall hunit hnoroot) γ

/-- The non-stopping simple-cluster correction monomials as a summable Hahn-series family. -/
def simpleClusterCorrectionFamilyOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    HahnSeries.SummableFamily Γ k ℕ where
  toFun n :=
    HahnSeries.single
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n)
      (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot n)
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono
      (simpleClusterApprox_stepValue_range_isPWO_of_no_root k Γ hsmall hunit hnoroot) ?_
    intro γ hγ
    rcases Set.mem_iUnion.mp hγ with ⟨n, hn⟩
    exact ⟨n, (HahnSeries.eq_of_mem_support_single hn).symm⟩
  finite_co_support' := by
    intro γ
    refine (simpleClusterApprox_stepValue_finite_preimage_of_no_root
      k Γ hsmall hunit hnoroot γ).subset ?_
    intro n hn
    change
      (HahnSeries.single
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n)
        (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot n)).coeff γ ≠ 0 at hn
    by_contra hne
    have hne' :
        γ ≠ simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n := by
      intro hγ
      exact hne hγ.symm
    exact hn (HahnSeries.coeff_single_of_ne hne')

@[simp]
theorem simpleClusterCorrectionFamilyOfNoRoot_apply
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    simpleClusterCorrectionFamilyOfNoRoot k Γ hsmall hunit hnoroot n =
      HahnSeries.single
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n)
        (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot n) :=
  rfl

/-- The Hahn-series sum of all non-stopping simple-cluster correction monomials. -/
def simpleClusterCorrectionHahnSeriesOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    HahnSeries Γ k :=
  (simpleClusterCorrectionFamilyOfNoRoot k Γ hsmall hunit hnoroot).hsum

theorem simpleClusterCorrectionHahnSeriesOfNoRoot_support_subset_stepValue_range
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).support ⊆
      Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot) := by
  intro γ hγ
  have hmem :
      γ ∈ ⋃ n : ℕ,
          (simpleClusterCorrectionFamilyOfNoRoot k Γ hsmall hunit hnoroot n).support :=
    HahnSeries.SummableFamily.support_hsum_subset hγ
  rcases Set.mem_iUnion.mp hmem with ⟨n, hn⟩
  have hsingle :
      γ ∈
        (HahnSeries.single
          (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n)
          (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot n)).support := by
    simpa [simpleClusterCorrectionFamilyOfNoRoot_apply] using hn
  exact ⟨n, (HahnSeries.eq_of_mem_support_single hsingle).symm⟩

theorem simpleClusterCorrectionHahnSeriesOfNoRoot_support_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    {γ : Γ}
    (hγ : γ ∈ (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).support) :
    0 < γ := by
  rcases simpleClusterCorrectionHahnSeriesOfNoRoot_support_subset_stepValue_range
      k Γ hsmall hunit hnoroot hγ with ⟨n, rfl⟩
  exact simpleClusterApprox_stepValue_pos_of_no_root k Γ hsmall hunit hnoroot n

/-- The omega correction sum has no support below the initial residual value. -/
theorem simpleClusterCorrectionHahnSeriesOfNoRoot_support_ge_first_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    {γ : Γ}
    (hγ : γ ∈ (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).support) :
    simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot 0 ≤ γ := by
  rcases simpleClusterCorrectionHahnSeriesOfNoRoot_support_subset_stepValue_range
      k Γ hsmall hunit hnoroot hγ with ⟨n, rfl⟩
  exact (simpleClusterApprox_stepValue_strictMono_of_no_root
    k Γ hsmall hunit hnoroot).monotone (Nat.zero_le n)

theorem simpleClusterCorrectionHahnSeriesOfNoRoot_orderTop_nonneg
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    (0 : WithTop Γ) ≤
      (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).orderTop := by
  rw [HahnSeries.zero_le_orderTop_iff]
  by_cases hzero :
      simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot = 0
  · simp [hzero]
  · have hcoeff :
        (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).coeff
          (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).order ≠ 0 := by
      simpa using
        (HahnSeries.coeff_order_eq_zero.not.2 hzero)
    have hmem :
        (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).order ∈
          (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).support := by
      simpa [Function.mem_support] using hcoeff
    exact le_of_lt
      (simpleClusterCorrectionHahnSeriesOfNoRoot_support_pos k Γ hsmall hunit hnoroot hmem)

theorem simpleClusterCorrectionHahnSeriesOfNoRoot_orderTop_pos
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    (0 : WithTop Γ) <
      (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).orderTop := by
  by_cases hzero :
      simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot = 0
  · simp [hzero]
  · rw [HahnSeries.zero_lt_orderTop_iff hzero]
    have hcoeff :
        (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).coeff
          (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).order ≠ 0 := by
      simpa using
        (HahnSeries.coeff_order_eq_zero.not.2 hzero)
    have hmem :
        (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).order ∈
          (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).support := by
      simpa [Function.mem_support] using hcoeff
    exact simpleClusterCorrectionHahnSeriesOfNoRoot_support_pos k Γ hsmall hunit hnoroot hmem

theorem simpleClusterCorrectionHahnSeriesOfNoRoot_coeff_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).coeff
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n) =
      simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot n := by
  rw [simpleClusterCorrectionHahnSeriesOfNoRoot,
    HahnSeries.SummableFamily.coeff_hsum]
  rw [finsum_eq_single
    (fun i =>
      (simpleClusterCorrectionFamilyOfNoRoot k Γ hsmall hunit hnoroot i).coeff
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n))
    n]
  · simp [simpleClusterCorrectionFamilyOfNoRoot_apply]
  · intro m hmn
    rw [simpleClusterCorrectionFamilyOfNoRoot_apply]
    exact HahnSeries.coeff_single_of_ne (by
      intro hval
      exact hmn
        ((simpleClusterApprox_stepValue_strictMono_of_no_root
          k Γ hsmall hunit hnoroot).injective hval.symm))

theorem simpleClusterApprox_ofLex_eq_sum_correction_monomials_range
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    ofLex ((simpleClusterApproxOfOneCluster k Γ hsmall hunit n : valuationSubring k Γ) :
        HahnField k Γ) =
      (Finset.range n).sum
        (fun i =>
          HahnSeries.single
            (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot i)
            (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot i)) := by
  have hsum :
      (Finset.range n).sum
          (fun i =>
            ((SimpleClusterChain.stepDiff k Γ
              (simpleClusterApproxOfOneCluster k Γ hsmall hunit) i :
                valuationSubring k Γ) : HahnField k Γ)) =
        ((simpleClusterApproxOfOneCluster k Γ hsmall hunit n :
          valuationSubring k Γ) : HahnField k Γ) := by
    simpa using congrArg
      (fun x : valuationSubring k Γ => (x : HahnField k Γ))
      (simpleClusterApprox_sum_stepDiff_range_eq k Γ hsmall hunit n)
  calc
    ofLex ((simpleClusterApproxOfOneCluster k Γ hsmall hunit n : valuationSubring k Γ) :
        HahnField k Γ)
        = ofLex ((Finset.range n).sum
            (fun i =>
              ((SimpleClusterChain.stepDiff k Γ
                (simpleClusterApproxOfOneCluster k Γ hsmall hunit) i :
                  valuationSubring k Γ) : HahnField k Γ))) := by
            rw [hsum]
    _ = (Finset.range n).sum
          (fun i =>
            ofLex ((SimpleClusterChain.stepDiff k Γ
              (simpleClusterApproxOfOneCluster k Γ hsmall hunit) i :
                valuationSubring k Γ) : HahnField k Γ)) := by
            exact map_sum (ofLexRingHom k Γ) _ _
    _ = (Finset.range n).sum
          (fun i =>
            HahnSeries.single
              (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot i)
              (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [simpleClusterApprox_stepDiff_eq_single_stepValue_of_no_root
              k Γ hsmall hunit hnoroot i]
            simp [singleOfNonneg_coe]

theorem simpleClusterCorrectionMonomialSumRange_coeff_stepValue_of_lt
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    {i n : ℕ} (hi : i < n) :
    ((Finset.range n).sum
        (fun j =>
          HahnSeries.single
            (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot j)
            (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot j))).coeff
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot i) =
      simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot i := by
  rw [HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [HahnSeries.coeff_single_of_ne]
    intro hval
    exact hji
      ((simpleClusterApprox_stepValue_strictMono_of_no_root
        k Γ hsmall hunit hnoroot).injective hval.symm)
  · intro hi_not
    exact False.elim (hi_not (Finset.mem_range.mpr hi))

theorem simpleClusterCorrectionTail_coeff_stepValue_eq_zero_of_lt
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    {i n : ℕ} (hi : i < n) :
    (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot -
        (Finset.range n).sum
          (fun j =>
            HahnSeries.single
              (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot j)
              (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot j))).coeff
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot i) = 0 := by
  rw [HahnSeries.coeff_sub,
    simpleClusterCorrectionHahnSeriesOfNoRoot_coeff_stepValue,
    simpleClusterCorrectionMonomialSumRange_coeff_stepValue_of_lt k Γ hsmall hunit hnoroot hi,
    sub_self]

theorem simpleClusterCorrectionTail_coeff_eq_zero_of_lt_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    {γ : Γ} {n : ℕ}
    (hγ : γ < simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n) :
    (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot -
        (Finset.range n).sum
          (fun j =>
            HahnSeries.single
              (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot j)
              (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot j))).coeff γ = 0 := by
  by_cases hmem : ∃ i : ℕ,
      γ = simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot i
  · rcases hmem with ⟨i, rfl⟩
    have hi : i < n :=
      (simpleClusterApprox_stepValue_strictMono_of_no_root
        k Γ hsmall hunit hnoroot).lt_iff_lt.mp hγ
    exact simpleClusterCorrectionTail_coeff_stepValue_eq_zero_of_lt
      k Γ hsmall hunit hnoroot hi
  · have hhsum :
        (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).coeff γ = 0 := by
      by_contra hcoeff
      have hsupport :
          γ ∈ (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot).support := by
        simpa [Function.mem_support] using hcoeff
      rcases simpleClusterCorrectionHahnSeriesOfNoRoot_support_subset_stepValue_range
          k Γ hsmall hunit hnoroot hsupport with ⟨i, hi⟩
      exact hmem ⟨i, hi.symm⟩
    have hsum :
        ((Finset.range n).sum
          (fun j =>
            HahnSeries.single
              (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot j)
              (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot j))).coeff γ = 0 := by
      rw [HahnSeries.coeff_sum]
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [HahnSeries.coeff_single_of_ne]
      intro hγj
      exact hmem ⟨j, hγj⟩
    rw [HahnSeries.coeff_sub, hhsum, hsum, sub_zero]

theorem simpleClusterCorrectionTail_orderTop_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
      (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot -
        (Finset.range n).sum
          (fun j =>
            HahnSeries.single
              (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot j)
              (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot j))).orderTop := by
  let T : HahnSeries Γ k :=
    simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot -
      (Finset.range n).sum
        (fun j =>
          HahnSeries.single
            (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot j)
            (simpleClusterApproxStepCoeffOfNoRoot k Γ hsmall hunit hnoroot j))
  change (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
    T.orderTop
  by_cases hT : T = 0
  · simp [hT]
  · by_contra hle
    have hlt :
        T.orderTop <
          (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n :
            WithTop Γ) := lt_of_not_ge hle
    have htop : T.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.mpr hT
    let γ : Γ := WithTop.untop T.orderTop htop
    have horder : T.orderTop = (γ : WithTop Γ) := by
      exact (WithTop.coe_untop T.orderTop htop).symm
    have hγlt :
        γ < simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n := by
      exact WithTop.coe_lt_coe.mp (by simpa [horder] using hlt)
    have hcoeff_ne : T.coeff γ ≠ 0 :=
      HahnSeries.coeff_orderTop_ne horder
    have hcoeff_zero : T.coeff γ = 0 := by
      simpa [T] using
        simpleClusterCorrectionTail_coeff_eq_zero_of_lt_stepValue
          k Γ hsmall hunit hnoroot hγlt
    exact hcoeff_ne hcoeff_zero

/-- The non-stopping simple-cluster correction sum, as a Hahn-field element. -/
def simpleClusterCorrectionHahnFieldOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    HahnField k Γ :=
  toLex (simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot)

/-- The non-stopping simple-cluster correction sum belongs to the natural valuation subring. -/
def simpleClusterCorrectionValuationSubringOfNoRoot
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    valuationSubring k Γ :=
  ⟨simpleClusterCorrectionHahnFieldOfNoRoot k Γ hsmall hunit hnoroot, by
    rw [mem_valuationSubring_iff, addVal_apply]
    simpa [simpleClusterCorrectionHahnFieldOfNoRoot] using
      simpleClusterCorrectionHahnSeriesOfNoRoot_orderTop_nonneg k Γ hsmall hunit hnoroot⟩

theorem simpleClusterCorrectionValuationSubringOfNoRoot_mem_maximalIdeal
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot ∈
      IsLocalRing.maximalIdeal (valuationSubring k Γ) := by
  rw [mem_maximalIdeal_iff_pos_addVal, addVal_apply]
  simpa [simpleClusterCorrectionValuationSubringOfNoRoot,
    simpleClusterCorrectionHahnFieldOfNoRoot] using
    simpleClusterCorrectionHahnSeriesOfNoRoot_orderTop_pos k Γ hsmall hunit hnoroot

theorem simpleClusterCorrectionValuationSubring_sub_approx_addVal_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
      addVal k Γ
        (((simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot -
            simpleClusterApproxOfOneCluster k Γ hsmall hunit n :
              valuationSubring k Γ) : HahnField k Γ)) := by
  rw [addVal_apply]
  change (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
    (ofLexRingHom k Γ
      ((simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
          HahnField k Γ) -
        ((simpleClusterApproxOfOneCluster k Γ hsmall hunit n :
          valuationSubring k Γ) : HahnField k Γ))).orderTop
  rw [map_sub]
  simp only [ofLexRingHom_apply]
  rw [show
      ofLex (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
          HahnField k Γ) =
        simpleClusterCorrectionHahnSeriesOfNoRoot k Γ hsmall hunit hnoroot by
      simp [simpleClusterCorrectionValuationSubringOfNoRoot,
        simpleClusterCorrectionHahnFieldOfNoRoot]]
  rw [simpleClusterApprox_ofLex_eq_sum_correction_monomials_range
    k Γ hsmall hunit hnoroot n]
  exact simpleClusterCorrectionTail_orderTop_ge_stepValue k Γ hsmall hunit hnoroot n

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem addVal_pow_sub_pow_ge_of_ge
    {x y : HahnField k Γ} {δ : Γ}
    (hx : (0 : WithTop Γ) ≤ addVal k Γ x)
    (hy : (0 : WithTop Γ) ≤ addVal k Γ y)
    (hxy : (δ : WithTop Γ) ≤ addVal k Γ (x - y)) :
    ∀ m : ℕ, (δ : WithTop Γ) ≤ addVal k Γ (x ^ m - y ^ m)
  | 0 => by simp
  | m + 1 => by
      have hpowx : (0 : WithTop Γ) ≤ addVal k Γ (x ^ m) := by
        rw [AddValuation.map_pow]
        exact nsmul_nonneg hx m
      have hterm₁ :
          (δ : WithTop Γ) ≤ addVal k Γ (x ^ m * (x - y)) := by
        rw [AddValuation.map_mul]
        have := add_le_add hpowx hxy
        simpa using this
      have hterm₂ :
          (δ : WithTop Γ) ≤ addVal k Γ ((x ^ m - y ^ m) * y) := by
        rw [AddValuation.map_mul]
        have := add_le_add (addVal_pow_sub_pow_ge_of_ge hx hy hxy m) hy
        simpa [add_comm] using this
      have hdecomp :
          x ^ (m + 1) - y ^ (m + 1) =
            x ^ m * (x - y) + (x ^ m - y ^ m) * y := by
        ring
      rw [hdecomp]
      exact (addVal k Γ).map_le_add hterm₁ hterm₂

theorem addVal_eval_map_sub_eval_map_ge_of_ge
    (F : Polynomial (valuationSubring k Γ))
    {x y : HahnField k Γ} {δ : Γ}
    (hx : (0 : WithTop Γ) ≤ addVal k Γ x)
    (hy : (0 : WithTop Γ) ≤ addVal k Γ y)
    (hxy : (δ : WithTop Γ) ≤ addVal k Γ (x - y)) :
    (δ : WithTop Γ) ≤
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval x -
          (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval y) := by
  rw [eval_map_algebraMap_eq_sum_range k Γ F x,
    eval_map_algebraMap_eq_sum_range k Γ F y]
  have hdiff_eq :
      (∑ i ∈ Finset.range (F.natDegree + 1), (F.coeff i : HahnField k Γ) * x ^ i) -
          (∑ i ∈ Finset.range (F.natDegree + 1), (F.coeff i : HahnField k Γ) * y ^ i) =
        ∑ i ∈ Finset.range (F.natDegree + 1),
          ((F.coeff i : HahnField k Γ) * x ^ i -
            (F.coeff i : HahnField k Γ) * y ^ i) := by
    let s := Finset.range (F.natDegree + 1)
    change (∑ i ∈ s, (F.coeff i : HahnField k Γ) * x ^ i) -
          (∑ i ∈ s, (F.coeff i : HahnField k Γ) * y ^ i) =
        ∑ i ∈ s,
          ((F.coeff i : HahnField k Γ) * x ^ i -
            (F.coeff i : HahnField k Γ) * y ^ i)
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
        let A : HahnField k Γ := (F.coeff a : HahnField k Γ) * x ^ a
        let B : HahnField k Γ := (F.coeff a : HahnField k Γ) * y ^ a
        let SX : HahnField k Γ := ∑ i ∈ s, (F.coeff i : HahnField k Γ) * x ^ i
        let SY : HahnField k Γ := ∑ i ∈ s, (F.coeff i : HahnField k Γ) * y ^ i
        let SD : HahnField k Γ :=
          ∑ i ∈ s, ((F.coeff i : HahnField k Γ) * x ^ i -
            (F.coeff i : HahnField k Γ) * y ^ i)
        change A + SX - (B + SY) = A - B + SD
        have hsplit : A + SX - (B + SY) = A - B + (SX - SY) := by
          abel
        rw [hsplit]
        change A - B + (SX - SY) = A - B + SD
        rw [ih]
  rw [hdiff_eq]
  have hsum_eq :
      (∑ i ∈ Finset.range (F.natDegree + 1),
          ((F.coeff i : HahnField k Γ) * x ^ i -
            (F.coeff i : HahnField k Γ) * y ^ i)) =
        ∑ i ∈ Finset.range (F.natDegree + 1),
          (F.coeff i : HahnField k Γ) * (x ^ i - y ^ i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hsum_eq]
  refine (addVal k Γ).map_le_sum ?_
  intro i _
  rw [AddValuation.map_mul]
  have hcoeff : (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i : HahnField k Γ) := by
    exact (F.coeff i).property
  have hpow := addVal_pow_sub_pow_ge_of_ge k Γ hx hy hxy i
  have := add_le_add hcoeff hpow
  simpa using this

theorem addVal_eval_map_sub_eval_zero_ge_of_nonbelow
    (F : Polynomial (valuationSubring k Γ))
    {m : ℕ} {δ γ : Γ} {z : HahnField k Γ}
    (hδpos : 0 < δ) (hscale : m • δ = γ)
    (hz : (δ : WithTop Γ) ≤ addVal k Γ z)
    (hnotBelow :
      ∀ j, 0 < j → j < m →
        (((m - j) • δ : Γ) : WithTop Γ) ≤
          addVal k Γ (F.coeff j : HahnField k Γ)) :
    (γ : WithTop Γ) ≤
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval z -
          (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval 0) := by
  rw [eval_map_algebraMap_eq_sum_range k Γ F z,
    eval_map_algebraMap_eq_sum_range k Γ F 0]
  have hdiff_eq :
      (∑ i ∈ Finset.range (F.natDegree + 1), (F.coeff i : HahnField k Γ) * z ^ i) -
          (∑ i ∈ Finset.range (F.natDegree + 1),
            (F.coeff i : HahnField k Γ) * (0 : HahnField k Γ) ^ i) =
        ∑ i ∈ Finset.range (F.natDegree + 1),
          ((F.coeff i : HahnField k Γ) * z ^ i -
            (F.coeff i : HahnField k Γ) * (0 : HahnField k Γ) ^ i) := by
    let s := Finset.range (F.natDegree + 1)
    change (∑ i ∈ s, (F.coeff i : HahnField k Γ) * z ^ i) -
          (∑ i ∈ s, (F.coeff i : HahnField k Γ) * (0 : HahnField k Γ) ^ i) =
        ∑ i ∈ s,
          ((F.coeff i : HahnField k Γ) * z ^ i -
            (F.coeff i : HahnField k Γ) * (0 : HahnField k Γ) ^ i)
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
        let A : HahnField k Γ := (F.coeff a : HahnField k Γ) * z ^ a
        let B : HahnField k Γ := (F.coeff a : HahnField k Γ) * (0 : HahnField k Γ) ^ a
        let SZ : HahnField k Γ := ∑ i ∈ s, (F.coeff i : HahnField k Γ) * z ^ i
        let S0 : HahnField k Γ := ∑ i ∈ s, (F.coeff i : HahnField k Γ) * (0 : HahnField k Γ) ^ i
        let SD : HahnField k Γ :=
          ∑ i ∈ s, ((F.coeff i : HahnField k Γ) * z ^ i -
            (F.coeff i : HahnField k Γ) * (0 : HahnField k Γ) ^ i)
        change A + SZ - (B + S0) = A - B + SD
        have hsplit : A + SZ - (B + S0) = A - B + (SZ - S0) := by
          abel
        rw [hsplit]
        change A - B + (SZ - S0) = A - B + SD
        rw [ih]
  rw [hdiff_eq]
  have hsum_eq :
      (∑ i ∈ Finset.range (F.natDegree + 1),
          ((F.coeff i : HahnField k Γ) * z ^ i -
            (F.coeff i : HahnField k Γ) * (0 : HahnField k Γ) ^ i)) =
        ∑ i ∈ Finset.range (F.natDegree + 1),
          (F.coeff i : HahnField k Γ) * (z ^ i - (0 : HahnField k Γ) ^ i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hsum_eq]
  refine (addVal k Γ).map_le_sum ?_
  intro i _
  by_cases hi0 : i = 0
  · subst i
    simp
  rw [AddValuation.map_mul]
  have hpow :
      i • (δ : WithTop Γ) ≤
        addVal k Γ (z ^ i - (0 : HahnField k Γ) ^ i) := by
    rw [zero_pow hi0, sub_zero, AddValuation.map_pow]
    exact nsmul_le_nsmul_right hz i
  by_cases hlt : i < m
  · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    have hcoeff := hnotBelow i hi_pos hlt
    calc
      (γ : WithTop Γ) =
          (((m - i) • δ + i • δ : Γ) : WithTop Γ) := by
            rw [← add_nsmul, Nat.sub_add_cancel (le_of_lt hlt), hscale]
      _ = (((m - i) • δ : Γ) : WithTop Γ) + i • (δ : WithTop Γ) := by
            simp [WithTop.coe_add, ← WithTop.coe_nsmul]
      _ ≤ addVal k Γ (F.coeff i : HahnField k Γ) +
            addVal k Γ (z ^ i - (0 : HahnField k Γ) ^ i) :=
            add_le_add hcoeff hpow
  · have hmi : m ≤ i := le_of_not_gt hlt
    have hpow_le : m • (δ : WithTop Γ) ≤ i • (δ : WithTop Γ) := by
      exact_mod_cast nsmul_le_nsmul_left (le_of_lt hδpos) hmi
    have hcoeff_nonneg :
        (0 : WithTop Γ) ≤ addVal k Γ (F.coeff i : HahnField k Γ) :=
      (F.coeff i).property
    calc
      (γ : WithTop Γ) = ((m • δ : Γ) : WithTop Γ) := by rw [hscale]
      _ = m • (δ : WithTop Γ) := by rw [WithTop.coe_nsmul]
      _ ≤ i • (δ : WithTop Γ) := hpow_le
      _ ≤ addVal k Γ (F.coeff i : HahnField k Γ) + i • (δ : WithTop Γ) :=
            le_add_of_nonneg_left hcoeff_nonneg
      _ ≤ addVal k Γ (F.coeff i : HahnField k Γ) +
            addVal k Γ (z ^ i - (0 : HahnField k Γ) ^ i) :=
            add_le_add_right hpow _

theorem addVal_eval_map_sub_eval_map_ge_of_comp_nonbelow
    (F : Polynomial (valuationSubring k Γ)) (A : valuationSubring k Γ)
    {m : ℕ} {δ γ : Γ} {z : HahnField k Γ}
    (hδpos : 0 < δ) (hscale : m • δ = γ)
    (hz : (δ : WithTop Γ) ≤ addVal k Γ z)
    (hnotBelow :
      ∀ j, 0 < j → j < m →
        (((m - j) • δ : Γ) : WithTop Γ) ≤
          addVal k Γ ((F.comp (Polynomial.X + Polynomial.C A)).coeff j :
            HahnField k Γ)) :
    (γ : WithTop Γ) ≤
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            ((A : HahnField k Γ) + z) -
          (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            (A : HahnField k Γ)) := by
  have h :=
    addVal_eval_map_sub_eval_zero_ge_of_nonbelow k Γ
      (F.comp (Polynomial.X + Polynomial.C A))
      (m := m) (δ := δ) (γ := γ) (z := z) hδpos hscale hz hnotBelow
  simpa [Polynomial.map_comp, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Algebra.algebraMap_ofSubsemiring_apply,
    add_comm] using h

theorem simpleClusterCorrection_eval_sub_approx_eval_addVal_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
              HahnField k Γ) -
          (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
            ((simpleClusterApproxOfOneCluster k Γ hsmall hunit n :
              valuationSubring k Γ) : HahnField k Γ)) := by
  exact addVal_eval_map_sub_eval_map_ge_of_ge k Γ F
    (x := (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
      HahnField k Γ))
    (y := ((simpleClusterApproxOfOneCluster k Γ hsmall hunit n :
      valuationSubring k Γ) : HahnField k Γ))
    (δ := simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n)
    (by
      exact (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot).property)
    (by
      exact (simpleClusterApproxOfOneCluster k Γ hsmall hunit n).property)
    (simpleClusterCorrectionValuationSubring_sub_approx_addVal_ge_stepValue
      k Γ hsmall hunit hnoroot n)

theorem simpleClusterCorrection_eval_addVal_ge_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
            HahnField k Γ)) := by
  let z : HahnField k Γ :=
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
        HahnField k Γ)
  let zn : HahnField k Γ :=
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      ((simpleClusterApproxOfOneCluster k Γ hsmall hunit n :
        valuationSubring k Γ) : HahnField k Γ)
  have hdiff :
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
        addVal k Γ (z - zn) := by
    exact simpleClusterCorrection_eval_sub_approx_eval_addVal_ge_stepValue
      k Γ hsmall hunit hnoroot n
  have happrox :
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
        addVal k Γ zn := by
    have happrox_eq :
        addVal k Γ zn =
          (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) := by
      dsimp [zn]
      rw [eval_map_algebraMap_eq_coe_eval]
      change
        addVal k Γ
            ((F.eval (simpleClusterApproxOfOneCluster k Γ hsmall hunit n) :
              valuationSubring k Γ) : HahnField k Γ) =
          (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ)
      rw [simpleClusterApprox_addVal_eval_eq_evalValue_of_no_root,
        ← simpleClusterApprox_stepValue_eq_evalValue_of_no_root]
    exact le_of_eq happrox_eq.symm
  have hdecomp : z = (z - zn) + zn := by
    abel
  change (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
    addVal k Γ z
  rw [hdecomp]
  exact (addVal k Γ).map_le_add hdiff happrox

theorem simpleClusterCorrection_eval_addVal_gt_stepValue
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (n : ℕ) :
    (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) <
      addVal k Γ
        ((F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
          (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
            HahnField k Γ)) := by
  let z : HahnField k Γ :=
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
        HahnField k Γ)
  let zn : HahnField k Γ :=
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      ((simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + 1) :
        valuationSubring k Γ) : HahnField k Γ)
  have hstep_lt_succ :
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n :
          WithTop Γ) <
        (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot (n + 1) :
          WithTop Γ) := by
    exact_mod_cast (simpleClusterApprox_stepValue_strictMono_of_no_root
      k Γ hsmall hunit hnoroot (Nat.lt_succ_self n))
  have hdiff :
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n :
          WithTop Γ) < addVal k Γ (z - zn) := by
    exact lt_of_lt_of_le hstep_lt_succ
      (simpleClusterCorrection_eval_sub_approx_eval_addVal_ge_stepValue
        k Γ hsmall hunit hnoroot (n + 1))
  have happrox :
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n :
          WithTop Γ) < addVal k Γ zn := by
    have happrox_eq :
        addVal k Γ zn =
          (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot (n + 1) :
            WithTop Γ) := by
      dsimp [zn]
      rw [eval_map_algebraMap_eq_coe_eval]
      change
        addVal k Γ
            ((F.eval (simpleClusterApproxOfOneCluster k Γ hsmall hunit (n + 1)) :
              valuationSubring k Γ) : HahnField k Γ) =
          (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot (n + 1) :
            WithTop Γ)
      rw [simpleClusterApprox_addVal_eval_eq_evalValue_of_no_root,
        ← simpleClusterApprox_stepValue_eq_evalValue_of_no_root]
    rw [happrox_eq]
    exact hstep_lt_succ
  have hdecomp : z = (z - zn) + zn := by
    abel
  change
    (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) <
      addVal k Γ z
  rw [hdecomp]
  exact (addVal k Γ).map_lt_add hdiff happrox

theorem simpleClusterCorrection_isRoot_map_of_stepValue_not_bddAbove
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (hnot_bdd :
      ¬ BddAbove
        (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot))) :
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).IsRoot
      (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
        HahnField k Γ) := by
  rw [Polynomial.IsRoot]
  let z : HahnField k Γ :=
    (F.map (algebraMap (valuationSubring k Γ) (HahnField k Γ))).eval
      (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot :
        HahnField k Γ)
  change z = 0
  by_contra hz
  have htop : addVal k Γ z ≠ ⊤ := by
    rw [addVal_apply]
    exact HahnSeries.orderTop_ne_top.mpr (fun hz_ofLex => hz (ofLex.injective hz_ofLex))
  let γ : Γ := WithTop.untop (addVal k Γ z) htop
  have hadd : addVal k Γ z = (γ : WithTop Γ) :=
    (WithTop.coe_untop (addVal k Γ z) htop).symm
  have hbdd :
      BddAbove
        (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot)) := by
    refine ⟨γ, ?_⟩
    intro δ hδ
    rcases hδ with ⟨n, rfl⟩
    apply WithTop.coe_le_coe.mp
    rw [← hadd]
    change
      (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot n : WithTop Γ) ≤
        addVal k Γ z
    exact simpleClusterCorrection_eval_addVal_ge_stepValue k Γ hsmall hunit hnoroot n
  exact hnot_bdd hbdd

theorem simpleClusterCorrection_isRoot_of_stepValue_not_bddAbove
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (hnot_bdd :
      ¬ BddAbove
        (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot))) :
    F.IsRoot (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot) := by
  have hmap :=
    simpleClusterCorrection_isRoot_map_of_stepValue_not_bddAbove
      k Γ hsmall hunit hnoroot hnot_bdd
  rw [Polynomial.IsRoot] at hmap ⊢
  rw [eval_map_algebraMap_eq_coe_eval (k := k) (Γ := Γ) F
    (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot)] at hmap
  exact Subtype.ext hmap

theorem exists_maximalIdeal_root_of_stepValue_not_bddAbove
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (hnot_bdd :
      ¬ BddAbove
        (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot))) :
    ∃ y : valuationSubring k Γ,
      y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y :=
  ⟨simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot,
    simpleClusterCorrectionValuationSubringOfNoRoot_mem_maximalIdeal k Γ hsmall hunit hnoroot,
    simpleClusterCorrection_isRoot_of_stepValue_not_bddAbove
      k Γ hsmall hunit hnoroot hnot_bdd⟩

theorem exists_simpleClusterStep_at_correction_limit_of_not_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n))
    (hlimit_not_root :
      ¬ F.IsRoot (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot)) :
    ∃ y' : valuationSubring k Γ,
      SimpleClusterStep k Γ F
        (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot) y' := by
  refine exists_simpleClusterStep_of_one_cluster k Γ hsmall hunit
    (simpleClusterCorrectionValuationSubringOfNoRoot_mem_maximalIdeal k Γ hsmall hunit hnoroot)
    ?_
  simpa [Polynomial.IsRoot] using hlimit_not_root

theorem exists_maximalIdeal_root_or_bddAbove_step_at_correction_limit_of_no_root
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1))
    (hnoroot : ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)) :
    (∃ y : valuationSubring k Γ,
      y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y) ∨
      BddAbove
        (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot)) ∧
        ∃ y' : valuationSubring k Γ,
          SimpleClusterStep k Γ F
            (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot) y' := by
  by_cases hbdd :
      BddAbove
        (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot))
  · by_cases hroot :
        F.IsRoot (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot)
    · left
      exact ⟨simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot,
        simpleClusterCorrectionValuationSubringOfNoRoot_mem_maximalIdeal k Γ hsmall hunit hnoroot,
        hroot⟩
    · right
      exact ⟨hbdd,
        exists_simpleClusterStep_at_correction_limit_of_not_root
          k Γ hsmall hunit hnoroot hroot⟩
  · left
    exact exists_maximalIdeal_root_of_stepValue_not_bddAbove
      k Γ hsmall hunit hnoroot hbdd

theorem exists_maximalIdeal_root_or_bddAbove_step_at_correction_limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) :
    (∃ y : valuationSubring k Γ,
      y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y) ∨
      ∃ hnoroot : ∀ n : ℕ,
          ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n),
        BddAbove
          (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmall hunit hnoroot)) ∧
          ∃ y' : valuationSubring k Γ,
            SimpleClusterStep k Γ F
              (simpleClusterCorrectionValuationSubringOfNoRoot k Γ hsmall hunit hnoroot) y' := by
  by_cases hfinite :
      ∃ n : ℕ, F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n)
  · left
    exact exists_maximalIdeal_root_of_simpleClusterApprox_root k Γ hsmall hunit hfinite
  · have hnoroot :
        ∀ n : ℕ, ¬ F.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmall hunit n) := by
      intro n hn
      exact hfinite ⟨n, hn⟩
    rcases exists_maximalIdeal_root_or_bddAbove_step_at_correction_limit_of_no_root
        k Γ hsmall hunit hnoroot with hroot | hstep
    · left
      exact hroot
    · right
      exact ⟨hnoroot, hstep⟩

theorem exists_maximalIdeal_root_or_bddAbove_step_at_translated_correction_limit
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F G : Polynomial (valuationSubring k Γ)} {A : valuationSubring k Γ}
    (hG : G = F.comp (Polynomial.X + Polynomial.C A))
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hsmallG : ∀ i, i < 1 → G.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunitG : IsUnit (G.coeff 1)) :
    (∃ y : valuationSubring k Γ,
      y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y) ∨
      ∃ hnoroot : ∀ n : ℕ,
          ¬ G.IsRoot (simpleClusterApproxOfOneCluster k Γ hsmallG hunitG n),
        BddAbove
          (Set.range (simpleClusterApproxStepValueOfNoRoot k Γ hsmallG hunitG hnoroot)) ∧
          ∃ y' : valuationSubring k Γ,
            SimpleClusterStep k Γ F
              (simpleClusterCorrectionValuationSubringOfNoRoot
                k Γ hsmallG hunitG hnoroot + A) y' := by
  subst G
  rcases exists_maximalIdeal_root_or_bddAbove_step_at_correction_limit
      k Γ hsmallG hunitG with hroot | hstep
  · left
    exact exists_maximalIdeal_root_of_comp_X_add_C k Γ hA hroot
  · right
    rcases hstep with ⟨hnoroot, hbdd, z', hzstep⟩
    exact ⟨hnoroot, hbdd, z' + A,
      OddClusterStep.of_comp_X_add_C k Γ hA hzstep⟩

theorem exists_maximalIdeal_root_or_bddAbove_step_at_start
    [IsRealClosed k] [DivisibleBy Γ ℕ]
    {F : Polynomial (valuationSubring k Γ)}
    (hsmall : ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ))
    (hunit : IsUnit (F.coeff 1)) {A : valuationSubring k Γ}
    (hA : A ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ)) :
    (∃ y : valuationSubring k Γ,
      y ∈ IsLocalRing.maximalIdeal (valuationSubring k Γ) ∧ F.IsRoot y) ∨
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
              ∃ y' : valuationSubring k Γ,
                SimpleClusterStep k Γ F
                  (simpleClusterCorrectionValuationSubringOfNoRoot
                    k Γ hsmallA hunitA hnoroot + A) y' := by
  have hclusterA :=
    cluster_coeffs_comp_X_add_C_of_mem_maximalIdeal (k := k) (Γ := Γ)
      (F := F) (m := 1) hsmall hunit hA
  let hsmallA : ∀ i, i < 1 →
      (F.comp (Polynomial.X + Polynomial.C A)).coeff i ∈
        IsLocalRing.maximalIdeal (valuationSubring k Γ) := hclusterA.1
  let hunitA : IsUnit ((F.comp (Polynomial.X + Polynomial.C A)).coeff 1) := hclusterA.2
  rcases exists_maximalIdeal_root_or_bddAbove_step_at_translated_correction_limit
      (k := k) (Γ := Γ) (F := F)
      (G := F.comp (Polynomial.X + Polynomial.C A)) (A := A)
      rfl hA hsmallA hunitA with hroot | hstep
  · left
    exact hroot
  · right
    exact ⟨hsmallA, hunitA, hstep⟩

end HahnField

end

end HahnKaplanskyRealClosedness
