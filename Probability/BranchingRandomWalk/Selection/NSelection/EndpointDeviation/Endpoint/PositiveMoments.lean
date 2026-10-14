/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
import Probability.BranchingRandomWalk.Assumptions.Moments
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive endpoint moments along predictable lineages

A generation-measurable address depends only on reproduction marks strictly
before its generation. Consequently, reading the reproduction field at that
random address still has the original one-step law. The resulting uniform
fourth-moment estimate controls positive increments along any predictable
lineage; applying it to the endpoint-minimizing selected lineage still needs
the measurable argmin and one-step selection comparison.
-/

open MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 1000000

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris

set_option maxHeartbeats 1000000 in
/-- A generation-measurable choice of a root/address at depth n sees a
fresh reproduction step with exactly the original law. The proof uses the
independence of all fixed root/address coordinates and the fact that the
choice is measurable with respect to the previous generations. -/
theorem finiteRootStepFieldLaw_predictableStep_map_eq
    (m n : ℕ) (μ : Measure (Combinatorics.Branching.Step ℕ ℝ))
    [IsProbabilityMeasure μ]
    (chosen : FiniteRootStepField m ℕ ℝ → Fin m × TreeNode ℕ)
    (hchosen : Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) n] chosen)
    (hdepth : ∀ field, (chosen field).2.length = n) :
    (finiteRootStepFieldLaw μ m).map
      (fun field => field (chosen field).1 (chosen field).2) = μ := by
  classical
  let P := finiteRootStepFieldLaw μ m
  have hcoord_le (p : Fin m × TreeNode ℕ) :
      RootIndexed.stepCoordinateSpace p ≤
        (inferInstance : MeasurableSpace (FiniteRootStepField m ℕ ℝ)) := by
    let hRoot : Measurable
        (fun field : FiniteRootStepField m ℕ ℝ => field p.1) :=
      measurable_pi_apply p.1
    let hAddress : Measurable
        (fun field : Combinatorics.Branching.StepField ℕ ℝ => field p.2) :=
      measurable_pi_apply p.2
    exact (hAddress.comp hRoot).comap_le
  have hindepCoords : ProbabilityTheory.iIndep
      (RootIndexed.stepCoordinateSpace (Root := Fin m) (α := ℕ) (X := ℝ)) P := by
    simpa [P] using
      RootIndexed.stepFieldLaw_coordinates_independent (Root := Fin m) μ
  have hindepPast (p : Fin m × TreeNode ℕ) (hp : p.2.length = n) :
      ProbabilityTheory.Indep
        (RootIndexed.stepGenerationSpace
          (Root := Fin m) (α := ℕ) (X := ℝ) n)
        (RootIndexed.stepCoordinateSpace p) P := by
    have hdisj : Disjoint
        {q : Fin m × TreeNode ℕ | q.2.length < n} ({p} : Set (Fin m × TreeNode ℕ)) := by
      refine Set.disjoint_left.mpr ?_
      intro q hq hqp
      have hq' : q.2.length < n := hq
      have hqp' : q = p := Set.mem_singleton_iff.mp hqp
      rw [hqp'] at hq'
      omega
    have hindep := ProbabilityTheory.indep_iSup_of_disjoint
      (m := RootIndexed.stepCoordinateSpace
        (Root := Fin m) (α := ℕ) (X := ℝ)) (μ := P)
      hcoord_le hindepCoords hdisj
    rw [← RootIndexed.stepGenerationSpace_eq_coordinate_iSup
      (Root := Fin m) (α := ℕ) (X := ℝ) n] at hindep
    simpa only [iSup_singleton] using hindep

  have hchosenFull : Measurable chosen :=
    hchosen.mono
      ((RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ)).le n)
      le_rfl
  have hfiberFull (p : Fin m × TreeNode ℕ) :
      MeasurableSet {field | chosen field = p} :=
    hchosenFull (measurableSet_singleton p)
  have hfiberPast (p : Fin m × TreeNode ℕ) :
      MeasurableSet[RootIndexed.stepGenerationSpace
        (Root := Fin m) (α := ℕ) (X := ℝ) n]
        {field | chosen field = p} :=
    hchosen (measurableSet_singleton p)
  have hmarkFiltration :
      Measurable[RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ) (n + 1)]
        (fun field : FiniteRootStepField m ℕ ℝ =>
          field (chosen field).1 (chosen field).2) := by
    letI : MeasurableSpace (FiniteRootStepField m ℕ ℝ) :=
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) (n + 1)
    have hchosenSucc : Measurable chosen :=
      hchosen.mono
        ((RootIndexed.stepFiltration
          (Root := Fin m) (α := ℕ) (X := ℝ)).mono' (Nat.le_succ n))
        le_rfl
    have hfiberSucc (p : Fin m × TreeNode ℕ) : MeasurableSet
        {field | chosen field = p} :=
      hchosenSucc (measurableSet_singleton p)
    have hdepth' : ∀ field, (chosen field).2.length < n + 1 := by
      intro field
      rw [hdepth field]
      exact Nat.lt_succ_self n
    have hcount : (Set.range chosen).Countable := by
      exact Set.countable_univ.mono (Set.subset_univ _)
    exact RootIndexed.selectedStep_measurable chosen hfiberSucc hdepth' hcount
  have hmarkMeas : Measurable
      (fun field : FiniteRootStepField m ℕ ℝ =>
        field (chosen field).1 (chosen field).2) :=
    hmarkFiltration.mono
      ((RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ)).le (n + 1))
      le_rfl

  ext A hA
  rw [Measure.map_apply hmarkMeas hA]
  let fiber : (Fin m × TreeNode ℕ) → Set (FiniteRootStepField m ℕ ℝ) :=
    fun p => {field | chosen field = p} ∩
      {field | field p.1 p.2 ∈ A}
  have hfiberMeas (p : Fin m × TreeNode ℕ) : MeasurableSet (fiber p) := by
    have hcoordA : MeasurableSet[RootIndexed.stepCoordinateSpace p]
        {field | field p.1 p.2 ∈ A} := by
      rw [RootIndexed.stepCoordinateSpace,
        MeasurableSpace.measurableSet_comap]
      exact ⟨A, hA, rfl⟩
    have hcoordAFull : MeasurableSet {field : FiniteRootStepField m ℕ ℝ |
        field p.1 p.2 ∈ A} := by
      let hRoot : Measurable
          (fun field : FiniteRootStepField m ℕ ℝ => field p.1) :=
        measurable_pi_apply p.1
      let hAddress : Measurable
          (fun field : Combinatorics.Branching.StepField ℕ ℝ => field p.2) :=
        measurable_pi_apply p.2
      exact (hAddress.comp hRoot) hA
    exact (hfiberFull p).inter hcoordAFull
  have hpair : Pairwise (fun p q => Disjoint (fiber p) (fiber q)) := by
    intro p q hpq
    refine Set.disjoint_left.mpr ?_
    intro field hp hq
    exact hpq ((hp.1.symm).trans hq.1)
  have hunion : (⋃ p : Fin m × TreeNode ℕ, fiber p) =
      {field | field (chosen field).1 (chosen field).2 ∈ A} := by
    ext field
    simp only [Set.mem_iUnion, fiber, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, hAfield⟩
      rw [hp]
      exact hAfield
    · intro hAfield
      exact ⟨chosen field, rfl, hAfield⟩
  have hfiberMeasure (p : Fin m × TreeNode ℕ) (hp : p.2.length = n) :
      P (fiber p) = P {field | chosen field = p} * μ A := by
    have hindep := (ProbabilityTheory.indep_iff_forall_indepSet P).mp
      (hindepPast p hp) {field | chosen field = p}
      {field | field p.1 p.2 ∈ A} (hfiberPast p) (by
        rw [RootIndexed.stepCoordinateSpace,
          MeasurableSpace.measurableSet_comap]
        exact ⟨A, hA, rfl⟩)
    have hfactor := hindep.measure_inter_eq_mul
    have hmarginal : P {field | field p.1 p.2 ∈ A} = μ A := by
      let hRoot : Measurable
          (fun field : FiniteRootStepField m ℕ ℝ => field p.1) :=
        measurable_pi_apply p.1
      let hAddress : Measurable
          (fun field : Combinatorics.Branching.StepField ℕ ℝ => field p.2) :=
        measurable_pi_apply p.2
      let eval : FiniteRootStepField m ℕ ℝ → Combinatorics.Branching.Step ℕ ℝ :=
        fun field => field p.1 p.2
      have heval : Measurable eval := hAddress.comp hRoot
      change P (eval ⁻¹' A) = μ A
      rw [← Measure.map_apply heval hA,
        finiteRootStepFieldLaw_coordinate_marginal μ p.1 p.2]
    simpa [fiber, hmarginal] using hfactor

  have hchosenFibersPair : Pairwise (fun p q => Disjoint
      {field : FiniteRootStepField m ℕ ℝ | chosen field = p}
      {field | chosen field = q}) := by
    intro p q hpq
    refine Set.disjoint_left.mpr ?_
    intro field hp hq
    exact hpq (hp.symm.trans hq)
  have hchosenFibersMeas (p : Fin m × TreeNode ℕ) :
      MeasurableSet {field : FiniteRootStepField m ℕ ℝ | chosen field = p} :=
    hfiberFull p
  have hchosenCover : (⋃ p : Fin m × TreeNode ℕ,
      {field : FiniteRootStepField m ℕ ℝ | chosen field = p}) = Set.univ := by
    ext field
    simp
  have hfiberTsum : (∑' p : Fin m × TreeNode ℕ,
      P {field | chosen field = p}) = 1 := by
    calc
      _ = P (⋃ p : Fin m × TreeNode ℕ,
          {field | chosen field = p}) := by
            symm
            exact measure_iUnion hchosenFibersPair hchosenFibersMeas
      _ = 1 := by rw [hchosenCover, measure_univ]
  have hsumFiber :
      (∑' p : Fin m × TreeNode ℕ, P (fiber p)) = μ A := by
    rw [show (∑' p : Fin m × TreeNode ℕ, P (fiber p)) =
      ∑' p : Fin m × TreeNode ℕ,
        P {field | chosen field = p} * μ A by
          apply tsum_congr
          intro p
          by_cases hp : (p.2.length = n)
          · exact hfiberMeasure p hp
          · have hempty : fiber p = ∅ := by
              ext field
              simp only [fiber, Set.mem_inter_iff, Set.mem_setOf_eq,
                Set.mem_empty_iff_false, iff_false]
              intro h
              have hp' : p.2.length = n := by
                simpa [h.1] using hdepth field
              exact hp hp'
            have hchosenEmpty :
                {field : FiniteRootStepField m ℕ ℝ | chosen field = p} = ∅ := by
              ext field
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              intro h
              apply hp
              simpa [h] using hdepth field
            simp [hempty, hchosenEmpty]]
    calc
      _ = (∑' p : Fin m × TreeNode ℕ,
          P {field | chosen field = p}) * μ A := ENNReal.tsum_mul_right
      _ = μ A := by rw [hfiberTsum]; simp
  change P {field | field (chosen field).1 (chosen field).2 ∈ A} = μ A
  rw [← hunion, measure_iUnion hpair hfiberMeas]
  exact hsumFiber

/-- The step read at a predictable random address is measurable at the next
generation. -/
theorem finiteRootStepFieldLaw_predictableStep_measurable
    (m n : ℕ)
    (chosen : FiniteRootStepField m ℕ ℝ → Fin m × TreeNode ℕ)
    (hchosen : Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) n] chosen)
    (hdepth : ∀ field, (chosen field).2.length = n) :
    Measurable (fun field : FiniteRootStepField m ℕ ℝ =>
      field (chosen field).1 (chosen field).2) := by
  have hchosenSucc : Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) (n + 1)]
      chosen := by
    exact hchosen.mono
      ((RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ)).mono' (Nat.le_succ n))
      le_rfl
  have hfiberSucc (p : Fin m × TreeNode ℕ) : MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) (n + 1)]
      {field | chosen field = p} :=
    hchosenSucc (measurableSet_singleton p)
  have hdepth' : ∀ field, (chosen field).2.length < n + 1 := by
    intro field
    rw [hdepth field]
    exact Nat.lt_succ_self n
  have hcount : (Set.range chosen).Countable := by
    exact Set.countable_univ.mono (Set.subset_univ _)
  have hmarkFiltration : Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) (n + 1)]
      (fun field : FiniteRootStepField m ℕ ℝ =>
        field (chosen field).1 (chosen field).2) :=
    RootIndexed.selectedStep_measurable chosen hfiberSucc hdepth' hcount
  exact hmarkFiltration.mono
    ((RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ)).le (n + 1))
    le_rfl

/-- The fourth-moment hypothesis on the paper's ordered leftmost step is
exactly the fourth moment of slot zero after sorting and applying the
potential. -/
theorem integrable_sortedPotentialImage_positiveSlotZero_pow_four
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hfour : HasLeftmostFourthMoment L) :
    Integrable (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
      (max (value' ξ 0) 0) ^ 4) L.sortedPotentialImage := by
  let f : Combinatorics.Branching.Step ℕ ℝ → ℝ :=
    fun ξ => (max (value' ξ 0) 0) ^ 4
  have hf : Measurable f := by
    exact ((value'_measurable (0 : ℕ)).max measurable_const).pow_const 4
  have hraw : Integrable
      (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
        f ((L.ordering ξ).map L.potential)) L.raw := by
    have hEq : (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
        f ((L.ordering ξ).map L.potential)) =
        fun ξ => (L.leftmostPositivePart ξ) ^ 4 := by
      funext ξ
      have hvalue : value' ((L.ordering ξ).map L.potential) 0 =
          (L.ordering ξ).potentialValue' L.potential 0 := by
        change (((L.ordering ξ).map L.potential) 0).getD 0 = _
        rw [Step.map_apply]
        rfl
      simp [f, StepLaw.leftmostPositivePart, StepLaw.displacement, hvalue]
    rw [hEq]
    exact hfour
  have hcompose : Integrable
      (fun ξ : Combinatorics.Branching.Step ℕ ℝ => f (ξ.map L.potential))
      L.sorted := by
    rw [StepLaw.sorted]
    exact (integrable_map_measure
      ((hf.comp (Step.map_measurable L.potential.measurable_toFun)).aestronglyMeasurable)
      L.ordering.measurable_ordered.aemeasurable).mpr hraw
  change Integrable f
    (L.sorted.map (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
      ξ.map L.potential))
  exact (integrable_map_measure hf.aestronglyMeasurable
    (Step.map_measurable L.potential.measurable_toFun).aemeasurable).mpr
      hcompose

/-- Jensen's finite-sum inequality turns a uniform fourth-moment bound on
nonnegative increments into the expected order n⁴ bound for their sum. This
is the moment-assembly part of the positive endpoint argument, abstracted
from the measurable choice of the leftmost ancestral particle. -/
theorem integral_pow_four_sum_le_of_uniform_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (Y : ℕ → Ω → ℝ) (hYmeas : ∀ k, Measurable (Y k))
    (hYnonneg : ∀ k ω, 0 ≤ Y k ω)
    (C : ℝ)
    (hYfour : ∀ k, k < n → Integrable (fun ω => (Y k ω) ^ 4) P)
    (hYmoment : ∀ k, k < n →
      (∫ ω, (Y k ω) ^ 4 ∂P) = C) :
    Integrable (fun ω => (∑ k ∈ Finset.range n, Y k ω) ^ 4) P ∧
      (∫ ω, (∑ k ∈ Finset.range n, Y k ω) ^ 4 ∂P) ≤ (n : ℝ) ^ 4 * C := by
  classical
  let F : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Y k ω
  let G : Ω → ℝ := fun ω => (n : ℝ) ^ 3 *
    ∑ k ∈ Finset.range n, (Y k ω) ^ 4
  have hsumMeas : Measurable F := by
    dsimp [F]
    exact Finset.measurable_sum (Finset.range n) (fun k hk => hYmeas k)
  have hsumFourMeas : Measurable (fun ω =>
      ∑ k ∈ Finset.range n, (Y k ω) ^ 4) := by
    exact Finset.measurable_sum (Finset.range n) (fun k hk =>
      (hYmeas k).pow_const 4)
  have hGMeas : Measurable G := by
    dsimp [G]
    exact measurable_const.mul hsumFourMeas
  have hsumFourIntegrable : Integrable
      (fun ω => ∑ k ∈ Finset.range n, (Y k ω) ^ 4) P := by
    apply integrable_finsetSum (Finset.range n)
    intro k hk
    exact hYfour k (Finset.mem_range.mp hk)
  have hGIntegrable : Integrable G P := by
    dsimp [G]
    exact hsumFourIntegrable.const_mul ((n : ℝ) ^ 3)
  have hGnonneg (ω : Ω) : 0 ≤ G ω := by
    dsimp [G]
    positivity
  have hpoint (ω : Ω) : F ω ^ 4 ≤ G ω := by
    dsimp [F, G]
    calc
      (∑ k ∈ Finset.range n, Y k ω) ^ 4 =
          (∑ k ∈ Finset.range n, Y k ω) ^ (3 + 1) := by norm_num
      _ ≤ ((Finset.range n).card : ℝ) ^ 3 *
          ∑ k ∈ Finset.range n, (Y k ω) ^ (3 + 1) :=
        pow_sum_le_card_mul_sum_pow
          (fun k hk => hYnonneg k ω) 3
      _ = (n : ℝ) ^ 3 *
          ∑ k ∈ Finset.range n, (Y k ω) ^ 4 := by
        simp [Finset.card_range]
  have hFIntegrable : Integrable (fun ω => F ω ^ 4) P := by
    apply hGIntegrable.mono' (hsumMeas.pow_const 4).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ F ω ^ 4)]
    exact hpoint ω
  have hIntegralBound :
      (∫ ω, F ω ^ 4 ∂P) ≤ (n : ℝ) ^ 4 * C := by
    calc
      (∫ ω, F ω ^ 4 ∂P) ≤ ∫ ω, G ω ∂P :=
        integral_mono_ae hFIntegrable hGIntegrable
          (ae_of_all P hpoint)
      _ = (n : ℝ) ^ 3 *
          ∑ k ∈ Finset.range n, (∫ ω, (Y k ω) ^ 4 ∂P) := by
        dsimp [G]
        rw [integral_const_mul,
          integral_finsetSum (Finset.range n)
            (fun k hk => hYfour k (Finset.mem_range.mp hk))]
      _ = (n : ℝ) ^ 3 * ((n : ℝ) * C) := by
        congr 1
        calc
          (∑ k ∈ Finset.range n, (∫ ω, (Y k ω) ^ 4 ∂P)) =
              ∑ k ∈ Finset.range n, C := by
                apply Finset.sum_congr rfl
                intro k hk
                exact hYmoment k (Finset.mem_range.mp hk)
          _ = (n : ℝ) * C := by simp
      _ = (n : ℝ) ^ 4 * C := by ring
  exact ⟨hFIntegrable, by simpa [F] using hIntegralBound⟩

/-- For any generation-by-generation predictable lineage, the sum of its
positive slot-zero increments has fourth moment at most n⁴ times the paper's
leftmost-step fourth moment. This isolates the probabilistic and moment
assembly part of the endpoint argument; selecting the endpoint-minimizing
address and proving the one-step comparison are separate pathwise lemmas. -/
theorem finiteRootStepFieldLaw_integral_pow_four_sum_predictablePositiveSlotZero_le
    (m n : ℕ) (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (chosen : ∀ k, FiniteRootStepField m ℕ ℝ → Fin m × TreeNode ℕ)
    (hchosen : ∀ k, Measurable[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
        (chosen k))
    (hdepth : ∀ k field, (chosen k field).2.length = k)
    (hfour : HasLeftmostFourthMoment L) :
    Integrable (fun field =>
      (∑ k ∈ Finset.range n,
        max (value' (field (chosen k field).1 (chosen k field).2) 0) 0) ^ 4)
        (finiteRootStepFieldLaw L.sortedPotentialImage m) ∧
      (∫ field,
        (∑ k ∈ Finset.range n,
          max (value' (field (chosen k field).1 (chosen k field).2) 0) 0) ^ 4
        ∂finiteRootStepFieldLaw L.sortedPotentialImage m) ≤
        (n : ℝ) ^ 4 *
          ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw := by
  let P := finiteRootStepFieldLaw L.sortedPotentialImage m
  let Y : ℕ → FiniteRootStepField m ℕ ℝ → ℝ := fun k field =>
    max (value' (field (chosen k field).1 (chosen k field).2) 0) 0
  let Q : ℝ := ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw
  have hstep4 := integrable_sortedPotentialImage_positiveSlotZero_pow_four L hfour
  have hslotMeas : Measurable
      (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
        (max (value' ξ 0) 0) ^ 4) := by
    exact ((value'_measurable (0 : ℕ)).max measurable_const).pow_const 4
  have hslotIntegral :
      (∫ ξ, (max (value' ξ 0) 0) ^ 4 ∂L.sortedPotentialImage) = Q := by
    let f : Combinatorics.Branching.Step ℕ ℝ → ℝ :=
      fun ξ => (max (value' ξ 0) 0) ^ 4
    have hcomposeEq : (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
        f ((L.ordering ξ).map L.potential)) =
        fun ξ => (L.leftmostPositivePart ξ) ^ 4 := by
      funext ξ
      have hvalue : value' ((L.ordering ξ).map L.potential) 0 =
          (L.ordering ξ).potentialValue' L.potential 0 := by
        change (((L.ordering ξ).map L.potential) 0).getD 0 = _
        rw [Step.map_apply]
        rfl
      simp [f, StepLaw.leftmostPositivePart, StepLaw.displacement, hvalue]
    calc
      (∫ ξ, f ξ ∂L.sortedPotentialImage) =
          ∫ ξ, f (ξ.map L.potential) ∂L.sorted := by
        rw [StepLaw.sortedPotentialImage]
        exact integral_map
          (Step.map_measurable L.potential.measurable_toFun).aemeasurable
          hslotMeas.aestronglyMeasurable
      _ = ∫ ξ, f ((L.ordering ξ).map L.potential) ∂L.raw := by
        rw [StepLaw.sorted]
        exact integral_map L.ordering.measurable_ordered.aemeasurable
          ((hslotMeas.comp
            (Step.map_measurable L.potential.measurable_toFun)).aestronglyMeasurable)
      _ = Q := by rw [hcomposeEq]
  have hYmeas : ∀ k, Measurable (Y k) := by
    intro k
    have hmark := finiteRootStepFieldLaw_predictableStep_measurable m k
      (chosen k) (hchosen k) (fun field => hdepth k field)
    simpa only [Y, Function.comp_def] using
      ((value'_measurable (0 : ℕ)).max measurable_const).comp hmark
  have hYnonneg : ∀ k field, 0 ≤ Y k field := by
    intro k field
    exact le_max_right _ _
  have hYfour : ∀ k, k < n → Integrable (fun field => (Y k field) ^ 4) P := by
    intro k hk
    let mark : FiniteRootStepField m ℕ ℝ → Combinatorics.Branching.Step ℕ ℝ :=
      fun field => field (chosen k field).1 (chosen k field).2
    have hmark : Measurable mark := by
      simpa [mark] using finiteRootStepFieldLaw_predictableStep_measurable
        m k (chosen k) (hchosen k) (fun field => hdepth k field)
    have hlaw := finiteRootStepFieldLaw_predictableStep_map_eq m k
      L.sortedPotentialImage (chosen k) (hchosen k)
      (fun field => hdepth k field)
    have htarget : Integrable (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
        (max (value' ξ 0) 0) ^ 4) (P.map mark) := by
      rw [show P.map mark = L.sortedPotentialImage by
        simpa [P, mark] using hlaw]
      exact hstep4
    change Integrable (fun field =>
      ((max (value' (mark field) 0) 0) ^ 4)) P
    exact (integrable_map_measure hslotMeas.aestronglyMeasurable
      hmark.aemeasurable).mp htarget
  have hYmoment : ∀ k, k < n →
      (∫ field, (Y k field) ^ 4 ∂P) = Q := by
    intro k hk
    let mark : FiniteRootStepField m ℕ ℝ → Combinatorics.Branching.Step ℕ ℝ :=
      fun field => field (chosen k field).1 (chosen k field).2
    have hmark : Measurable mark := by
      simpa [mark] using finiteRootStepFieldLaw_predictableStep_measurable
        m k (chosen k) (hchosen k) (fun field => hdepth k field)
    have hlaw := finiteRootStepFieldLaw_predictableStep_map_eq m k
      L.sortedPotentialImage (chosen k) (hchosen k)
      (fun field => hdepth k field)
    have htarget : Integrable (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
        (max (value' ξ 0) 0) ^ 4) (P.map mark) := by
      rw [show P.map mark = L.sortedPotentialImage by
        simpa [P, mark] using hlaw]
      exact hstep4
    change (∫ field,
        ((max (value' (mark field) 0) 0) ^ 4) ∂P) = Q
    rw [← integral_map hmark.aemeasurable
      hslotMeas.aestronglyMeasurable]
    rw [show P.map mark = L.sortedPotentialImage by
      simpa [P, mark] using hlaw]
    exact hslotIntegral
  have hsum := integral_pow_four_sum_le_of_uniform_moments P n Y hYmeas
    hYnonneg Q hYfour hYmoment
  constructor
  · simpa [P, Y] using hsum.1
  · simpa [P, Y, Q] using hsum.2


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
