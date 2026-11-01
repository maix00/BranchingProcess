/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Step.Ordering.Law
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
import Probability.BranchingRandomWalk.Assumptions.Moments
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.PredictableAddress
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import MeasureTheory.Integral.Moments.FiniteSum

/-!
# Positive increment moments along the endpoint-minimizing lineage

## Internal proof declarations

- `integrable_sortedPotentialImage_positiveSlotZero_pow_four` transports the
  leftmost fourth-moment assumption to the ordered step law.
- `finiteRootStepFieldLaw_integral_pow_four_sum_predictablePositiveSlotZero_le`
  applies those bounds to a generation-predictable lineage in the finite-root
  step field.

The module contains the fourth-moment transport from the ordered step law and
its finite-sum assembly. These declarations are proof support for the
endpoint-minimum argument in `Minimum/Lemmas/Lineage.lean`.

For a generation-predictable lineage with positive slot-zero increments
$X_k^+$, the fourth-moment assembly gives
\[
  \mathbb E\!\left[\left(\sum_{k<n}X_k^+\right)^4\right]
       \le n^4\,\mathbb E[(X_0^+)^4].
\]
-/

open MeasureTheory
open scoped ENNReal

section

set_option maxHeartbeats 1000000

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris

lemma integrable_sortedPotentialImage_positiveSlotZero_pow_four
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

/-- For any generation-by-generation predictable lineage, the sum of its
positive slot-zero increments has fourth moment at most n⁴ times the
leftmost-step fourth moment. This isolates the probabilistic and moment
assembly part of the endpoint argument; selecting the endpoint-minimizing
address and proving the one-step comparison are separate pathwise lemmas. -/
lemma finiteRootStepFieldLaw_integral_pow_four_sum_predictablePositiveSlotZero_le
    (m n : ℕ) (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (chosen : ∀ _k, FiniteRootStepField m ℕ ℝ → Fin m × TreeNode ℕ)
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
  have hmarkMeas (k : ℕ) : Measurable (fun field : FiniteRootStepField m ℕ ℝ =>
      field (chosen k field).1 (chosen k field).2) := by
    have hchosenSucc : Measurable[
        RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) (k + 1)]
        (chosen k) :=
      (hchosen k).mono
        ((RootIndexed.stepFiltration
          (Root := Fin m) (α := ℕ) (X := ℝ)).mono' (Nat.le_succ k))
        le_rfl
    have hfiber (p : Fin m × TreeNode ℕ) : MeasurableSet[
        RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) (k + 1)]
        {field | chosen k field = p} :=
      hchosenSucc (measurableSet_singleton p)
    have hdepth' (field : FiniteRootStepField m ℕ ℝ) :
        (chosen k field).2.length < k + 1 := by
      rw [hdepth k field]
      exact Nat.lt_succ_self k
    have hcount : (Set.range (chosen k)).Countable :=
      Set.countable_univ.mono (Set.subset_univ _)
    have hmarkFiltration := RootIndexed.selectedStep_measurable
      (chosen k) hfiber hdepth' hcount
    exact hmarkFiltration.mono
      ((RootIndexed.stepFiltration
        (Root := Fin m) (α := ℕ) (X := ℝ)).le (k + 1)) le_rfl
  have hpredictableLaw (k : ℕ) :
      (finiteRootStepFieldLaw L.sortedPotentialImage m).map
        (fun field => field (chosen k field).1 (chosen k field).2) =
          L.sortedPotentialImage := by
    have hfiber (p : Fin m × TreeNode ℕ) : MeasurableSet[
        RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ) k]
        {field | chosen k field = p} :=
      hchosen k (measurableSet_singleton p)
    simpa [finiteRootStepFieldLaw] using
      RootIndexed.stepFieldLaw_predictableAddress_map_eq
        (Root := Fin m) (α := ℕ) (X := ℝ) (n := k)
        L.sortedPotentialImage (chosen k) hfiber (hdepth k)
        (Set.countable_univ.mono (Set.subset_univ _))
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
    have hmark := hmarkMeas k
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
      simpa [mark] using hmarkMeas k
    have htarget : Integrable (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
        (max (value' ξ 0) 0) ^ 4) (P.map mark) := by
      rw [show P.map mark = L.sortedPotentialImage by
        simpa [P, mark] using hpredictableLaw k]
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
      simpa [mark] using hmarkMeas k
    have htarget : Integrable (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
        (max (value' ξ 0) 0) ^ 4) (P.map mark) := by
      rw [show P.map mark = L.sortedPotentialImage by
        simpa [P, mark] using hpredictableLaw k]
      exact hstep4
    change (∫ field,
        ((max (value' (mark field) 0) 0) ^ 4) ∂P) = Q
    rw [← integral_map hmark.aemeasurable
      hslotMeas.aestronglyMeasurable]
    rw [show P.map mark = L.sortedPotentialImage by
      simpa [P, mark] using hpredictableLaw k]
    exact hslotIntegral
  have hsum := MeasureTheory.integral_pow_sum_le_of_uniform_moment_bound
    P (Finset.range n) 3 Y
    (fun k _ => hYmeas k)
    (fun k _ field => hYnonneg k field)
    Q
    (fun k hk => by simpa using hYfour k (Finset.mem_range.mp hk))
    (fun k hk => (hYmoment k (Finset.mem_range.mp hk)).le)
  constructor
  · simpa [P, Y] using hsum.1
  · simpa [P, Y, Q, Finset.card_range] using hsum.2


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
