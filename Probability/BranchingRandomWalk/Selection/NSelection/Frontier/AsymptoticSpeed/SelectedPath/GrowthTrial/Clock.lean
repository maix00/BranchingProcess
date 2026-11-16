/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Causal
import Probability.BranchingProcess.Offspring.FieldLaw
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.RecursiveClock
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.SampledMark
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitTime.Finite
import Probability.Independence.FiniteEventCount

/-!
# First successful growth trial along a selected path

## Public declarations

* `measure_firstSuccessfulCompletion_gt_le`: for split probability $q>0$
  and one-trial failure probability $r$, if $K \le nq/4$, then
  $\mathbb P(\tau>n+d)\le e^{-nq/4}+r^K$. Here $d$ is the duration
  of each growth trial.

The two terms bound the probability of too few splits by time $n$ and the
probability of failure of the first $K$ growth trials. This is the clock
estimate in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1
for $a=0$.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

noncomputable section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime

/-- The two clock failure terms in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1, case $a=0$. -/
theorem measure_firstSuccessfulCompletion_gt_le
    {Root : Type} {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (hne : μ {ξ | (R ξ).Nonempty} = 1) (hsplit : 0 < μ (splitBy R))
    (lower upper duration n K : ℕ) (hn : 0 < n) (r : Root)
    (hK : (K : ℝ) ≤ (n : ℝ) * (μ (splitBy R)).toReal / 4) :
    let P := RootIndexed.stepFieldLaw (Root := Root) μ
    P {ω | ((n + duration : ℕ) : WithTop ℕ) <
      firstSuccessfulCompletion R growth hR lower upper duration r ω} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * (μ (splitBy R)).toReal / 4))) +
        (offspringFieldLaw μ {ω | ¬ growthTrialSuccess growth lower upper duration ω}) ^ K := by
  classical
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let step := Coupling.step R r
  let E := splitBy R
  let few := {ω | splitCount R r n ω < K}
  let failed := (fun ω : RootIndexed.StepField Root α X => ω r) ⁻¹'
    recursiveFailure R growth duration lower upper K
  have hmeas := Coupling.step_measurable R hR r
  have hlaw := Coupling.step_law μ R hR r
  have hE := splitBy_measurable R hR
  have hcount := measure_iidEventCount_le_quarter_mean P step (Finset.range n) 0
    (Finset.mem_range.mpr hn) E hE hmeas (Coupling.step_iIndepFun μ R hR r)
    (fun i _ => ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable,
      (hlaw i).trans (hlaw 0).symm⟩)
  have hprob : P (step 0 ⁻¹' E) = μ E := by
    rw [← Measure.map_apply (hmeas 0) hE, hlaw 0]
  simp only [Finset.card_range, hprob] at hcount
  have hall : ∀ᵐ ω ∂P, ∀ u, (R (ω r u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have hneMeas : MeasurableSet {ξ | (R ξ).Nonempty} := by
      have hm : Measurable (fun ξ => (R ξ).card) :=
        (measurable_of_countable fun s : Finset α => s.card).comp hR
      have heq : {ξ | (R ξ).Nonempty} = (fun ξ => (R ξ).card) ⁻¹' Set.Ioi 0 := by
        ext ξ
        exact Finset.card_pos.symm
      rw [heq]
      exact hm measurableSet_Ioi
    have heval : Measurable (fun ω : RootIndexed.StepField Root α X => ω r u) :=
      (measurable_pi_apply u).comp (measurable_pi_apply r)
    apply (ae_mem_iff_measure_eq (heval hneMeas).nullMeasurableSet).2
    rw [← Measure.map_apply heval hneMeas, RootIndexed.stepFieldLaw_coordinate_marginal μ r u, hne]
    exact measure_univ.symm
  have alive (ω : RootIndexed.StepField Root α X) (h : ∀ u, (R (ω r u)).Nonempty) :
      ∀ j, isAlive R r j ω := by
    intro j
    induction j with
    | zero => trivial
    | succ j ih => exact ⟨ih, h _⟩
  have hfew : P few ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * (μ E).toReal / 4))) := by
    refine (measure_mono_ae ?_).trans hcount
    filter_upwards [hall] with ω hω hf
    change splitCount R r n ω < K at hf
    have heq : (∑ i ∈ Finset.range n, E.indicator (fun _ => (1 : ℝ)) (step i ω)) =
        (splitCount R r n ω : ℝ) := by
      rw [splitCount_eq_sum_indicators, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [Set.indicator, alive ω hω i, E, step, Coupling.step, splitEvent, apply_ite]
    change (∑ i ∈ Finset.range n, E.indicator (fun _ => (1 : ℝ)) (step i ω)) ≤ _
    rw [heq]
    exact (by exact_mod_cast hf.le : (splitCount R r n ω : ℝ) ≤ K).trans hK
  have hfinite := selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    μ R hR hne hE hsplit
  have hfailed : P failed =
      (offspringFieldLaw μ {ω | ¬ growthTrialSuccess growth lower upper duration ω}) ^ K := by
    have hm : Measurable (fun ω : RootIndexed.StepField Root α X => ω r) :=
      measurable_pi_apply r
    change P ((fun ω : RootIndexed.StepField Root α X => ω r) ⁻¹'
      recursiveFailure R growth duration lower upper K) = _
    rw [← Measure.map_apply hm (recursiveFailure_measurable R growth hR hgrowth duration lower upper K),
      RootIndexed.stepFieldLaw_root_marginal μ r,
      measure_recursiveFailure_eq_pow μ R growth hR hgrowth duration lower upper hfinite K]
  have hsub : {ω | ((n + duration : ℕ) : WithTop ℕ) <
      firstSuccessfulCompletion R growth hR lower upper duration r ω} ≤ᵐ[P] few ∪ failed := by
    filter_upwards [hall] with ω hω hlate
    by_cases hf : ω ∈ few
    · exact Or.inl hf
    refine Or.inr (mem_recursiveFailure_of_no_success R growth hR lower upper duration K r ω hω n
      (le_of_not_gt hf) ?_)
    intro j hj hsuccess
    apply hlate.not_ge
    apply (firstDeclaredSuccess_le_iff _ ω (n + duration)).2
    exact ⟨j + 1 + duration, by omega, j, rfl, hsuccess⟩
  exact ((measure_mono_ae hsub).trans (measure_union_le _ _)).trans
    (add_le_add hfew hfailed.le)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial

end
