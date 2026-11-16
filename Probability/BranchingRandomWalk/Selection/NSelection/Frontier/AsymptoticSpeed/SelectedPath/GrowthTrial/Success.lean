/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot.Growth
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot.GaltonWatson
import Probability.MeasureTheory.Moments.SecondMomentGrowth
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Causal
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Roots
import Probability.BranchingProcess.Offspring.Count
import Probability.BranchingProcess.Offspring.FieldLaw
/-!
# Successful growth trials

This module combines the finite-slot population bound with the observable
growth-trial candidate construction. The first theorem gives a uniform positive
probability for a selected growth-trial population to complete a logarithmic growth
trial. The second transfers almost-sure nonemptiness of selected marks to the
observable success event for each enabled growth-trial candidate.

## Public declarations

For \(N\ge1\) and exponent \(a\), define the logarithmic horizon

\[d_N=\left\lceil\frac{a\log N+\log 2}{\log\rho}\right\rceil_+.\]

Under the nonempty supercritical offspring hypotheses, a finite potential
cutoff \(M\) gives, uniformly in \(N\),

\[\mathbb P_{\mathrm{offspringFieldLaw}(L.\mathrm{sorted})}
  \!\left\{\omega:\
    \operatorname{growthTrialSuccess}
      (S,\lfloor N^a\rfloor_+,2^{d_N},d_N,\omega)\right\}
  \ge\frac{1}{4K(\rho,v)},\]

where \(S\) is the cutoff selected-growth-trial rule and \(K\) is the normalized
second-moment constant.

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.exists_success_probability_lower_bound` states that under
  nonempty supercritical offspring assumptions there is a finite cutoff
  `M` for which the selector retaining the first two slots with potential
  at most $M$ has mean $\rho>1$, and the path selector has positive split
  probability at the same cutoff. For $N\ge1$ and $a\ge0$, the probability
  of a trial reaching
  `⌊N ^ a⌋₊` by generation
  `d = ⌈(a log N + log 2) / log ρ⌉₊`, with upper bound `2 ^ d`, is at least
  `1 / (4 K(ρ, v))`, where `K` is the normalized second-moment constant.
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.successEvent_of_binary_horizon_ae` states that
  an enabled split candidate satisfies the full trial event almost surely when
  its horizon obeys `2 ^ duration ≤ upper` and every selected mark is almost
  surely nonempty.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial

open ProbabilityTheory.BranchingRandomWalk.Step.Selection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)
open ProbabilityTheory.BranchingProcess.GaltonWatson

/-- The growth trial of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026), Chapter 4,
Theorem 1.1 for $a=0$. A finite cutoff on both selected displacements
gives a supercritical binary selector and a uniform success probability. -/
theorem exists_success_probability_lower_bound
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ :
        ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι X))
    (hsupercritical : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ :
        ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι X)) :
    ∃ M : ℕ,
      let B := Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
      let S := B.belowPotential L.potential (M : ℝ)
      let hS := B.belowPotential_measurable firstTwoBySlotOrder_measurable L.potential (M : ℝ)
      let law := Selection.Stepwise.binaryOffspringLaw ⟨L.sorted, inferInstance⟩ S hS
      let ρ := finiteSlotOffspringMeanReal law
      let variance := finiteSlotOffspringSecondMomentReal law - ρ ^ 2
      1 < ρ ∧ 0 < L.sorted (splitBy (firstOrBelowPotential B L.potential (M : ℝ))) ∧
        ∀ (N : ℕ) (a : ℝ), 1 ≤ N → 0 ≤ a →
        let duration := ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊
        (offspringFieldLaw L.sorted).real
          {ω | growthTrialSuccess S (⌊(N : ℝ) ^ a⌋₊)
            (2 ^ duration) duration ω} ≥
          1 / (4 * normalizedSecondMomentConstant ρ variance) := by
  let B := Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  let ν : ProbabilityMeasure (Step α X) := ⟨L.sorted, inferInstance⟩
  have hB : Measurable B.select := firstTwoBySlotOrder_measurable
  have hBcap : B.IsBoundedBy 2 := firstNBySlotOrder_isBoundedBy 2
  obtain ⟨M₀, hsplit, _⟩ := exists_nat_cutoff_positive_firstOrBelowPotentialSplit L hsupercritical
  have hBne : ∀ᵐ ξ ∂(ν : Measure _), (B ξ).Nonempty := by
    filter_upwards [firstOrBelowPotential_nonempty_ae L hnonempty (M₀ : ℝ)] with ξ hξ
    exact hξ.mono (firstOrBelowPotential_subset B L.potential (M₀ : ℝ) ξ)
  have hBsplit : 0 < (ν : Measure _) {ξ | 2 ≤ (B ξ).card} :=
    hsplit.trans_le (measure_mono fun ξ hξ => hξ.trans
      (Finset.card_le_card (firstOrBelowPotential_subset B L.potential (M₀ : ℝ) ξ)))
  have hmean := finiteSlotOffspringMeanReal_gt_one_of_nonempty_and_split
    ν B hB hBcap hBne hBsplit
  obtain ⟨M, hM⟩ := exists_nat_cutoff_binaryOffspringMean_gt_one ν B hB hBcap L.potential hmean
  let S := B.belowPotential L.potential (M : ℝ)
  have hS : Measurable S.select := B.belowPotential_measurable hB L.potential (M : ℝ)
  have hScap : S.IsBoundedBy 2 := by
    intro ξ
    apply (Finset.card_le_card ?_).trans (hBcap ξ)
    intro i hi
    exact ((Step.FiniteSelection.mem_filter B _ ξ i).mp hi).1
  have hsplitS := measure_selects_two_pos_of_binaryOffspringMean_gt_one ν S hS hScap hM
  have hsplitR : 0 < L.sorted (splitBy (firstOrBelowPotential B L.potential (M : ℝ))) := by
    apply hsplitS.trans_le
    apply measure_mono
    intro ξ hξ
    change 2 ≤ (S ξ).card at hξ
    change 2 ≤ (firstOrBelowPotential B L.potential (M : ℝ) ξ).card
    exact hξ.trans (Finset.card_le_card fun i hi =>
      @Finset.mem_union_right α (Classical.decEq α) _ i _ hi)
  refine ⟨M, hM, hsplitR, ?_⟩
  intro N a hN ha
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlower : 0 < ⌊(N : ℝ) ^ a⌋₊ :=
    Nat.floor_pos.mpr (Real.one_le_rpow hNreal ha)
  exact measure_finiteSlotGrowthTrialSuccess_ge_floor_rpow
    L.sorted S hS hScap hM N a hN (Or.inl hlower)

/-- A growth-trial candidate's growth trial is successful whenever its observable
split is enabled, almost surely, if its binary horizon fits under the cap.
All coordinates belong to the same pre-sampled field; the proof does not
resample a trial after inspecting another trial's outcome. -/
theorem successEvent_of_binary_horizon_ae
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (hnonempty : ∀ᵐ ξ ∂μ, (growth ξ).Nonempty)
    (hcapacity : ∀ ξ, (growth ξ).card ≤ 2)
    (upper duration : ℕ) (hupper : 2 ^ duration ≤ upper)
    (r : Root) (k : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.isAlive R r k field ∧
        ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.splitEvent R r k field) →
      field ∈ ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.successEvent R growth hR
        1 upper duration r k := by
  classical
  let split : Set (Step α X) := {ξ | (growth ξ).Nonempty}
  have hsplit : MeasurableSet split := by
    change MeasurableSet {ξ | (growth ξ).Nonempty}
    have hcard : Measurable (fun ξ : Step α X => (growth ξ).card) :=
      (measurable_of_countable fun s : Finset α => s.card).comp hgrowth
    have heq : {ξ | (growth ξ).Nonempty} =
        {ξ | 0 < (growth ξ).card} := by
      ext ξ
      simp
    rw [heq]
    exact hcard measurableSet_Ioi
  have hsplitOne : μ split = 1 := by
    have hset : split =ᵐ[μ] Set.univ := by
      filter_upwards [hnonempty] with ξ hξ
      simp [split, hξ]
    exact (measure_congr hset).trans (measure_univ)
  have hall : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ u : TreeNode α, (growth (field r u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have heval : Measurable
        (fun field : RootIndexed.StepField Root α X => field r u) :=
      (measurable_pi_apply u).comp (measurable_pi_apply r)
    apply (ae_mem_iff_measure_eq (heval hsplit).nullMeasurableSet).2
    rw [← Measure.map_apply heval hsplit,
      RootIndexed.stepFieldLaw_coordinate_marginal μ r u, hsplitOne]
    simp
  filter_upwards [hall] with field hmarks
  intro hsplitCandidate
  rcases hsplitCandidate with ⟨halive, hsplitCandidate⟩
  change ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.isAlive R r k field ∧
    ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.splitEvent R r k field ∧
    growthTrialSuccess growth 1 upper duration
      (fun v => field r
        ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
          R r PUnit.unit (k + 1) field).2 ++ v))
  refine ⟨halive, hsplitCandidate, ?_⟩
  refine growthTrialSuccess_of_population_ge_lower
    growth hcapacity
    (fun v => field r
      ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
        R r PUnit.unit (k + 1) field).2 ++ v))
    (fun v => hmarks ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
      R r PUnit.unit (k + 1) field).2 ++ v))
    1 duration upper hupper ?_
  let trial : Mark α (Step α X) := fun v => field r
    ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
      R r PUnit.unit (k + 1) field).2 ++ v)
  have hpop : (Selection.Stepwise.population growth duration trial).Nonempty :=
    Selection.Stepwise.population_nonempty_of_all_selected_marks_nonempty growth trial
      (fun v => hmarks ((ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.growthTrialRootAt (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.lineages R hR)
        R r PUnit.unit (k + 1) field).2 ++ v)) duration
  exact Finset.card_pos.mpr hpop
end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial
