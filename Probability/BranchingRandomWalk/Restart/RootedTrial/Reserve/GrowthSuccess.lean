/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.FiniteSlot.Growth
import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.GaltonWatson
import Probability.MeasureTheory.Moments.SecondMomentGrowth
import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.BranchingRandomWalk.Restart.Trial.Basic
import Probability.BranchingRandomWalk.Restart.Trial.RootIndexed
import Probability.BranchingProcess.Offspring.Count
import Probability.BranchingProcess.Offspring.FieldLaw
/-!
# Successful reserve growth trials

This module combines the finite-slot population bound with the observable
reserve-candidate construction. The first theorem gives a uniform positive
probability for a selected reserve population to complete a logarithmic growth
trial. The second transfers almost-sure nonemptiness of selected marks to the
observable success event for each enabled reserve candidate.

## Public declarations

For \(N\ge1\) and exponent \(a\), define the logarithmic horizon

\[d_N=\left\lceil\frac{a\log N+\log 2}{\log\rho}\right\rceil_+.\]

Under the nonempty supercritical offspring hypotheses, a finite reserve
cutoff \(M\) gives, uniformly in \(N\),

\[\mathbb P_{\mathrm{offspringFieldLaw}(L.\mathrm{sorted})}
  \!\left\{\omega:\
    \operatorname{growthTrialSuccess}
      (S,\lfloor N^a\rfloor_+,2^{d_N},d_N,\omega)\right\}
  \ge\frac{1}{4K(\rho,v)},\]

where \(S\) is the cutoff reserve selector and \(K\) is the normalized
second-moment constant.

* `exists_reserveGrowthTrialSuccess_probability_lower_bound` states that under
  nonempty supercritical offspring assumptions there is a finite reserve cutoff
  `M` such that, for every `N ≥ 1`, the probability of a trial reaching
  `⌊N ^ a⌋₊` by generation
  `d = ⌈(a log N + log 2) / log ρ⌉₊`, with upper bound `2 ^ d`, is at least
  `1 / (4 K(ρ, v))`, where `K` is the normalized second-moment constant.
* `selectedReserveSpineCandidateSuccessEvent_of_binary_horizon_ae` states that
  an enabled split candidate satisfies the full trial event almost surely when
  its horizon obeys `2 ^ duration ≤ upper` and every selected mark is almost
  surely nonempty.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)
open ProbabilityTheory.BranchingProcess.GaltonWatson

/-- Under the offspring assumptions, a finite reserve cutoff gives a
supercritical binary selector. Its actual selected population has a uniformly
positive probability of satisfying the complete logarithmic growth-trial
conditions, without a moment assumption on the original offspring law. -/
theorem exists_reserveGrowthTrialSuccess_probability_lower_bound
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
    ∃ M : ℕ, ∀ N : ℕ, ∀ a : ℝ, 1 ≤ N →
      let S : Step.FiniteSelection α X :=
        reserveSelectionBelowPotential
          (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
          L.potential (M : ℝ)
      let law := reserveFiniteOffspringLaw L M
      let ρ := finiteSlotOffspringMeanReal law
      let duration := ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊
      let variance := finiteSlotOffspringSecondMomentReal law - ρ ^ 2
      (offspringFieldLaw L.sorted).real
        {ω | growthTrialSuccess S (⌊(N : ℝ) ^ a⌋₊)
          (2 ^ duration) duration ω} ≥
        1 / (4 * normalizedSecondMomentConstant ρ variance) := by
  obtain ⟨M, hsplit, _hsplitMeas⟩ :=
    exists_nat_cutoff_positive_reserveSplit L hsupercritical
  refine ⟨M, ?_⟩
  intro N a hN
  let R : Step.FiniteSelection α X :=
    Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  let S : Step.FiniteSelection α X :=
    reserveSelectionBelowPotential R L.potential (M : ℝ)
  let ν : ProbabilityMeasure (Step α X) := ⟨L.sorted, inferInstance⟩
  have hRmeas : Measurable R.select := by
    simpa [R] using firstTwoBySlotOrder_measurable (α := α) (X := X)
  have hRcap : R.IsBoundedBy 2 := by
    simpa [R] using
      (Step.FiniteSelection.firstNBySlotOrder_isBoundedBy
        (α := α) (X := X) 2)
  have hSmeas : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable
      R hRmeas L.potential (M : ℝ)
  have hScap : ∀ ξ, (S ξ).card ≤ 2 := by
    intro ξ
    exact reserveSelectionBelowPotential_isBoundedBy
      R L.potential (M : ℝ) hRcap ξ
  have hSnonempty : ∀ᵐ ξ ∂(ν : Measure (Step α X)), (S ξ).Nonempty := by
    simpa [ν, S] using reserveSelectionBelowPotential_nonempty_ae
      L hnonempty (M : ℝ)
  have hSsplit : 0 < (ν : Measure (Step α X))
      {ξ | 2 ≤ (S ξ).card} := by
    simpa [ν, S, splitBy] using hsplit
  have hmean : 1 < finiteSlotOffspringMeanReal
      (finiteOffspringLaw ν S hSmeas) :=
    finiteSlotOffspringMeanReal_gt_one_of_nonempty_and_split ν S hSmeas
      hScap hSnonempty hSsplit
  have hbound := measure_finiteSlotGrowthTrialSuccess_ge_floor_rpow
    L.sorted S hSmeas hScap hSnonempty hmean N a hN
  have hlaw : reserveFiniteOffspringLaw L M =
      finiteOffspringLaw ν S hSmeas := by
    simp [reserveFiniteOffspringLaw, R, S, ν]
  simpa [R, S, ν, hlaw] using hbound

/-- A reserve candidate's growth trial is successful whenever its observable
split is enabled, almost surely, if its binary horizon fits under the cap.
All coordinates belong to the same pre-sampled field; the proof does not
resample a trial after inspecting another trial's outcome. -/
theorem selectedReserveSpineCandidateSuccessEvent_of_binary_horizon_ae
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
      (selectedReserveSpineAlive R r k field ∧
        field r (selectedReserveSpinePath R r k field) ∈ splitBy R) →
      field ∈ selectedReserveSpineCandidateSuccessEvent R growth hR
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
  change selectedReserveSpineAlive R r k field ∧
    field r (selectedReserveSpinePath R r k field) ∈ splitBy R ∧
    growthTrialSuccess growth 1 upper duration
      (fun v => field r
        (((selectedReserveSpineLineages R hR).firstChildRootAt
          R r PUnit.unit (k + 1) field).2 ++ v))
  refine ⟨halive, hsplitCandidate, ?_⟩
  refine growthTrialSuccess_of_population_ge_lower
    growth hcapacity
    (fun v => field r
      (((selectedReserveSpineLineages R hR).firstChildRootAt
        R r PUnit.unit (k + 1) field).2 ++ v))
    (fun v => hmarks (((selectedReserveSpineLineages R hR).firstChildRootAt
      R r PUnit.unit (k + 1) field).2 ++ v))
    1 duration upper hupper ?_
  let trial : Mark α (Step α X) := fun v => field r
    (((selectedReserveSpineLineages R hR).firstChildRootAt
      R r PUnit.unit (k + 1) field).2 ++ v)
  have hpop : (StepSelection.population growth duration trial).Nonempty :=
    StepSelection.population_nonempty_of_all_selected_marks_nonempty growth trial
      (fun v => hmarks (((selectedReserveSpineLineages R hR).firstChildRootAt
        R r PUnit.unit (k + 1) field).2 ++ v)) duration
  exact Finset.card_pos.mpr hpop
end ProbabilityTheory.BranchingRandomWalk
