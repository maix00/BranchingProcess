/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Roots
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Almost-sure success of repeated fixed-age root trials

The split-schedule API proves that an injectively indexed family of
fixed-age trials has a finite first successful trial whenever its one-trial
success probability is positive. A successful trial supplies `N` distinct
same-generation roots, and `SplitSchedule.freshField_law` gives their
descendant fields the exact product law.

This is a trial-schedule statement. It does not yet identify those trial
roots with the active particles of the process started from
`N₀ < N` particles. That process-level identification, and the corresponding
random-time identification with the exact-`N` ranked environment, remain the
bridge needed before applying the Kingman interface.
-/

open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching
open scoped ENNReal

/-- If a fixed-age trial has positive one-root success probability, then an
injectively indexed sequence of independent root trials succeeds at some
finite trial index almost surely. -/
theorem firstSuccess_ne_top_ae_of_positive
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (hroot : Function.Injective root)
    (duration target : ℕ) (μ : Measure (Step α X))
    [IsProbabilityMeasure μ]
    (hpositive : 0 < ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      (α := α) μ (successSet R duration target)) :
    ∀ᵐ ω ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      firstSuccess R root duration target ω ≠ ⊤ := by
  let ν := RootIndexed.stepFieldLaw (Root := Root) μ
  let p := ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
    (α := α) μ (successSet R duration target)
  let bad : Set (RootIndexed.StepField Root α X) :=
    {ω | firstSuccess R root duration target ω = ⊤}
  have hq_lt : 1 - p < 1 := by
    exact ENNReal.sub_lt_self ENNReal.one_ne_top (by norm_num)
      hpositive.ne'
  have hbad_meas : MeasurableSet bad := by
    dsimp [bad]
    exact RootIndexed.stepFiltration.le duration bad
      (measurableSet_firstSuccess_eq_top_adapted R hR root duration target)
  have hbad_subset (k : ℕ) : bad ⊆
      ⋂ i ∈ Finset.range k, failureEvent R root duration target i := by
    intro ω hω
    change firstSuccess R root duration target ω = ⊤ at hω
    have hnoSuccess : ω ∈ (⋃ i, successEvent R root duration target i)ᶜ := by
      have hω' : firstDeclaredSuccess
          (successEvent R root duration target) ω = ⊤ := by
        simpa [firstSuccess] using hω
      have hEq := firstDeclaredSuccess_eq_top_event
        (successEvent R root duration target)
      rw [← hEq]
      exact hω'
    have hnoSuccessEach : ∀ i, ω ∉ successEvent R root duration target i := by
      simpa only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] using hnoSuccess
    simp only [Set.mem_iInter, Finset.mem_range]
    intro i hi
    rw [failureEvent]
    exact hnoSuccessEach i
  have hbad_bound (k : ℕ) : ν bad ≤ (1 - p) ^ k := by
    calc
      ν bad ≤ ν (⋂ i ∈ Finset.range k,
          failureEvent R root duration target i) := measure_mono (hbad_subset k)
      _ = (1 - p) ^ k := by
        simpa [ν, p] using
          measure_iInter_failureEvent R hR root hroot duration target μ
            (Finset.range k)
  have hpow : Tendsto (fun k : ℕ => (1 - p) ^ k) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq_lt
  have hbad_zero : ν bad = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hbad_bound
    · exact bot_le
  have hbad_compl : ν badᶜ = ν Set.univ := by
    rw [measure_compl hbad_meas (by finiteness), hbad_zero]
    simp
  have hgood : ∀ᵐ ω ∂ν, ω ∈ badᶜ :=
    (ae_mem_iff_measure_eq hbad_meas.compl.nullMeasurableSet).2 hbad_compl
  filter_upwards [hgood] with ω hω
  simpa [bad] using hω

/-- Almost surely some scheduled root has a fixed-age selected population
reaching the requested target. This describes the trial family, without
identifying it with a separate initially smaller active population. -/
theorem ae_exists_successful_root_of_positive
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (hroot : Function.Injective root)
    (duration target : ℕ) (μ : Measure (Step α X))
    [IsProbabilityMeasure μ]
    (hpositive : 0 < ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      (α := α) μ (successSet R duration target)) :
    ∀ᵐ ω ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∃ k, target ≤
        (RootIndexed.StepSelection.population R duration ω (root k)).card := by
  filter_upwards [firstSuccess_ne_top_ae_of_positive R hR root hroot
    duration target μ hpositive] with ω hfinite
  obtain ⟨k, hk : (k : WithTop ℕ) = firstSuccess R root duration target ω⟩ :=
    WithTop.ne_top_iff_exists.mp hfinite
  exact ⟨k,
    (firstSuccess_eq_iff R root duration target k ω).mp hk.symm |>.1⟩

/-- On the first successful trial, the split-schedule root selector chooses
only particles from that successful population. `N ≤ target` ensures the
population contains each of the `N` selected roots. -/
theorem roots_of_firstSuccess_ae_mem_successful_population
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (hroot : Function.Injective root)
    (duration target : ℕ) (fallback : Fin N → Root × TreeNode α)
    (hNtarget : N ≤ target) (μ : Measure (Step α X))
    [IsProbabilityMeasure μ]
    (hpositive : 0 < ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      (α := α) μ (successSet R duration target)) :
    ∀ᵐ ω ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∃ k : ℕ, firstSuccess R root duration target ω = k ∧
        ∀ i : Fin N,
          (roots N R root duration target fallback ω i).1 = root k ∧
          (roots N R root duration target fallback ω i).2 ∈
            RootIndexed.StepSelection.population R duration ω (root k) := by
  filter_upwards [firstSuccess_ne_top_ae_of_positive R hR root hroot
    duration target μ hpositive] with ω hfinite
  obtain ⟨k, hk : (k : WithTop ℕ) = firstSuccess R root duration target ω⟩ :=
    WithTop.ne_top_iff_exists.mp hfinite
  have hfirst : firstSuccess R root duration target ω = k := hk.symm
  refine ⟨k, hfirst, ?_⟩
  intro i
  exact roots_mem_population_of_firstSuccess_eq N R root duration target k
    fallback ω hfirst hNtarget i

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk

end
