/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Basic
public import Probability.Process.RandomWalk.Path.Window
public import Probability.Kernel.Step.Iteration
public import Probability.Kernel.Survival

/-!
# Random walks killed outside a measurable set

Restricting the additive transition kernel to a measurable target set is the
sub-Markov kernel of the walk killed on exit.  Its remaining mass is identified
with the corresponding event under the canonical IID increment law.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableAdd₂ E]

/-- The additive random-walk kernel killed whenever its new position lies
outside `allowed`. -/
noncomputable def killedIncrementKernel (ν : Measure E) [SFinite ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed) : Kernel E E :=
  (incrementKernel ν).restrict hallowed

noncomputable instance killedIncrementKernel.instIsSubMarkovKernel
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed) :
    IsSubMarkovKernel (killedIncrementKernel ν allowed hallowed) := by
  unfold killedIncrementKernel
  infer_instance

/-- The killed increment kernel with its state space restricted to the safe
set itself.  This is the natural state space for uniform survival estimates:
every source state is admissible, while an attempted exit loses mass. -/
noncomputable def killedIncrementKernelOn (ν : Measure E) [SFinite ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed) :
    Kernel allowed allowed :=
  ((incrementKernel ν).comap Subtype.val measurable_subtype_coe).comapRight
    (MeasurableEmbedding.subtype_coe hallowed)

noncomputable instance killedIncrementKernelOn.instIsSubMarkovKernel
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed) :
    IsSubMarkovKernel (killedIncrementKernelOn ν allowed hallowed) := by
  unfold killedIncrementKernelOn
  infer_instance

/-- One-step remaining mass on the restricted state space is exactly the
probability that the translated increment remains in the safe set. -/
theorem killedIncrementKernelOn_apply_univ
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed) (x : allowed) :
    killedIncrementKernelOn ν allowed hallowed x univ =
      ν {z | (x : E) + z ∈ allowed} := by
  rw [killedIncrementKernelOn,
    Kernel.comapRight_apply' _ (MeasurableEmbedding.subtype_coe hallowed)
      x MeasurableSet.univ,
    Kernel.comap_apply', incrementKernel_apply ν,
    Measure.map_apply (measurable_const_add (x : E))]
  · congr 1
    ext z
    simp
  · exact (MeasurableEmbedding.subtype_coe hallowed).measurableSet_image.2
      MeasurableSet.univ

/-- Mapping the restricted-state kernel back to the ambient space recovers
the ambient killed kernel at every admissible source state. -/
theorem map_killedIncrementKernelOn_apply
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed) (x : allowed) :
    (killedIncrementKernelOn ν allowed hallowed x).map Subtype.val =
      killedIncrementKernel ν allowed hallowed (x : E) := by
  rw [killedIncrementKernelOn, Kernel.comapRight_apply,
    (MeasurableEmbedding.subtype_coe hallowed).map_comap,
    Subtype.range_coe, Kernel.comap_apply, killedIncrementKernel,
    Kernel.restrict_apply]

/-- Restricting the state space does not change survival mass at any
admissible starting point, for any number of steps. -/
theorem killedIncrementKernelOn_remainingMass
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (n : ℕ) (x : allowed) :
    Kernel.remainingMass (killedIncrementKernelOn ν allowed hallowed) n x =
      Kernel.remainingMass (killedIncrementKernel ν allowed hallowed)
        n (x : E) := by
  induction n generalizing x with
  | zero =>
      rw [Kernel.remainingMass_zero, Kernel.remainingMass_zero]
  | succ n ih =>
      rw [show n + 1 = 1 + n by omega,
        Kernel.remainingMass_add, Kernel.remainingMass_add]
      simp only [pow_one]
      have hmap := map_killedIncrementKernelOn_apply
        ν allowed hallowed x
      rw [← hmap, MeasureTheory.lintegral_map]
      · simp_rw [ih]
      · exact (Kernel.measurable_coe _ MeasurableSet.univ)
      · exact measurable_subtype_coe

/-- One additive step, killed when its target is outside `allowed`. -/
noncomputable def killedStep (allowed : Set E) (x z : E) : Option E :=
  @ite (Option E) (x + z ∈ allowed) (Classical.propDecidable _)
    (some (x + z)) none

theorem measurableSet_staysIn (allowed : Set E)
    (hallowed : MeasurableSet allowed) (n : ℕ) (initial : E) :
    MeasurableSet {increment : ℕ → E |
      StaysIn allowed n initial increment} := by
  rw [show {increment : ℕ → E | StaysIn allowed n initial increment} =
      ⋂ k : Fin n,
        {increment | initial + partialSum (k + 1) increment ∈ allowed} by
    ext increment
    simp [StaysIn]]
  exact MeasurableSet.iInter fun k => hallowed.preimage
    (measurable_const.add (partialSum_measurable (k + 1)))

/-- The option-valued additive step killed outside a measurable set is jointly
measurable in its current state and increment. -/
theorem killedStep_measurable (allowed : Set E)
    (hallowed : MeasurableSet allowed) :
    Measurable (Function.uncurry (killedStep allowed)) := by
  classical
  unfold killedStep
  exact Measurable.ite (hallowed.preimage measurable_add)
    (measurable_option_some.comp measurable_add) measurable_const

/-- Kernel restriction agrees with the direct option-valued realization of
the killed additive step. -/
theorem killedIncrementKernel_eq_ofPartialStep
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed) :
    killedIncrementKernel ν allowed hallowed =
      Kernel.ofPartialStep ν
        (killedStep allowed)
        (killedStep_measurable allowed hallowed) := by
  ext x target htarget
  rw [killedIncrementKernel, Kernel.restrict_apply' _ hallowed _ htarget,
    Kernel.ofPartialStep_apply ν _ _ x target htarget,
    incrementKernel_apply ν, Measure.map_apply
      (measurable_const_add x) (htarget.inter hallowed)]
  congr 1
  ext z
  classical
  by_cases hz : x + z ∈ allowed <;> simp [killedStep, hz]

omit [MeasurableSpace E] [MeasurableAdd₂ E] in
/-- Survival of the direct killed step is exactly the path event `StaysIn`. -/
theorem survivesPrefix_killedStep_iff
    (allowed : Set E) (n : ℕ) (initial : E) (increment : ℕ → E) :
    Kernel.SurvivesPrefix
        (killedStep allowed)
        n initial increment ↔
      StaysIn allowed n initial increment := by
  induction n generalizing initial increment with
  | zero => simp [StaysIn, Kernel.SurvivesPrefix, Kernel.Survives,
      Kernel.runPartialSteps]
  | succ n ih =>
      classical
      rw [Kernel.survivesPrefix_succ_iff, staysIn_succ_iff]
      by_cases hfirst : initial + increment 0 ∈ allowed
      · simp [killedStep, hfirst, ih]
      · simp [killedStep, hfirst]

/-- Remaining mass of the killed increment kernel is the probability that
the IID random walk remains in the allowed set through the prescribed time. -/
theorem killedIncrementKernel_pow_apply_univ
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (n : ℕ) (initial : E) :
    (killedIncrementKernel ν allowed hallowed ^ n) initial univ =
      iidSequenceLaw ν {increment | StaysIn allowed n initial increment} := by
  rw [killedIncrementKernel_eq_ofPartialStep ν allowed hallowed,
    Kernel.pow_apply_univ_ofPartialStep_eq_iidSequenceLaw]
  congr 1
  ext increment
  exact survivesPrefix_killedStep_iff allowed n initial increment

/-- The restricted-state kernel has the same canonical IID path-survival
interpretation, now with every possible source state lying in `allowed`. -/
theorem killedIncrementKernelOn_remainingMass_eq_iidSequenceLaw
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (n : ℕ) (initial : allowed) :
    Kernel.remainingMass (killedIncrementKernelOn ν allowed hallowed)
        n initial =
      iidSequenceLaw ν
        {increment | StaysIn allowed n (initial : E) increment} := by
  rw [killedIncrementKernelOn_remainingMass]
  exact killedIncrementKernel_pow_apply_univ
    ν allowed hallowed n (initial : E)

/-- Closed-interval survival under an arbitrary IID increment law, expressed
as the remaining mass of the corresponding killed additive kernel. -/
theorem killedIncrementKernel_Icc_pow_apply_univ
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper : ℝ) (n : ℕ) (initial : ℝ)
    (hinitial : initial ∈ Set.Icc lower upper) :
    (killedIncrementKernel ν (Set.Icc lower upper) measurableSet_Icc ^ n)
        initial univ =
      independentIncrementLaw ν
        {increment | InClosedInterval lower upper n initial increment} := by
  rw [killedIncrementKernel_pow_apply_univ]
  congr 1
  ext increment
  exact staysIn_Icc_iff_inClosedInterval
    lower upper n initial hinitial increment

end ProbabilityTheory.RandomWalk
