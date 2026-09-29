module

public import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Return

@[expose] public section

/-!
# Endpoint laws of killed random walks

The endpoint distribution of a killed walk is the image of the IID increment
law restricted to paths that stay in the allowed region.  This identifies
weighted endpoint integrals for the kernel with path-space integrals, not only
the indicator-valued survival probabilities.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableAdd₂ E] [MeasurableSingletonClass E]

/-- The endpoint law of an `n`-step walk, restricted to paths that survive
inside `allowed`. -/
noncomputable def killedEndpointLaw
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (_hallowed : MeasurableSet allowed)
    (n : ℕ) (initial : E) : Measure E :=
  ((iidSequenceLaw ν).restrict
      {increment | StaysIn allowed n initial increment}).map
    (fun increment => initial + partialSum n increment)

/-- The pathwise killed endpoint law is exactly the iterated killed-kernel
transition measure. -/
theorem killedEndpointLaw_eq_killedIncrementKernel_pow_apply
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (n : ℕ) (initial : E) :
    killedEndpointLaw ν allowed hallowed n initial =
      (killedIncrementKernel ν allowed hallowed ^ n) initial := by
  apply Measure.ext
  intro target htarget
  change ((iidSequenceLaw ν).restrict
      {increment | StaysIn allowed n initial increment}).map
        (fun increment => initial + partialSum n increment) target = _
  have hendpoint : Measurable
      (fun increment : ℕ → E => initial + partialSum n increment) :=
    (measurable_const_add initial).comp (partialSum_measurable n)
  rw [Measure.map_apply hendpoint htarget,
    Measure.restrict_apply'
      (measurableSet_staysIn allowed hallowed n initial)]
  rw [killedIncrementKernel_pow_apply_eq_staysIn_endsIn
    ν allowed hallowed target htarget n initial]
  congr 1
  ext increment
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  exact and_comm

/-- Integrating any nonnegative measurable endpoint weight against the killed
kernel is the same as integrating it over surviving increment histories. -/
theorem lintegral_killedIncrementKernel_pow_eq_lintegral_iidSequenceLaw_restrict
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (n : ℕ) (initial : E)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(killedIncrementKernel ν allowed hallowed ^ n) initial =
      ∫⁻ increment, f (initial + partialSum n increment) ∂
        (iidSequenceLaw ν).restrict
          {increment | StaysIn allowed n initial increment} := by
  rw [← killedEndpointLaw_eq_killedIncrementKernel_pow_apply
    ν allowed hallowed n initial, killedEndpointLaw]
  have hendpoint : Measurable
      (fun increment : ℕ → E => initial + partialSum n increment) :=
    (measurable_const_add initial).comp (partialSum_measurable n)
  exact lintegral_map hf hendpoint

end ProbabilityTheory.RandomWalk
