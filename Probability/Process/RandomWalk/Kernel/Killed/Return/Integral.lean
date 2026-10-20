/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Return.Basic

/-!
# Endpoint laws of killed random walks

For a probability measure $\nu$, measurable allowed set $A$, and initial
point $x$, the public declarations are:

- `killedEndpointLaw`: the image law of the endpoint of the IID walk
  restricted to histories that stay in $A$ for $n$ steps.
- `killedEndpointLaw_eq_killedIncrementKernel_pow_apply`: this endpoint law
  is the transition measure $(\kappa_A^n)(x,\cdot)$.
- `lintegral_killedIncrementKernel_pow_eq_lintegral_iidSequenceLaw_restrict`:
  for every measurable $f:E\to[0,\infty]$, integration against the killed
  transition measure equals integration of $f$ of the partial-sum endpoint
  over the IID law restricted to surviving histories.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.RandomWalk


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
    (fun increment => initial + AdditivePath.displacement n increment)

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
        (fun increment => initial + AdditivePath.displacement n increment) target = _
  have hendpoint : Measurable
      (fun increment : ℕ → E => initial + AdditivePath.displacement n increment) :=
    (measurable_const_add initial).comp (displacement_measurable n)
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
      ∫⁻ increment, f (initial + AdditivePath.displacement n increment) ∂
        (iidSequenceLaw ν).restrict
          {increment | StaysIn allowed n initial increment} := by
  rw [← killedEndpointLaw_eq_killedIncrementKernel_pow_apply
    ν allowed hallowed n initial, killedEndpointLaw]
  have hendpoint : Measurable
      (fun increment : ℕ → E => initial + AdditivePath.displacement n increment) :=
    (measurable_const_add initial).comp (displacement_measurable n)
  exact lintegral_map hf hendpoint

end ProbabilityTheory.RandomWalk
