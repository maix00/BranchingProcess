/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Step.FiniteBranches.Survival
public import Probability.Kernel.Step.FiniteBranches.Basic
public import Probability.Sequence.IID.Basic

/-!
# IID realizations of finite partial steps

## Public declarations

- `iidSequenceLaw_apply_survivingPartialSteps` identifies the probability of
  surviving the first $n$ transitions of the canonical IID sequence with the
  explicit finite sum of surviving history weights.
- `pow_apply_univ_ofFinitePartialStep_eq_iidSequenceLaw` identifies the total
  mass of the $n$-step finite partial-step kernel with that canonical IID
  survival probability.

Restricting a canonical IID sequence to its first `n` coordinates gives the
finite product law.  Consequently, the probability that a partial step
survives those coordinates is its kernel survival mass.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α ξ : Type*} [Fintype ξ] [MeasurableSpace ξ]
  [MeasurableSingletonClass ξ]

/-- The canonical IID probability of surviving the first `n` partial
transitions equals the recursively defined survival weight. -/
theorem iidSequenceLaw_apply_survivingPartialSteps
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (hsingleton : ∀ k, ν {k} = weight k) (n : ℕ) (a : α) :
    iidSequenceLaw ν
        ((Combinatorics.Sequence.blockCoordinates 0 (E := ξ) n) ⁻¹'
          (survivingPartialStepHistories next n a : Set (Fin n → ξ))) =
      partialStepSurvivalWeight weight next n a := by
  have hmeas : MeasurableSet
      (survivingPartialStepHistories next n a : Set (Fin n → ξ)) :=
    (survivingPartialStepHistories next n a).finite_toSet.measurableSet
  calc
    _ = (Measure.pi (fun _ : Fin n => ν))
        (survivingPartialStepHistories next n a : Set (Fin n → ξ)) :=
      iidSequenceLaw_measure_blockCoordinates_preimage_eq_pi ν 0 n
        (survivingPartialStepHistories next n a : Set (Fin n → ξ)) hmeas
    _ = partialStepHistoryWeight weight next n a :=
      pi_apply_survivingPartialStepHistories ν weight next hsingleton n a
    _ = _ := partialStepHistoryWeight_eq_survivalWeight weight next n a

/-- Kernel survival mass equals the corresponding canonical IID path-event
probability. -/
theorem pow_apply_univ_ofFinitePartialStep_eq_iidSequenceLaw
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (hsingleton : ∀ k, ν {k} = weight k) (n : ℕ) (a : α)
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] :
    (ofFinitePartialStep weight next ^ n) a Set.univ =
      iidSequenceLaw ν
        ((Combinatorics.Sequence.blockCoordinates 0 (E := ξ) n) ⁻¹'
          (survivingPartialStepHistories next n a : Set (Fin n → ξ))) := by
  rw [pow_apply_univ_ofFinitePartialStep,
    iidSequenceLaw_apply_survivingPartialSteps ν weight next hsingleton]

end ProbabilityTheory.Kernel

end
