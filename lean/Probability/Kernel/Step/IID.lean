import Probability.Kernel.Step.Survival
import Probability.Kernel.Step.Iteration
import Probability.Sequence.IID

/-!
# IID realizations of finite partial steps

Restricting a canonical IID sequence to its first `n` coordinates gives the
finite product law.  Consequently, the probability that a partial step
survives those coordinates is its kernel survival mass.
-/

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
        ((sequencePrefix (ξ := ξ) n) ⁻¹'
          (survivingPartialStepHistories next n a : Set (Fin n → ξ))) =
      partialStepSurvivalWeight weight next n a := by
  have hmeas : MeasurableSet
      (survivingPartialStepHistories next n a : Set (Fin n → ξ)) :=
    (survivingPartialStepHistories next n a).finite_toSet.measurableSet
  have hprefix : Measurable (sequencePrefix (ξ := ξ) n) :=
    sequencePrefix_measurable n
  calc
    _ = (iidSequenceLaw ν).map (sequencePrefix (ξ := ξ) n)
        (survivingPartialStepHistories next n a : Set (Fin n → ξ)) :=
      (Measure.map_apply hprefix hmeas).symm
    _ = (Measure.pi (fun _ : Fin n => ν))
        (survivingPartialStepHistories next n a : Set (Fin n → ξ)) := by
      rw [iidSequenceLaw_map_sequencePrefix]
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
        ((sequencePrefix (ξ := ξ) n) ⁻¹'
          (survivingPartialStepHistories next n a : Set (Fin n → ξ))) := by
  rw [pow_apply_univ_ofFinitePartialStep,
    iidSequenceLaw_apply_survivingPartialSteps ν weight next hsingleton]

end ProbabilityTheory.Kernel
