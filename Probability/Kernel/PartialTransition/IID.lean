import Probability.Kernel.PartialTransition.Survival
import Probability.Sequence.IID

/-!
# IID realizations of finite partial transitions

Restricting a canonical IID sequence to its first `n` coordinates gives the
finite product law.  Consequently, the probability that a partial transition
survives those coordinates is its kernel survival mass.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α ξ : Type*} [Fintype ξ] [MeasurableSpace ξ]
  [MeasurableSingletonClass ξ]

/-- Restriction of a sequence to its first `n` coordinates. -/
def sequencePrefix (n : ℕ) (sequence : ℕ → ξ) : Fin n → ξ :=
  fun k => sequence k

omit [Fintype ξ] [MeasurableSingletonClass ξ] in
/-- A canonical IID sequence restricted to `Fin n` has the finite product
law. -/
theorem iidSequenceLaw_map_sequencePrefix
    (ν : Measure ξ) [IsProbabilityMeasure ν] (n : ℕ) :
    (iidSequenceLaw ν).map (sequencePrefix (ξ := ξ) n) =
      Measure.pi (fun _ : Fin n => ν) := by
  unfold iidSequenceLaw
  change (Measure.infinitePi (fun _ : ℕ => ν)).map
      (fun sequence (k : Fin n) => sequence (k : ℕ)) = _
  rw [Measure.map_infinitePi_infinitePi_of_inj
      (f := fun k : Fin n => (k : ℕ)) Fin.val_injective]
  exact Measure.infinitePi_eq_pi _

/-- The canonical IID probability of surviving the first `n` partial
transitions equals the recursively defined survival weight. -/
theorem iidSequenceLaw_apply_survivingPartialTransitions
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (hsingleton : ∀ k, ν {k} = weight k) (n : ℕ) (a : α) :
    iidSequenceLaw ν
        ((sequencePrefix (ξ := ξ) n) ⁻¹'
          (survivingPartialTransitionHistories next n a : Set (Fin n → ξ))) =
      partialTransitionSurvivalWeight weight next n a := by
  have hmeas : MeasurableSet
      (survivingPartialTransitionHistories next n a : Set (Fin n → ξ)) :=
    (survivingPartialTransitionHistories next n a).finite_toSet.measurableSet
  have hprefix : Measurable (sequencePrefix (ξ := ξ) n) := by
    unfold sequencePrefix
    rw [measurable_pi_iff]
    exact fun k => measurable_pi_apply (k : ℕ)
  calc
    _ = (iidSequenceLaw ν).map (sequencePrefix (ξ := ξ) n)
        (survivingPartialTransitionHistories next n a : Set (Fin n → ξ)) :=
      (Measure.map_apply hprefix hmeas).symm
    _ = (Measure.pi (fun _ : Fin n => ν))
        (survivingPartialTransitionHistories next n a : Set (Fin n → ξ)) := by
      rw [iidSequenceLaw_map_sequencePrefix]
    _ = partialTransitionHistoryWeight weight next n a :=
      pi_apply_survivingPartialTransitionHistories ν weight next hsingleton n a
    _ = _ := partialTransitionHistoryWeight_eq_survivalWeight weight next n a

/-- Kernel survival mass equals the corresponding canonical IID path-event
probability. -/
theorem pow_apply_univ_ofFinitePartialTransition_eq_iidSequenceLaw
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (hsingleton : ∀ k, ν {k} = weight k) (n : ℕ) (a : α)
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] :
    (ofFinitePartialTransition weight next ^ n) a Set.univ =
      iidSequenceLaw ν
        ((sequencePrefix (ξ := ξ) n) ⁻¹'
          (survivingPartialTransitionHistories next n a : Set (Fin n → ξ))) := by
  rw [pow_apply_univ_ofFinitePartialTransition,
    iidSequenceLaw_apply_survivingPartialTransitions ν weight next hsingleton]

end ProbabilityTheory.Kernel
