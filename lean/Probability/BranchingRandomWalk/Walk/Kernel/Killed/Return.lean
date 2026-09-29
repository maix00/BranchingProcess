import Probability.BranchingRandomWalk.Walk.Kernel.Killed
import Probability.Kernel.Step.Endpoint
import Probability.Kernel.Survival.Return

/-!
# Killed block kernels returning to an interior set

One transition of `returnKernel` runs a killed kernel for a prescribed number
of steps and retains only endpoints in a measurable return set.  Iterating
this kernel is the natural blocking device for corridor lower bounds: every
new block starts in the strict interior state space.
-/

open MeasureTheory Set

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableAdd₂ E]

/-- Run the additive walk killed outside `allowed` for `length` steps, then
retain only endpoints in `returnSet`.  Both the source and target state spaces
are the return set itself. -/
noncomputable def returnKernel (ν : Measure E) [SFinite ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (returnSet : Set E) (hreturn : MeasurableSet returnSet)
    (length : ℕ) : Kernel returnSet returnSet :=
  Kernel.returnKernel (killedIncrementKernel ν allowed hallowed)
    returnSet hreturn length

noncomputable instance returnKernel.instIsSubMarkovKernel
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (returnSet : Set E) (hreturn : MeasurableSet returnSet)
    (length : ℕ) :
    IsSubMarkovKernel
      (returnKernel ν allowed hallowed returnSet hreturn length) := by
  unfold returnKernel
  infer_instance

/-- The mass of one return block is the killed `length`-step transition mass
whose endpoint lies in `returnSet`. -/
theorem returnKernel_apply_univ
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (returnSet : Set E) (hreturn : MeasurableSet returnSet)
    (length : ℕ) (x : returnSet) :
    returnKernel ν allowed hallowed returnSet hreturn length x univ =
      (killedIncrementKernel ν allowed hallowed ^ length)
        (x : E) returnSet := by
  exact Kernel.returnKernel_apply_univ
    (killedIncrementKernel ν allowed hallowed)
    returnSet hreturn length x

/-- One return-block mass is the canonical IID event that the killed partial
step survives and its endpoint belongs to the return set. -/
theorem returnKernel_apply_univ_eq_iidSequenceLaw
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (returnSet : Set E) (hreturn : MeasurableSet returnSet)
    (length : ℕ) (x : returnSet) :
    returnKernel ν allowed hallowed returnSet hreturn length x univ =
      iidSequenceLaw ν {sequence |
        Kernel.EndsInPrefix (killedStep allowed) returnSet
          length (x : E) sequence} := by
  rw [returnKernel_apply_univ,
    killedIncrementKernel_eq_ofPartialStep ν allowed hallowed,
    Kernel.pow_apply_ofPartialStep_eq_iidSequenceLaw
      ν (killedStep allowed) (killedStep_measurable allowed hallowed)
      hreturn length (x : E)]

omit [MeasurableSpace E] [MeasurableAdd₂ E] in
/-- On a surviving path, executing the killed additive partial step gives the
usual partial-sum endpoint. -/
theorem runPartialSteps_killedStep_sequencePrefix_eq_some
    (allowed : Set E) (n : ℕ) (initial : E) (increment : ℕ → E)
    (hsurvives : StaysIn allowed n initial increment) :
    Kernel.runPartialSteps (killedStep allowed) n initial
        (Kernel.sequencePrefix n increment) =
      some (initial + partialSum n increment) := by
  induction n generalizing initial increment with
  | zero => simp [Kernel.runPartialSteps, partialSum]
  | succ n ih =>
      have h := (staysIn_succ_iff allowed n initial increment).1 hsurvives
      have htail : Fin.tail (Kernel.sequencePrefix (n + 1) increment) =
          Kernel.sequencePrefix n (fun k => increment (k + 1)) := by
        funext k
        rfl
      rw [Kernel.runPartialSteps, htail]
      change ((killedStep allowed initial (increment 0)).bind fun b =>
        Kernel.runPartialSteps (killedStep allowed) n b
          (Kernel.sequencePrefix n (fun k => increment (k + 1)))) = _
      rw [show killedStep allowed initial (increment 0) =
          some (initial + increment 0) by simp [killedStep, h.1]]
      simp only [Option.bind_some]
      rw [ih _ _ h.2, partialSum_succ_eq_head_add_tail]
      ac_rfl

omit [MeasurableSpace E] [MeasurableAdd₂ E] in
/-- On a killed path, execution returns `none`. -/
theorem runPartialSteps_killedStep_sequencePrefix_eq_none
    (allowed : Set E) (n : ℕ) (initial : E) (increment : ℕ → E)
    (hkilled : ¬StaysIn allowed n initial increment) :
    Kernel.runPartialSteps (killedStep allowed) n initial
        (Kernel.sequencePrefix n increment) = none := by
  cases hrun : Kernel.runPartialSteps (killedStep allowed) n initial
      (Kernel.sequencePrefix n increment) with
  | none => rfl
  | some endpoint =>
      exfalso
      apply hkilled
      rw [← survivesPrefix_killedStep_iff allowed n initial increment]
      simp [Kernel.SurvivesPrefix, Kernel.Survives, hrun]

omit [MeasurableSpace E] [MeasurableAdd₂ E] in
/-- The killed partial-step endpoint event is exactly path survival together
with membership of the final partial-sum position in the target set. -/
theorem endsInPrefix_killedStep_iff
    (allowed target : Set E) (n : ℕ) (initial : E)
    (increment : ℕ → E) :
    Kernel.EndsInPrefix (killedStep allowed) target n initial increment ↔
      StaysIn allowed n initial increment ∧
        initial + partialSum n increment ∈ target := by
  classical
  rw [Kernel.EndsInPrefix, Kernel.EndsIn]
  by_cases hsurvives : StaysIn allowed n initial increment
  · rw [runPartialSteps_killedStep_sequencePrefix_eq_some
      allowed n initial increment hsurvives]
    simp [hsurvives]
  · rw [runPartialSteps_killedStep_sequencePrefix_eq_none
      allowed n initial increment hsurvives]
    simp [hsurvives]

/-- Return-block mass is the IID event of staying in the outer set and ending
in the prescribed inner set. -/
theorem returnKernel_apply_univ_eq_staysIn_endsIn
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (returnSet : Set E) (hreturn : MeasurableSet returnSet)
    (length : ℕ) (x : returnSet) :
    returnKernel ν allowed hallowed returnSet hreturn length x univ =
      iidSequenceLaw ν {increment |
        StaysIn allowed length (x : E) increment ∧
          (x : E) + partialSum length increment ∈ returnSet} := by
  rw [returnKernel_apply_univ_eq_iidSequenceLaw]
  congr 1
  ext increment
  exact endsInPrefix_killedStep_iff
    allowed returnSet length (x : E) increment

/-- A uniform one-block return estimate multiplies over any number of complete
blocks. -/
theorem pow_le_remainingMass_returnKernel
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (returnSet : Set E) (hreturn : MeasurableSet returnSet)
    (length blocks : ℕ) (lowerBound : ENNReal)
    (hblock : ∀ x : returnSet, lowerBound ≤
      returnKernel ν allowed hallowed returnSet hreturn length x univ) :
    ∀ x : returnSet,
      lowerBound ^ blocks ≤ Kernel.remainingMass
        (returnKernel ν allowed hallowed returnSet hreturn length)
        blocks x := by
  intro x
  have hblock' : ∀ state : returnSet, lowerBound ≤
      Kernel.remainingMass
        (returnKernel ν allowed hallowed returnSet hreturn length) 1 state := by
    intro state
    simpa [Kernel.remainingMass] using hblock state
  simpa using Kernel.pow_le_remainingMass_mul
    (returnKernel ν allowed hallowed returnSet hreturn length)
    1 blocks x lowerBound hblock'

/-- Paths that return to `returnSet` after every block form a subset of the
ambient killed-walk survival event over the same total duration. -/
theorem remainingMass_returnKernel_le_killedIncrementKernel
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (returnSet : Set E) (hreturn : MeasurableSet returnSet)
    (length blocks : ℕ) (x : returnSet) :
    Kernel.remainingMass
        (returnKernel ν allowed hallowed returnSet hreturn length)
        blocks x ≤
      Kernel.remainingMass
        (killedIncrementKernel ν allowed hallowed)
        (blocks * length) (x : E) := by
  exact Kernel.remainingMass_returnKernel_le
    (killedIncrementKernel ν allowed hallowed)
    returnSet hreturn length blocks x

end ProbabilityTheory.RandomWalk
