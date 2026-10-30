/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Basic
public import Probability.Kernel.Step.Endpoint
public import Probability.Kernel.Survival.Return.Basic

/-!
# Killed block kernels returning to an interior set

## Public declarations

Let $\kappa_A$ be the additive kernel killed outside a measurable set $A$,
and let $R$ be any measurable return set. `returnKernel` runs $\ell$ steps
of $\kappa_A$ and retains endpoints in $R$. The public declarations are:

- `returnKernel`: the resulting transition kernel on the state space $R$.
- `returnKernel_apply_univ`:
  $\rho_\ell(x,R)=(\kappa_A^\ell)(x,R)$ for $x\in R$.
- `killedIncrementKernel_pow_apply_eq_staysIn_endsIn`: an $n$-step killed
  transition to a measurable target equals the IID probability of survival
  and endpoint membership.
- `returnKernel_apply_univ_eq_staysIn_endsIn`: the same identity for a return
  block starting in $R$ and ending in $R$.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk


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

omit [MeasurableSpace E] [MeasurableAdd₂ E] in
/-- On a surviving path, executing the killed additive partial step gives the
usual partial-sum endpoint. -/
private lemma runPartialSteps_killedStep_sequencePrefix_eq_some
    (allowed : Set E) (n : ℕ) (initial : E) (increment : ℕ → E)
    (hsurvives : StaysIn allowed n initial increment) :
    Kernel.runPartialSteps (killedStep allowed) n initial
        (Combinatorics.Sequence.blockCoordinates 0 n increment) =
      some (initial + AdditivePath.displacement n increment) := by
  induction n generalizing initial increment with
  | zero => simp [Kernel.runPartialSteps, AdditivePath.displacement]
  | succ n ih =>
      have h := (staysIn_succ_iff allowed n initial increment).1 hsurvives
      have htail : Fin.tail (Combinatorics.Sequence.blockCoordinates 0 (n + 1) increment) =
          Combinatorics.Sequence.blockCoordinates 0 n (fun k => increment (k + 1)) := by
        funext k
        rfl
      rw [Kernel.runPartialSteps, htail]
      change ((killedStep allowed initial (increment 0)).bind fun b =>
        Kernel.runPartialSteps (killedStep allowed) n b
          (Combinatorics.Sequence.blockCoordinates 0 n (fun k => increment (k + 1)))) = _
      rw [show killedStep allowed initial (increment 0) =
          some (initial + increment 0) by simp [killedStep, h.1]]
      simp only [Option.bind_some]
      rw [ih _ _ h.2, AdditivePath.displacement_succ_eq_head_add_tail]
      ac_rfl

omit [MeasurableSpace E] [MeasurableAdd₂ E] in
/-- On a killed path, execution returns `none`. -/
private lemma runPartialSteps_killedStep_sequencePrefix_eq_none
    (allowed : Set E) (n : ℕ) (initial : E) (increment : ℕ → E)
    (hkilled : ¬StaysIn allowed n initial increment) :
    Kernel.runPartialSteps (killedStep allowed) n initial
        (Combinatorics.Sequence.blockCoordinates 0 n increment) = none := by
  cases hrun : Kernel.runPartialSteps (killedStep allowed) n initial
      (Combinatorics.Sequence.blockCoordinates 0 n increment) with
  | none => rfl
  | some endpoint =>
      exfalso
      apply hkilled
      rw [← survivesPrefix_killedStep_iff allowed n initial increment]
      simp [Kernel.SurvivesPrefix, Kernel.Survives, hrun]

omit [MeasurableSpace E] [MeasurableAdd₂ E] in
/-- The killed partial-step endpoint event is exactly path survival together
with membership of the final partial-sum position in the target set. -/
private lemma endsInPrefix_killedStep_iff
    (allowed target : Set E) (n : ℕ) (initial : E)
    (increment : ℕ → E) :
    Kernel.EndsInPrefix (killedStep allowed) target n initial increment ↔
      StaysIn allowed n initial increment ∧
        initial + AdditivePath.displacement n increment ∈ target := by
  classical
  rw [Kernel.EndsInPrefix, Kernel.EndsIn]
  by_cases hsurvives : StaysIn allowed n initial increment
  · rw [runPartialSteps_killedStep_sequencePrefix_eq_some
      allowed n initial increment hsurvives]
    simp [hsurvives]
  · rw [runPartialSteps_killedStep_sequencePrefix_eq_none
      allowed n initial increment hsurvives]
    simp [hsurvives]

/-- A killed additive kernel reaches a measurable target after `length`
steps exactly on the IID event of staying in the allowed set and ending in
that target. -/
theorem killedIncrementKernel_pow_apply_eq_staysIn_endsIn
    [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (allowed : Set E) (hallowed : MeasurableSet allowed)
    (target : Set E) (htarget : MeasurableSet target)
    (length : ℕ) (initial : E) :
    (killedIncrementKernel ν allowed hallowed ^ length) initial target =
      iidSequenceLaw ν {increment |
        StaysIn allowed length initial increment ∧
          initial + AdditivePath.displacement length increment ∈ target} := by
  rw [killedIncrementKernel_eq_ofPartialStep ν allowed hallowed,
    Kernel.pow_apply_ofPartialStep_eq_iidSequenceLaw
      ν (killedStep allowed) (killedStep_measurable allowed hallowed)
      htarget length initial]
  congr 1
  ext increment
  exact endsInPrefix_killedStep_iff
    allowed target length initial increment

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
          (x : E) + AdditivePath.displacement length increment ∈ returnSet} := by
  rw [returnKernel_apply_univ,
    killedIncrementKernel_pow_apply_eq_staysIn_endsIn
      ν allowed hallowed returnSet hreturn length (x : E)]

end ProbabilityTheory.RandomWalk
