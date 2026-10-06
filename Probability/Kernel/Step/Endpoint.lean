/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Step.Iteration

/-!
# Endpoint events for iterated partial steps

This extends the survival-only iteration API with evaluation on an arbitrary
measurable endpoint set.  No finiteness or countability assumption is placed
on either the state or noise space.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α ξ : Type*} [MeasurableSpace α] [MeasurableSpace ξ]

/-- Probability that a finite partial-step history survives and ends in a
specified target. -/
noncomputable def endpointProbability (ν : Measure ξ)
    (step : α → ξ → Option α) (target : Set α) (n : ℕ) (a : α) : ENNReal :=
  (Measure.pi fun _ : Fin n => ν)
    {history | EndsIn step target n a history}

omit [MeasurableSpace α] in
theorem endsIn_piFinSuccAbove_symm_iff
    (step : α → ξ → Option α) (target : Set α) (n : ℕ) (a : α)
    (z : ξ) (tail : Fin n → ξ) :
    EndsIn step target (n + 1) a
        ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ξ) 0).symm (z, tail)) ↔
      (step a z).elim False (fun b => EndsIn step target n b tail) := by
  simp only [EndsIn, runPartialSteps,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  cases h : step a z <;> simp [h]

/-- Splitting off the first noise coordinate gives the endpoint-probability
recursion. -/
theorem endpointProbability_succ
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step))
    {target : Set α} (htarget : MeasurableSet target)
    (n : ℕ) (a : α) :
    endpointProbability ν step target (n + 1) a =
      ∫⁻ z, (step a z).elim 0
        (endpointProbability ν step target n) ∂ν := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ξ) 0
  let T : Set (ξ × (Fin n → ξ)) :=
    {p | (step a p.1).elim False fun b =>
      EndsIn step target n b p.2}
  have hT : MeasurableSet T := by
    rw [show T = e.symm ⁻¹' {history |
        EndsIn step target (n + 1) a history} by
      ext p
      exact (endsIn_piFinSuccAbove_symm_iff
        step target n a p.1 p.2).symm]
    exact (measurableSet_endsIn step hstep htarget (n + 1) a).preimage
      e.symm.measurable
  have he := MeasureTheory.measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ν) 0
  calc
    endpointProbability ν step target (n + 1) a =
        (Measure.pi fun _ : Fin (n + 1) => ν) (e ⁻¹' T) := by
      unfold endpointProbability
      congr 1
      ext history
      exact endsIn_piFinSuccAbove_symm_iff step target n a
        (e history).1 (e history).2
    _ = (ν.prod (Measure.pi fun _ : Fin n => ν)) T := by
      exact he.measure_preimage hT.nullMeasurableSet
    _ = ∫⁻ z, (Measure.pi fun _ : Fin n => ν)
          (Prod.mk z ⁻¹' T) ∂ν := Measure.prod_apply hT
    _ = ∫⁻ z, (step a z).elim 0
          (endpointProbability ν step target n) ∂ν := by
      congr with z
      cases h : step a z with
      | none => simp [T, h]
      | some b => simp [T, h, endpointProbability]

/-- Finite-product endpoint probability is the corresponding canonical IID
prefix event. -/
theorem iidSequenceLaw_apply_endsInPrefix
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step))
    {target : Set α} (htarget : MeasurableSet target)
    (n : ℕ) (a : α) :
    iidSequenceLaw ν {sequence |
        EndsInPrefix step target n a sequence} =
      endpointProbability ν step target n a := by
  rw [show {sequence : ℕ → ξ |
      EndsInPrefix step target n a sequence} =
      Combinatorics.Sequence.blockCoordinates 0 n ⁻¹' {history |
        EndsIn step target n a history} by rfl]
  rw [← Measure.map_apply (measurable_blockCoordinates 0 n)
      (measurableSet_endsIn step hstep htarget n a),
    iidSequenceLaw_map_blockCoordinates_zero]
  rfl

/-- An iterated partial-step kernel evaluated on a measurable target equals
the finite-product probability of surviving and ending in that target. -/
theorem pow_apply_ofPartialStep
    [MeasurableSingletonClass α]
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step))
    {target : Set α} (htarget : MeasurableSet target)
    (n : ℕ) (a : α) :
    (ofPartialStep ν step hstep ^ n) a target =
      endpointProbability ν step target n a := by
  induction n generalizing a with
  | zero =>
      change Kernel.id a target = _
      rw [Kernel.id_apply]
      by_cases ha : a ∈ target <;>
        simp [endpointProbability, EndsIn, runPartialSteps, ha]
  | succ n ih =>
      rw [show n + 1 = 1 + n by omega,
        Kernel.pow_add_apply_eq_lintegral _ 1 n a htarget]
      simp only [pow_one]
      rw [lintegral_ofPartialStep ν step hstep a _]
      · simp_rw [ih]
        simpa [Nat.add_comm] using
          (endpointProbability_succ ν step hstep htarget n a).symm
      · exact (Kernel.measurable_coe _ htarget)

/-- Target mass of an iterated partial-step kernel equals the canonical IID
prefix event of surviving and ending in that target. -/
theorem pow_apply_ofPartialStep_eq_iidSequenceLaw
    [MeasurableSingletonClass α]
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step))
    {target : Set α} (htarget : MeasurableSet target)
    (n : ℕ) (a : α) :
    (ofPartialStep ν step hstep ^ n) a target =
      iidSequenceLaw ν {sequence |
        EndsInPrefix step target n a sequence} := by
  rw [pow_apply_ofPartialStep ν step hstep htarget n a,
    iidSequenceLaw_apply_endsInPrefix ν step hstep htarget n a]

end ProbabilityTheory.Kernel

end
