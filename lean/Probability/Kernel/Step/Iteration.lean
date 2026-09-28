import Probability.Kernel.Step.Path
import Probability.Sequence.IID
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Iteration of partial random steps

The remaining mass of an iterated partial-step kernel is identified with the
probability that a finite IID noise history survives.  No finiteness or
countability assumption is imposed on the noise space.
-/

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α ξ : Type*} [MeasurableSpace α] [MeasurableSpace ξ]

/-- Survival probability under a finite product of the noise law. -/
noncomputable def survivalProbability (ν : Measure ξ)
    (step : α → ξ → Option α) (n : ℕ) (a : α) : ENNReal :=
  (Measure.pi fun _ : Fin n => ν)
    {history | Survives step n a history}

/-- The head-tail form of the next survival event. -/
def nextSurvivalSet (step : α → ξ → Option α) (n : ℕ) (a : α) :
    Set (ξ × (Fin n → ξ)) :=
  {p | (step a p.1).elim False fun b => Survives step n b p.2}

omit [MeasurableSpace α] in
theorem survives_piFinSuccAbove_symm_iff
    (step : α → ξ → Option α) (n : ℕ) (a : α)
    (z : ξ) (tail : Fin n → ξ) :
    Survives step (n + 1) a
        ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ξ) 0).symm (z, tail)) ↔
      (step a z).elim False (fun b => Survives step n b tail) := by
  cases h : step a z <;>
    simp [h, Survives, runPartialSteps,
      MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem measurableSet_nextSurvivalSet
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step)) (n : ℕ) (a : α) :
    MeasurableSet (nextSurvivalSet step n a) := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ξ) 0
  rw [show nextSurvivalSet step n a =
      e.symm ⁻¹' {history | Survives step (n + 1) a history} by
    ext p
    exact (survives_piFinSuccAbove_symm_iff
      step n a p.1 p.2).symm]
  exact (measurableSet_survives step hstep (n + 1) a).preimage
    e.symm.measurable

/-- Splitting a finite IID noise history into its head and tail gives the
recursive survival probability. -/
theorem survivalProbability_succ
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step)) (n : ℕ) (a : α) :
    survivalProbability ν step (n + 1) a =
      ∫⁻ z, (step a z).elim 0 (survivalProbability ν step n) ∂ν := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ξ) 0
  let T := nextSurvivalSet step n a
  have hT : MeasurableSet T := measurableSet_nextSurvivalSet step hstep n a
  have he := MeasureTheory.measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ν) 0
  calc
    survivalProbability ν step (n + 1) a =
        (Measure.pi fun _ : Fin (n + 1) => ν) (e ⁻¹' T) := by
      unfold survivalProbability
      congr 1
      ext history
      exact survives_piFinSuccAbove_symm_iff step n a
        (e history).1 (e history).2
    _ = (ν.prod (Measure.pi fun _ : Fin n => ν)) T := by
      exact he.measure_preimage hT.nullMeasurableSet
    _ = ∫⁻ z, (Measure.pi fun _ : Fin n => ν)
          (Prod.mk z ⁻¹' T) ∂ν := Measure.prod_apply hT
    _ = ∫⁻ z, (step a z).elim 0
          (survivalProbability ν step n) ∂ν := by
      congr with z
      cases h : step a z with
      | none => simp [T, nextSurvivalSet, h]
      | some b =>
          simp [T, nextSurvivalSet, h, survivalProbability]

/-- A canonical IID sequence restricted to its first `n` coordinates has the
finite product law. -/
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

/-- Finite-product survival is the corresponding event under the canonical
IID noise sequence. -/
theorem iidSequenceLaw_apply_survivesPrefix
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step)) (n : ℕ) (a : α) :
    iidSequenceLaw ν {sequence | SurvivesPrefix step n a sequence} =
      survivalProbability ν step n a := by
  rw [show {sequence : ℕ → ξ | SurvivesPrefix step n a sequence} =
      sequencePrefix n ⁻¹' {history | Survives step n a history} by rfl]
  rw [← Measure.map_apply (sequencePrefix_measurable n)
      (measurableSet_survives step hstep n a),
    iidSequenceLaw_map_sequencePrefix]
  rfl

/-- The remaining mass after `n` partial-kernel steps is the finite-product
survival probability. -/
theorem pow_apply_univ_ofPartialStep
    [MeasurableSingletonClass α]
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step)) (n : ℕ) (a : α) :
    (ofPartialStep ν step hstep ^ n) a univ =
      survivalProbability ν step n a := by
  induction n generalizing a with
  | zero =>
      change Kernel.id a univ = _
      simp [survivalProbability, Survives, runPartialSteps]
  | succ n ih =>
      rw [show n + 1 = 1 + n by omega,
        Kernel.pow_add_apply_eq_lintegral _ 1 n a MeasurableSet.univ]
      simp only [pow_one]
      rw [lintegral_ofPartialStep ν step hstep a _]
      · simp_rw [ih]
        simpa [Nat.add_comm] using
          (survivalProbability_succ ν step hstep n a).symm
      · exact (Kernel.measurable_coe _ MeasurableSet.univ)

/-- Kernel survival mass equals the canonical IID prefix-survival event. -/
theorem pow_apply_univ_ofPartialStep_eq_iidSequenceLaw
    [MeasurableSingletonClass α]
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step)) (n : ℕ) (a : α) :
    (ofPartialStep ν step hstep ^ n) a univ =
      iidSequenceLaw ν {sequence | SurvivesPrefix step n a sequence} := by
  rw [pow_apply_univ_ofPartialStep ν step hstep n a,
    iidSequenceLaw_apply_survivesPrefix ν step hstep n a]

end ProbabilityTheory.Kernel
