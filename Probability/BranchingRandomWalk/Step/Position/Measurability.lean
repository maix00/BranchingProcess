import MeasureTheory.BranchingStep.Position.Accumulate
import MeasureTheory.BranchingStep.Position.Increment
import MeasureTheory.BranchingStep.Tree.Realization
import Probability.BranchingRandomWalk.Tree.Filtration

/-!
# Measurability of realized nodes and accumulated marks

A realized node is observable at its own generation, and the accumulated mark
of a fixed or generation-measurably selected node is adapted. The step-field
object and the accumulated marks themselves live under `Branching/`; this file
only contains the measurability results. Nothing here is specific to `ℝ`: the
accumulated mark only needs an additive commutative monoid whose addition is
measurable, and the mark type is an arbitrary parameter `X`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingStep MeasureTheory



/-- Realization along a remaining path is observable as soon as the whole path
has been revealed. The induction is on the path; the address is carried along
so each step only needs the mark at one fixed address. -/
theorem presentAlong_measurableSet {X : Type*} [MeasurableSpace X]
    (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    MeasurableSet[generationFiltration (M := Step ℕ X) n]
      {step : StepField ℕ X | presentAlong step v p} := by
  induction p generalizing v with
  | nil =>
      have hset : {step : StepField ℕ X |
          presentAlong step v []} = Set.univ := by
        ext step
        simp
      rw [hset]
      exact MeasurableSet.univ
  | cons i p ih =>
      have hlen : (v ++ [i]).length = v.length + 1 := by simp
      have hlen' : (i :: p).length = p.length + 1 := by simp
      have hset : {step : StepField ℕ X |
          presentAlong step v (i :: p)} =
          {step : StepField ℕ X | present (step v) i} ∩
            {step : StepField ℕ X |
              presentAlong step (v ++ [i]) p} := by
        ext step
        simp [presentAlong]
      rw [hset]
      refine MeasurableSet.inter ?_ ?_
      · exact (mark_measurable_of_depth_lt (M := Step ℕ X) v n
          (by omega))
          (present_measurableSet (X := X) i)
      · exact ih (v := v ++ [i]) (by omega)

theorem realizedNode_measurableSet {X : Type*} [MeasurableSpace X]
    (u : 𝕍) :
    MeasurableSet[generationFiltration (M := Step ℕ X) u.length]
      {step : StepField ℕ X | realizedNode step u} := by
  change MeasurableSet[generationFiltration (M := Step ℕ X) u.length]
    {step : StepField ℕ X | presentAlong step [] u}
  exact presentAlong_measurableSet (X := X) [] u u.length (by simp)

/-- The accumulated mark is observable at the generation reached by the path;
again the induction carries the current address. Both the mark type and the
monoid are parameters, so this is not a real-valued statement. -/
theorem accumulate_measurable
    {X : Type*} [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (fun step : StepField ℕ X =>
        accumulate step v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons i p ih =>
      have hlen : (v ++ [i]).length = v.length + 1 := by simp
      have hlen' : (i :: p).length = p.length + 1 := by simp
      have hstep : Measurable[generationFiltration (M := Step ℕ X) n]
          (fun step : StepField ℕ X =>
            MeasureTheory.BranchingStep.value (step v) i) :=
        (value_measurable (X := X) i).comp
          (mark_measurable_of_depth_lt (M := Step ℕ X) v n
            (by omega))
      have hrec : Measurable[generationFiltration (M := Step ℕ X) n]
          (fun step : StepField ℕ X =>
            accumulate step (v ++ [i]) p) :=
        ih (v := v ++ [i]) (by omega)
      change Measurable[generationFiltration (M := Step ℕ X) n]
        ((fun step : StepField ℕ X => MeasureTheory.BranchingStep.value (step v) i) +
          fun step => accumulate step (v ++ [i]) p)
      exact hstep.add hrec

theorem accumulateRoot_measurable
    {X : Type*} [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (u : 𝕍) :
    Measurable[generationFiltration (M := Step ℕ X) u.length]
      (fun step : StepField ℕ X =>
        accumulateRoot step u) := by
  change Measurable[generationFiltration (M := Step ℕ X) u.length]
    (fun step : StepField ℕ X =>
      accumulate step [] u)
  exact accumulate_measurable [] u u.length (by simp)

/-- Position of a fixed address once the observed generation matches its
depth, and zero before that. -/
def stepPositionAtGeneration {X : Type*} [AddCommMonoid X]
    (n : ℕ) (u : 𝕍) (step : StepField ℕ X) : X :=
  if u.length = n then accumulateRoot step u else 0

theorem stepPositionAtGeneration_measurable
    {X : Type*} [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (n : ℕ) (u : 𝕍) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (stepPositionAtGeneration n u) := by
  change Measurable[generationFiltration (M := Step ℕ X) n]
    (fun step : StepField ℕ X =>
      if u.length = n then accumulateRoot step u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using accumulateRoot_measurable (X := X) u
  · simp only [hu, ite_false]
    exact measurable_const

set_option linter.style.haveILetI false in
theorem selectedStepPosition_measurable
    {X : Type*} [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (n : ℕ)
    (chosen : StepField ℕ X → 𝕍)
    (hchosen : Measurable[
      generationFiltration (M := Step ℕ X) n] chosen)
    (hdepth : ∀ step, (chosen step).length = n) :
    Measurable[generationFiltration (M := Step ℕ X) n]
      (fun step => accumulateRoot step (chosen step)) := by
  letI : MeasurableSpace (StepField ℕ X) :=
    generationFiltration (M := Step ℕ X) n
  have hjoint : Measurable
      (fun p : 𝕍 × StepField ℕ X =>
        stepPositionAtGeneration n p.1 p.2) :=
    measurable_from_prod_countable_right
      (stepPositionAtGeneration_measurable (X := X) n)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext step
  simp [stepPositionAtGeneration, hdepth step]

end ProbabilityTheory.BranchingRandomWalk
