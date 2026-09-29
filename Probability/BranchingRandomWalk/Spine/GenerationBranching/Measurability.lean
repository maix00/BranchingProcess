module

public import Probability.BranchingRandomWalk.Spine.Generation
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.DomainFlow

/-!
# Measurability of generation branching observables

Joint endpoint observables and the recursive branching operators are separated
from the pathwise generation decomposition.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

theorem weightedGenerationEndpoint_joint_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      weightedGenerationEndpoint φ n f p.1 p.2) := by
  apply Measurable.tsum
  intro u
  have hp : Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      pathPotential φ p.2 u) :=
    (pathPotential_measurable φ [] u).comp measurable_snd
  have hevent : MeasurableSet
      {p : ℝ × Combinatorics.Branching.StepField ι X |
        u.length = n ∧ surviveAlong p.2 [] u} := by
    by_cases hu : u.length = n
    · convert (measurableSet_surviveAlong (X := X) [] u).preimage
          (measurable_snd : Measurable
            (Prod.snd : ℝ × Combinatorics.Branching.StepField ι X → _)) using 1
      simp [hu]
    · simp [hu]
  apply (show Measurable
      (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
        ENNReal.ofReal (Real.exp (-pathPotential φ p.2 u)) *
          f (p.1 + pathPotential φ p.2 u)) by fun_prop).indicator hevent

theorem generationEndpoint_joint_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      generationEndpoint φ n f p.1 p.2) := by
  apply Measurable.tsum
  intro u
  have hp : Measurable (fun p : ℝ × Combinatorics.Branching.StepField ι X =>
      pathPotential φ p.2 u) :=
    (pathPotential_measurable φ [] u).comp measurable_snd
  have hevent : MeasurableSet
      {p : ℝ × Combinatorics.Branching.StepField ι X |
        u.length = n ∧ surviveAlong p.2 [] u} := by
    by_cases hu : u.length = n
    · convert (measurableSet_surviveAlong (X := X) [] u).preimage
          (measurable_snd : Measurable
            (Prod.snd : ℝ × Combinatorics.Branching.StepField ι X → _)) using 1
      simp [hu]
    · simp [hu]
  exact (hf.comp (measurable_fst.add hp)).indicator hevent

theorem measurable_weightedBranchingEndpointOperator
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [SFinite μ] {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (weightedBranchingEndpointOperator φ μ f) := by
  apply Measurable.lintegral_prod_right
  apply Measurable.tsum
  intro i
  exact ((realizedPotentialWeight_measurable φ (-1) i).comp measurable_snd).mul
    (hf.comp (measurable_fst.add
      ((Step.potentialValue'_measurable φ i).comp measurable_snd)))

theorem measurable_branchingEndpointOperator
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [SFinite μ] {f : ℝ → ENNReal} (hf : Measurable f) :
    Measurable (branchingEndpointOperator φ μ f) := by
  apply Measurable.lintegral_prod_right
  apply Measurable.tsum
  intro i
  unfold survivingPotentialTest
  exact (hf.comp (measurable_fst.add
    ((Step.potentialValue'_measurable φ i).comp measurable_snd))).ite
      ((survive_measurableSet i).preimage measurable_snd) measurable_const

theorem measurable_weightedBranchingEndpointIterate
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [SFinite μ] {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable (weightedBranchingEndpointIterate φ μ n f)
  | 0 => hf
  | n + 1 => measurable_weightedBranchingEndpointOperator φ μ
      (measurable_weightedBranchingEndpointIterate φ μ hf n)

theorem measurable_branchingEndpointIterate
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [SFinite μ] {f : ℝ → ENNReal} (hf : Measurable f) :
    ∀ n, Measurable (branchingEndpointIterate φ μ n f)
  | 0 => hf
  | n + 1 => measurable_branchingEndpointOperator φ μ
      (measurable_branchingEndpointIterate φ μ hf n)

end ProbabilityTheory.BranchingRandomWalk.Spine
