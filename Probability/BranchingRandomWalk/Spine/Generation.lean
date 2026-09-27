import Probability.BranchingRandomWalk.Spine.EndpointManyToOne
import Combinatorics.BranchingWalk.Basic.DisplacementMap
import Probability.BranchingRandomWalk.Step.Map

/-!
# Actual generation observables

These are the two endpoint sums on an actual pre-sampled step field.  They are
kept separate from the recursively defined branching operators until the
product-law theorem identifies their expectations.  All sums range over
addresses and test survival explicitly, so extinction and empty generations
require no special convention.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Scalar displacement accumulated along an address through a potential on
raw edge marks. -/
def pathPotential {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : StepField ι X) (u : TreeNode ι) : ℝ :=
  displaceWith φ ω [] u

@[simp] theorem pathPotential_nil {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : StepField ι X) :
    pathPotential φ ω [] = 0 := rfl

/-- Survival of a fixed address is measurable on the full step field. -/
theorem measurableSet_surviveAlong
    {ι X : Type*} [MeasurableSpace X] (v p : TreeNode ι) :
    MeasurableSet {ω : StepField ι X | surviveAlong ω v p} := by
  induction p generalizing v with
  | nil =>
      simp [surviveAlong]
  | cons i p ih =>
      rw [show {ω : StepField ι X | surviveAlong ω v (i :: p)} =
          {ω | survive (ω v) i} ∩
            {ω | surviveAlong ω (v ++ [i]) p} by
        ext ω
        simp [surviveAlong]]
      exact ((measurable_pi_apply v) (survive_measurableSet i)).inter
        (ih (v := v ++ [i]))

/-- The scalar displacement of a fixed address is measurable. -/
theorem pathPotential_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (v p : TreeNode ι) :
    Measurable (fun ω : StepField ι X => displaceWith φ ω v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons i p ih =>
      change Measurable
        ((fun ω : StepField ι X => value' ((ω v).map φ) i) +
          fun ω => displaceWith φ ω (v ++ [i]) p)
      exact ((value'_measurable i).comp
          ((Step.map_measurable φ.measurable_toFun).comp (measurable_pi_apply v))).add
        (ih (v := v ++ [i]))

/-- Exponentially weighted contribution of one address at generation `n`. -/
noncomputable def weightedGenerationTerm
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (f : ℝ → ENNReal) (x : ℝ)
    (u : TreeNode ι) : StepField ι X → ENNReal :=
  {ω | u.length = n ∧ surviveAlong ω [] u}.indicator fun ω =>
    ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
      f (x + pathPotential φ ω u)

/-- Contribution of one surviving address without exponential weighting. -/
noncomputable def generationTerm
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (f : ℝ → ENNReal) (x : ℝ)
    (u : TreeNode ι) : StepField ι X → ENNReal :=
  {ω | u.length = n ∧ surviveAlong ω [] u}.indicator fun ω =>
    f (x + pathPotential φ ω u)

theorem weightedGenerationTerm_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {f : ℝ → ENNReal} (hf : Measurable f)
    (x : ℝ) (u : TreeNode ι) :
    Measurable (weightedGenerationTerm φ n f x u) := by
  have hp : Measurable (fun ω : StepField ι X => pathPotential φ ω u) :=
    pathPotential_measurable φ [] u
  apply (show Measurable (fun ω : StepField ι X =>
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
        f (x + pathPotential φ ω u)) by fun_prop).indicator
  by_cases hu : u.length = n
  · simpa [hu] using measurableSet_surviveAlong (X := X) [] u
  · simp [hu]

theorem generationTerm_measurable
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {f : ℝ → ENNReal} (hf : Measurable f)
    (x : ℝ) (u : TreeNode ι) :
    Measurable (generationTerm φ n f x u) := by
  have hp : Measurable (fun ω : StepField ι X => pathPotential φ ω u) :=
    pathPotential_measurable φ [] u
  apply (hf.comp (measurable_const.add hp)).indicator
  by_cases hu : u.length = n
  · simpa [hu] using measurableSet_surviveAlong (X := X) [] u
  · simp [hu]

/-- Actual exponentially weighted endpoint sum over generation `n`. -/
noncomputable def weightedGenerationEndpoint
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (f : ℝ → ENNReal) (x : ℝ)
    (ω : StepField ι X) : ENNReal :=
  ∑' u : TreeNode ι, weightedGenerationTerm φ n f x u ω

/-- Actual unweighted endpoint sum over generation `n`. -/
noncomputable def generationEndpoint
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (f : ℝ → ENNReal) (x : ℝ)
    (ω : StepField ι X) : ENNReal :=
  ∑' u : TreeNode ι, generationTerm φ n f x u ω

theorem weightedGenerationEndpoint_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {f : ℝ → ENNReal} (hf : Measurable f)
    (x : ℝ) :
    Measurable (weightedGenerationEndpoint (ι := ι) φ n f x) := by
  exact Measurable.tsum fun u => weightedGenerationTerm_measurable φ n hf x u

theorem generationEndpoint_measurable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {f : ℝ → ENNReal} (hf : Measurable f)
    (x : ℝ) :
    Measurable (generationEndpoint (ι := ι) φ n f x) := by
  exact Measurable.tsum fun u => generationTerm_measurable φ n hf x u

@[simp] theorem weightedGenerationEndpoint_zero
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (f : ℝ → ENNReal) (x : ℝ) (ω : StepField ι X) :
    weightedGenerationEndpoint φ 0 f x ω = f x := by
  classical
  rw [weightedGenerationEndpoint, tsum_eq_single ([] : TreeNode ι)]
  · rw [weightedGenerationTerm, Set.indicator_of_mem]
    · simp
    · exact ⟨rfl, surviveAlong_nil ω []⟩
  · intro u hu
    simp [weightedGenerationTerm, Set.indicator, hu,
      List.length_eq_zero_iff]

@[simp] theorem generationEndpoint_zero
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (f : ℝ → ENNReal) (x : ℝ) (ω : StepField ι X) :
    generationEndpoint φ 0 f x ω = f x := by
  classical
  rw [generationEndpoint, tsum_eq_single ([] : TreeNode ι)]
  · rw [generationTerm, Set.indicator_of_mem]
    · simp
    · exact ⟨rfl, surviveAlong_nil ω []⟩
  · intro u hu
    simp [generationTerm, Set.indicator, hu,
      List.length_eq_zero_iff]

end ProbabilityTheory.BranchingRandomWalk.Spine
