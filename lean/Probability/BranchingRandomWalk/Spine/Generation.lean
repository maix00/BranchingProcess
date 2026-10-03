module

public import Probability.BranchingRandomWalk.Spine.EndpointManyToOne
public import Combinatorics.BranchingWalk.Basic.DisplacementMap
public import Combinatorics.BranchingWalk.Basic.Map
public import Probability.BranchingRandomWalk.Step.Law
public import Combinatorics.BranchingWalk.StepField

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

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Child slots are exactly the addresses of generation one. -/
def singletonNodeEquiv (ι : Type*) :
    ι ≃ {u : TreeNode ι // u.length = 1} where
  toFun i := ⟨[i], by simp⟩
  invFun u := u.1[0]'(by omega)
  left_inv i := by simp
  right_inv u := by
    apply Subtype.ext
    obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp u.2
    change [u.1[0]'(by omega)] = u.1
    simp [hi]

/-- Scalar displacement accumulated along an address through a potential on
raw edge marks. -/
def pathPotential {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : StepField ι X) (u : TreeNode ι) : ℝ :=
  displaceWith φ ω [] u

@[simp] theorem pathPotential_nil {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : StepField ι X) :
    pathPotential φ ω [] = 0 := rfl

@[simp] theorem pathPotential_singleton {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : StepField ι X) (i : ι) :
    pathPotential φ ω [i] = (ω []).potentialValue' φ i := by
  simp [pathPotential, displaceWith, displace, StepField.map,
    Step.potentialValue', Step.potentialAt?, value']

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

/-- The actual weighted first generation is the slot sum appearing in the
one-step weighted branching operator. -/
theorem weightedGenerationEndpoint_one
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (f : ℝ → ENNReal) (x : ℝ) (ω : StepField ι X) :
    weightedGenerationEndpoint φ 1 f x ω =
      ∑' i : ι, realizedPotentialWeight φ (-1) (ω []) i *
        f (x + (ω []).potentialValue' φ i) := by
  classical
  rw [weightedGenerationEndpoint]
  let s : Set (TreeNode ι) := {u | u.length = 1}
  calc
    (∑' u : TreeNode ι, weightedGenerationTerm φ 1 f x u ω) =
        ∑' u : TreeNode ι,
          s.indicator (fun u => weightedGenerationTerm φ 1 f x u ω) u := by
      apply tsum_congr
      intro u
      by_cases hu : u.length = 1
      · simp [s, hu]
      · simp [s, hu, weightedGenerationTerm, Set.indicator]
    _ = ∑' u : s, weightedGenerationTerm φ 1 f x u.1 ω := by
      exact (tsum_subtype s
        (fun u => weightedGenerationTerm φ 1 f x u ω)).symm
    _ = ∑' i : ι,
          weightedGenerationTerm φ 1 f x [i] ω := by
      exact (Equiv.tsum_eq (singletonNodeEquiv ι)
        (fun u : s => weightedGenerationTerm φ 1 f x u.1 ω)).symm
    _ = ∑' i : ι, realizedPotentialWeight φ (-1) (ω []) i *
          f (x + (ω []).potentialValue' φ i) := by
      apply tsum_congr
      intro i
      by_cases hi : survive (ω []) i
      · simp [weightedGenerationTerm, Set.indicator, hi,
          surviveAlong, realizedPotentialWeight]
      · simp [weightedGenerationTerm, Set.indicator, hi,
          surviveAlong, realizedPotentialWeight]

/-- The actual unweighted first generation is the slot sum appearing in the
one-step unweighted branching operator. -/
theorem generationEndpoint_one
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (f : ℝ → ENNReal) (x : ℝ) (ω : StepField ι X) :
    generationEndpoint φ 1 f x ω =
      ∑' i : ι, survivingPotentialTest φ (fun y => f (x + y)) (ω []) i := by
  classical
  rw [generationEndpoint]
  let s : Set (TreeNode ι) := {u | u.length = 1}
  calc
    (∑' u : TreeNode ι, generationTerm φ 1 f x u ω) =
        ∑' u : TreeNode ι,
          s.indicator (fun u => generationTerm φ 1 f x u ω) u := by
      apply tsum_congr
      intro u
      by_cases hu : u.length = 1
      · simp [s, hu]
      · simp [s, hu, generationTerm, Set.indicator]
    _ = ∑' u : s, generationTerm φ 1 f x u.1 ω := by
      exact (tsum_subtype s
        (fun u => generationTerm φ 1 f x u ω)).symm
    _ = ∑' i : ι, generationTerm φ 1 f x [i] ω := by
      exact (Equiv.tsum_eq (singletonNodeEquiv ι)
        (fun u : s => generationTerm φ 1 f x u.1 ω)).symm
    _ = ∑' i : ι,
          survivingPotentialTest φ (fun y => f (x + y)) (ω []) i := by
      apply tsum_congr
      intro i
      by_cases hi : survive (ω []) i
      · simp [generationTerm, Set.indicator, hi,
          surviveAlong, survivingPotentialTest]
      · simp [generationTerm, Set.indicator, hi,
          surviveAlong, survivingPotentialTest]

/-- Integrating the actual weighted first generation under the i.i.d. field
law gives the one-step weighted branching operator. -/
theorem lintegral_weightedGenerationEndpoint_one
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ]
    {f : ℝ → ENNReal} (hf : Measurable f) (x : ℝ) :
    (∫⁻ ω, weightedGenerationEndpoint φ 1 f x ω ∂stepFieldLaw μ) =
      weightedBranchingEndpointOperator φ μ f x := by
  let g : Combinatorics.Branching.Step ι X → ENNReal := fun ξ =>
    ∑' i : ι, realizedPotentialWeight φ (-1) ξ i *
      f (x + ξ.potentialValue' φ i)
  have hg : Measurable g := by
    apply Measurable.tsum
    intro i
    exact (realizedPotentialWeight_measurable φ (-1) i).mul
      (hf.comp (measurable_const.add (Step.potentialValue'_measurable φ i)))
  simp_rw [weightedGenerationEndpoint_one]
  change (∫⁻ ω, g (ω []) ∂stepFieldLaw μ) = _
  rw [← lintegral_map hg (measurable_pi_apply ([] : TreeNode ι)),
    stepFieldLaw_coordinate μ ([] : TreeNode ι)]
  rfl

/-- Integrating the actual unweighted first generation under the i.i.d. field
law gives the one-step unweighted branching operator. -/
theorem lintegral_generationEndpoint_one
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ]
    {f : ℝ → ENNReal} (hf : Measurable f) (x : ℝ) :
    (∫⁻ ω, generationEndpoint φ 1 f x ω ∂stepFieldLaw μ) =
      branchingEndpointOperator φ μ f x := by
  let g : Combinatorics.Branching.Step ι X → ENNReal := fun ξ =>
    ∑' i : ι, survivingPotentialTest φ (fun y => f (x + y)) ξ i
  have hg : Measurable g := by
    apply Measurable.tsum
    intro i
    unfold survivingPotentialTest
    exact (hf.comp
      (measurable_const.add (Step.potentialValue'_measurable φ i))).ite
        (survive_measurableSet i) measurable_const
  simp_rw [generationEndpoint_one]
  change (∫⁻ ω, g (ω []) ∂stepFieldLaw μ) = _
  rw [← lintegral_map hg (measurable_pi_apply ([] : TreeNode ι)),
    stepFieldLaw_coordinate μ ([] : TreeNode ι)]
  rfl

end ProbabilityTheory.BranchingRandomWalk.Spine
