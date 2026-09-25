import Combinatorics.BranchingStep.Field
import Mathlib.Probability.Independence.InfinitePi

/-!
# Product laws on branching step fields

`branchingStepFieldLaw μ` is the product law of an i.i.d. family of branching
steps, one at every address; `rootIndexedBranchingStepFieldLaw` is the product
of one such field over every initial root. The file also records the
coordinate marginals and the independence statements that the restart and
multi-root arguments consume.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



noncomputable def branchingStepFieldLaw {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep α X)) :
    Measure (BranchingStepField α X) :=
  Measure.infinitePi (fun _ : TreeNode α => μ)

instance branchingStepFieldLaw.isProbabilityMeasure
    {α : Type*} {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep α X))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (branchingStepFieldLaw μ) := by
  unfold branchingStepFieldLaw
  infer_instance

theorem branchingStepFieldLaw_coordinate
    {α : Type*} {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep α X))
    [IsProbabilityMeasure μ] (u : TreeNode α) :
    (branchingStepFieldLaw μ).map (fun ω => ω u) = μ := by
  unfold branchingStepFieldLaw
  exact Measure.infinitePi_map_eval (fun _ : TreeNode α => μ) u

theorem branchingStepFieldLaw_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep α X)) [IsProbabilityMeasure μ] :
    iIndepFun (fun u (ω : BranchingStepField α X) => ω u)
      (branchingStepFieldLaw μ) := by
  unfold branchingStepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : TreeNode α => μ)
    (X := fun _ : TreeNode α => id)
    (fun _ => measurable_id))

theorem branchingStepFieldLaw_injective_coordinates_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (f : ι → TreeNode α) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : BranchingStepField α X) => ω (f i))
      (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_independent μ).precomp hf

theorem branchingStepFieldLaw_injective_coordinates_comp_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (f : ι → TreeNode α) (hf : Function.Injective f)
    (g : ∀ i, BranchingStep α X → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (ω : BranchingStepField α X) =>
      g i (ω (f i))) (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_injective_coordinates_independent μ f hf).comp
    (fun i => g i) hg

end ProbabilityTheory.BranchingRandomWalk
