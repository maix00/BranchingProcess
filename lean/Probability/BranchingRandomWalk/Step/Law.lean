import Combinatorics.BranchingWalk.Basic.Definitions
import Combinatorics.BranchingWalk.Step.Measurability
import Mathlib.Probability.Independence.InfinitePi

/-!
# Product laws on branching step fields

`stepFieldLaw μ` is the product law of an i.i.d. family of branching
steps, one at every address; `RootIndexed.stepFieldLaw` is the product
of one such field over every initial root. The file also records the
coordinate marginals and the independence statements that the restart and
multi-root arguments consume.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



noncomputable def stepFieldLaw {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) :
    Measure (StepField α X) :=
  Measure.infinitePi (fun _ : TreeNode α => μ)

instance stepFieldLaw.isProbabilityMeasure
    {α : Type*} {X : Type*} [MeasurableSpace X] (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (stepFieldLaw μ) := by
  unfold stepFieldLaw
  infer_instance

theorem stepFieldLaw_coordinate
    {α : Type*} {X : Type*} [MeasurableSpace X] (μ : Measure (Step α X))
    [IsProbabilityMeasure μ] (u : TreeNode α) :
    (stepFieldLaw μ).map (fun ω => ω u) = μ := by
  unfold stepFieldLaw
  exact Measure.infinitePi_map_eval (fun _ : TreeNode α => μ) u

theorem stepFieldLaw_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    iIndepFun (fun u (ω : StepField α X) => ω u)
      (stepFieldLaw μ) := by
  unfold stepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : TreeNode α => μ)
    (X := fun _ : TreeNode α => id)
    (fun _ => measurable_id))

theorem stepFieldLaw_injective_coordinates_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (f : ι → TreeNode α) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : StepField α X) => ω (f i))
      (stepFieldLaw μ) := by
  exact (stepFieldLaw_independent μ).precomp hf

theorem stepFieldLaw_injective_coordinates_comp_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (f : ι → TreeNode α) (hf : Function.Injective f)
    (g : ∀ i, Step α X → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (ω : StepField α X) =>
      g i (ω (f i))) (stepFieldLaw μ) := by
  exact (stepFieldLaw_injective_coordinates_independent μ f hf).comp
    (fun i => g i) hg

/-- The first displacement of injectively reindexed addresses is independent — the law of the atoms of the
step at each address, in the form the restart and multi-root arguments consume. -/
theorem stepFieldLaw_injective_displacements_independent {α X : Type*} [MeasurableSpace X]
    [Zero α] [Zero X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (f : ι → TreeNode α) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : StepField α X) => value' (ω (f i)) 0)
      (stepFieldLaw μ) := by
  apply stepFieldLaw_injective_coordinates_comp_independent μ f hf
    (fun _ ξ => value' ξ 0)
  intro i
  exact value'_measurable 0

/-- The joint law of the first displacements of finitely many injectively reindexed addresses: independent
copies of the displaced child law. -/
theorem stepFieldLaw_injective_displacements_law {α X : Type*} [MeasurableSpace X]
    [Zero α] [Zero X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {k : ℕ} (f : Fin k → TreeNode α) (hf : Function.Injective f) :
    (stepFieldLaw μ).map
        (fun ω i => value' (ω (f i)) 0) =
      Measure.infinitePi
        (fun _ : Fin k => μ.map (fun ξ => value' ξ 0)) := by
  have h := (stepFieldLaw_injective_displacements_independent μ f hf)
  have hmeas : ∀ i : Fin k, Measurable
      (fun ω : StepField α X => value' (ω (f i)) 0) := by
    intro i
    exact (value'_measurable 0).comp (measurable_pi_apply (f i))
  rw [h.map_fun_eq_infinitePi_map hmeas]
  apply congrArg Measure.infinitePi
  funext i
  calc
    Measure.map (fun ω : StepField α X => value' (ω (f i)) 0) (stepFieldLaw μ) =
      ((stepFieldLaw μ).map (fun ω => ω (f i))).map (fun ξ => value' ξ 0) := by
        rw [Measure.map_map]
        · rfl
        · exact value'_measurable 0
        · exact measurable_pi_apply (f i)
    _ = μ.map (fun ξ => value' ξ 0) := by
      rw [stepFieldLaw_coordinate]

end ProbabilityTheory.BranchingRandomWalk
