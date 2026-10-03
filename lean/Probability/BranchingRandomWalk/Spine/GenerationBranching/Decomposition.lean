module

public import Probability.BranchingRandomWalk.Spine.Generation
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.DomainFlow
public import Combinatorics.BranchingWalk.Basic.Map

/-!
# First-generation branching decomposition

The root step and each child descendant field have their product law under the
pre-sampled i.i.d. step field. The generation-address equivalence records the
deterministic decomposition of generation `n + 1` into a first child slot and
a generation-`n` address inside that child's subtree.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Generation `n + 1` addresses are a first slot followed by a generation
`n` address. No distinguished or default slot is chosen. -/
def generationConsEquiv (ι : Type*) (n : ℕ) :
    ι × {v : TreeNode ι // v.length = n} ≃
      {u : TreeNode ι // u.length = n + 1} where
  toFun p := ⟨p.1 :: p.2.1, by simp [p.2.2]⟩
  invFun u := by
    have hpos : 0 < u.1.length := by omega
    have hne : u.1 ≠ [] := List.ne_nil_of_length_pos hpos
    exact (u.1.head hne, ⟨u.1.tail, by simp [List.length_tail, u.2]⟩)
  left_inv p := by
    rcases p with ⟨i, v⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp
  right_inv u := by
    apply Subtype.ext
    exact List.cons_head_tail
      (List.ne_nil_of_length_pos (by omega : 0 < u.1.length))

/-- The root reproduction step and the complete descendant step field below
any one child have the product of their marginal laws. -/
theorem root_subtreeStepField_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (i : ι) :
    (stepFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι), subtreeStepField [i] ω)) =
      μ.prod (stepFieldLaw μ) := by
  have hrootPast : Measurable[generationFiltration
      (M := Combinatorics.Branching.Step ι X) 1]
      (fun ω : Combinatorics.Branching.StepField ι X =>
        ω ([] : TreeNode ι)) :=
    mark_measurable_of_depth_lt [] 1 (by simp)
  have hind : IndepFun
      (fun ω : Combinatorics.Branching.StepField ι X =>
        ω ([] : TreeNode ι))
      (subtreeStepField (X := X) [i]) (stepFieldLaw μ) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (generation_subtreeStepField_independent μ [i]) hrootPast.comap_le
  rw [hind.map_prod_eq_prod_map_map
      (measurable_pi_apply ([] : TreeNode ι)).aemeasurable
      (subtreeStepField_measurable [i]).aemeasurable,
    stepFieldLaw_coordinate μ ([] : TreeNode ι),
    subtreeStepField_law μ [i]]

theorem pathPotential_cons
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : Combinatorics.Branching.StepField ι X)
    (i : ι) (v : TreeNode ι) :
    pathPotential φ ω (i :: v) =
      (ω []).potentialValue' φ i +
        pathPotential φ (subtreeStepField [i] ω) v := by
  rw [show i :: v = [i] ++ v from rfl]
  unfold pathPotential displaceWith
  rw [subtreeStepField_position_decomposition (ω.map φ) [i] v]
  have hmap : subtreeStepField [i] (ω.map φ) =
      Combinatorics.Branching.StepField.map φ
        (subtreeStepField [i] ω) := rfl
  rw [hmap]
  simp [displace, Combinatorics.Branching.StepField.map_apply,
    Step.potentialValue', Step.potentialAt?, value']

end ProbabilityTheory.BranchingRandomWalk.Spine
