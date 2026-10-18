/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Step.Law.Field
public import Combinatorics.BranchingWalk.Basic.Position.Displace
public import Probability.BranchingRandomWalk.Tree.Filtration

/-!
# Measurable subtree fields and their law

`ProbabilityTheory.BranchingRandomWalk.subtreeStepField u ω` is the subtree
field `v ↦ ω (u ++ v)`. The public declarations establish its measurability,
preservation of the IID step-field law, and the displacement decomposition
$\operatorname{displace}(\omega,[],u{++}v)=
  \operatorname{displace}(\omega,[],u)+
  \operatorname{displace}(\operatorname{subtreeStepField}(u,\omega),[],v)$.

- `ProbabilityTheory.BranchingRandomWalk.subtreeStepField` defines the
  subtree restriction.
- `ProbabilityTheory.BranchingRandomWalk.subtreeStepField_measurable` proves
  it is measurable.
- `ProbabilityTheory.BranchingRandomWalk.subtreeStepField_law` proves
  `(stepFieldLaw μ).map (subtreeStepField u) = stepFieldLaw μ` for a
  probability step law.
- `ProbabilityTheory.BranchingRandomWalk.subtreeStepField_position_decomposition`
  gives the displacement identity above.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



def subtreeStepField {α X : Type*} (u : TreeNode α)
    (ω : TreeNode α → Step α X) :
    TreeNode α → Step α X :=
  fun v => ω (u ++ v)

theorem subtreeStepField_measurable
    {α X : Type*} [MeasurableSpace X] (u : TreeNode α) :
    Measurable (subtreeStepField (X := X) u) := by
  apply measurable_pi_iff.mpr
  intro v
  exact measurable_pi_apply (u ++ v)

theorem subtreeStepField_law
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (u : TreeNode α) :
    (stepFieldLaw μ).map (subtreeStepField (X := X) u) =
      stepFieldLaw μ := by
  change (Measure.infinitePi (fun _ : TreeNode α => μ)).map
    (fun ω v => ω (u ++ v)) =
      Measure.infinitePi (fun _ : TreeNode α => μ)
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : TreeNode α => μ)
    (f := fun v : TreeNode α => u ++ v)
    (fun _ _ h => List.append_cancel_left h)

theorem subtreeStepField_position_decomposition
    {α X : Type*} [AddCommMonoid X]
    (ω : TreeNode α → Step α X) (u v : TreeNode α) :
    displace ω [] (u ++ v) =
      displace ω [] u +
        displace (subtreeStepField u ω) [] v := by
  rw [displace_append, List.nil_append]
  congr 1
  rw [show subtreeStepField u ω = (fun x => ω (u ++ x)) from rfl]
  simpa only [List.append_nil] using
    (displace_rebase ω u ([] : TreeNode α) v).symm

end ProbabilityTheory.BranchingRandomWalk
