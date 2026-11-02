/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The root-step batch of a root-indexed field

## Public declarations

Reading the empty-address step from every root of an i.i.d. root-indexed
field gives the product batch law:

\[
\left(\operatorname{stepFieldLaw}_{R}^{\mu}\right)
\circ\left(\operatorname{rootStepBatch}\right)^{-1}
=\operatorname{Measure.infinitePi}(\lambda\_ : R,\mu).
\]

- `RootIndexed.rootStepBatch` maps a root-indexed field
  `Root → TreeNode α → Step α X` to its root-step family
  `Root → Step α X`, by evaluating each tree at the empty address.
- `RootIndexed.measurable_rootStepBatch` proves measurability of this map.
- `RootIndexed.stepFieldLaw_map_rootStepBatch` states that for any `Root`,
  the root-step family of a field with law `stepFieldLaw μ` has product law
  `Measure.infinitePi (fun _ : Root => μ)`.

This is the fixed-coordinate batch interface. Generation-measurable choices
of subtree roots and their independence statements are in
`Genealogy/Exploration/RootIndexed/SelectedSubtrees/GenerationBatch.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk

/-- Read the step at the root of each tree in a root-indexed field. -/
def rootStepBatch {Root α X : Type*}
    (field : RootIndexed.StepField Root α X) : Root → Step α X :=
  fun i => field i []

theorem measurable_rootStepBatch {Root α X : Type*} [MeasurableSpace X] :
    Measurable (rootStepBatch (Root := Root) (α := α) (X := X)) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply ([] : TreeNode α)).comp
    (measurable_pi_apply i)

/-- The root steps of an i.i.d. root-indexed field have the usual batch law. -/
theorem stepFieldLaw_map_rootStepBatch
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (rootStepBatch (Root := Root) (α := α) (X := X)) =
      Measure.infinitePi (fun _ : Root => μ) := by
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let coordinate : Root → RootIndexed.StepField Root α X → Step α X :=
    fun i field => field i []
  have hX : ∀ i, AEMeasurable (coordinate i) P := by
    intro i
    exact ((measurable_pi_apply ([] : TreeNode α)).comp
      (measurable_pi_apply i)).aemeasurable
  have hind : iIndepFun coordinate P := by
    have hcoord := RootIndexed.stepFieldLaw_coordinates_independent
      (Root := Root) (α := α) μ
    have hinj : Function.Injective (fun i : Root => (i, ([] : TreeNode α))) := by
      intro i j hij
      exact congrArg Prod.fst hij
    have h := hcoord.precomp hinj
    change iIndep
      (fun i : Root => RootIndexed.stepCoordinateSpace
        (Root := Root) (α := α) (X := X) (i, []))
      (RootIndexed.stepFieldLaw (Root := Root) μ) at h
    have h' : iIndep
        (fun i : Root => RootIndexed.stepCoordinateSpace
          (Root := Root) (α := α) (X := X) (i, [])) P := by
      simpa [P] using h
    have hindep : iIndep
        (fun i : Root => (inferInstance : MeasurableSpace (Step α X)).comap
          (coordinate i)) P := by
      simpa [coordinate, RootIndexed.stepCoordinateSpace] using h'
    apply (iIndepFun_iff_iIndep
      (fun _ : Root => (inferInstance : MeasurableSpace (Step α X)))
      coordinate P).2
    exact hindep
  have hXi (i : Root) : HasLaw (coordinate i) μ P := by
    refine ⟨hX i, ?_⟩
    exact RootIndexed.stepFieldLaw_coordinate_marginal
      (Root := Root) (α := α) μ i []
  have hbatch : HasLaw (fun field i => coordinate i field)
      (Measure.infinitePi (fun _ : Root => μ)) P :=
    (iIndepFun_iff_hasLaw_Pi_infinitePi hXi
      measurable_rootStepBatch.aemeasurable).mp hind
  change P.map (fun field i => field i []) =
    Measure.infinitePi (fun _ : Root => μ)
  exact hbatch.map_eq

end ProbabilityTheory.BranchingRandomWalk.RootIndexed

end
