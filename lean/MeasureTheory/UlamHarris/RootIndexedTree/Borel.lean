import MeasureTheory.UlamHarris.RootIndexedTree.Metric
import MeasureTheory.UlamHarris.Tree.Borel
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Borel structure on root-indexed trees

`RootIndexedTree Root α` carries the product σ-algebra of the tree σ-algebras.
The default product topology makes it a Borel space with exactly this
σ-algebra when both the roots and the labels are countable. The finer
product-truncation and uniform topologies contain at least the cylinder
σ-algebra; if their bases are countable and cylinder-measurable, their Borel
σ-algebras coincide with the cylinder σ-algebra as well.

The metric topology agrees with the uniform topology, so their Borel
σ-algebras agree without any further countability hypothesis on the roots.
-/

open MeasureTheory
open scoped Topology

set_option linter.style.haveILetI false

namespace MeasureTheory

namespace UlamHarris

namespace RootIndexedTree

variable {Root α : Type*} [LT α]

/-- Under countably many roots and labels, the Borel σ-algebra of the default
product topology is the product σ-algebra carried by a root-indexed tree. -/
theorem borel_pointwiseTopology_eq_cylinder [Countable Root] [Countable α] :
    @borel (RootIndexedTree Root α)
      (inferInstance : TopologicalSpace (RootIndexedTree Root α)) =
      (inferInstance : MeasurableSpace (RootIndexedTree Root α)) :=
  (BorelSpace.measurable_eq (α := RootIndexedTree Root α)).symm

/-- The default product topology makes a root-indexed tree a Borel space with
the product σ-algebra. -/
instance instBorelSpaceRootIndexedTree [Countable Root] [Countable α] :
    BorelSpace (RootIndexedTree Root α) :=
  ⟨borel_pointwiseTopology_eq_cylinder.symm⟩

/-- The cylinder σ-algebra is contained in the Borel σ-algebra of the product
truncation topology. -/
theorem cylinder_le_borel_productTruncation [Countable Root] [Countable α] :
    (inferInstance : MeasurableSpace (RootIndexedTree Root α)) ≤
      @borel (RootIndexedTree Root α)
        (productTruncationTopology (Root := Root) (α := α)) :=
  by
    rw [← borel_pointwiseTopology_eq_cylinder]
    exact borel_anti
      (productTruncationTopology_le_pointwise (Root := Root) (α := α))

/-- The cylinder σ-algebra is contained in the Borel σ-algebra of the uniform
topology. -/
theorem cylinder_le_borel_uniformTopology [Countable Root] [Countable α] :
    (inferInstance : MeasurableSpace (RootIndexedTree Root α)) ≤
      @borel (RootIndexedTree Root α)
        (uniformTopology (Root := Root) (α := α)) :=
  by
    rw [← borel_pointwiseTopology_eq_cylinder]
    exact borel_anti
      ((uniformTopology_le_productTruncation (Root := Root) (α := α)).trans
        (productTruncationTopology_le_pointwise (Root := Root) (α := α)))

/-- If the product truncation topology has a countable basis of
cylinder-measurable sets, then its Borel σ-algebra is exactly the cylinder
σ-algebra. -/
theorem borel_productTruncationTopology_eq_cylinder_of_countable_basis
    [Countable Root] [Countable α]
    {B : Set (Set (RootIndexedTree Root α))}
    (hB : TopologicalSpace.IsTopologicalBasis
      (t := productTruncationTopology (Root := Root) (α := α)) B)
    (hcount : B.Countable) (hmeas : ∀ s ∈ B, MeasurableSet s) :
    @borel (RootIndexedTree Root α)
        (productTruncationTopology (Root := Root) (α := α)) =
      (inferInstance : MeasurableSpace (RootIndexedTree Root α)) :=
  le_antisymm (borel_le_of_countable_basis hB hcount hmeas)
    cylinder_le_borel_productTruncation

/-- If the uniform topology has a countable basis of cylinder-measurable sets,
then its Borel σ-algebra is exactly the cylinder σ-algebra. -/
theorem borel_uniformTopology_eq_cylinder_of_countable_basis
    [Countable Root] [Countable α]
    {B : Set (Set (RootIndexedTree Root α))}
    (hB : TopologicalSpace.IsTopologicalBasis
      (t := uniformTopology (Root := Root) (α := α)) B)
    (hcount : B.Countable) (hmeas : ∀ s ∈ B, MeasurableSet s) :
    @borel (RootIndexedTree Root α)
        (uniformTopology (Root := Root) (α := α)) =
      (inferInstance : MeasurableSpace (RootIndexedTree Root α)) :=
  le_antisymm (borel_le_of_countable_basis hB hcount hmeas)
    cylinder_le_borel_uniformTopology

/-- The Borel σ-algebras of the uniform and metric topologies coincide. -/
theorem borel_uniformTopology_eq_borel_metricTopology [Nonempty Root] :
    @borel (RootIndexedTree Root α)
        (metricTopology (Root := Root) (α := α)) =
      @borel (RootIndexedTree Root α)
        (uniformTopology (Root := Root) (α := α)) := by
  rw [metricTopology_eq_uniformTopology]

/-- If the uniform topology has a countable basis of cylinder-measurable sets,
then the Borel σ-algebra of the sup tree metric is exactly the cylinder
σ-algebra. -/
theorem borel_metricTopology_eq_cylinder_of_countable_basis [Nonempty Root]
    [Countable Root] [Countable α]
    {B : Set (Set (RootIndexedTree Root α))}
    (hB : TopologicalSpace.IsTopologicalBasis
      (t := uniformTopology (Root := Root) (α := α)) B)
    (hcount : B.Countable) (hmeas : ∀ s ∈ B, MeasurableSet s) :
    @borel (RootIndexedTree Root α)
        (metricTopology (Root := Root) (α := α)) =
      (inferInstance : MeasurableSpace (RootIndexedTree Root α)) := by
  rw [borel_uniformTopology_eq_borel_metricTopology]
  exact borel_uniformTopology_eq_cylinder_of_countable_basis hB hcount hmeas

end RootIndexedTree

end UlamHarris

end MeasureTheory
