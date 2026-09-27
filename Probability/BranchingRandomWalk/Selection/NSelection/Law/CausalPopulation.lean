import Probability.BranchingRandomWalk.Selection.NSelection.Law.SelectedPopulation
import Probability.BranchingRandomWalk.Population.Processes.Causal
import Probability.Coupling.Basic

/-!
# Coupled product law for a causal finite branching population

The source of the equal-rank coupling may be any finite genealogical process
adapted to the generation domain flow.  Its killing rule may depend on time,
ancestral positions, and all information exposed by the current generation.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- Matching an arbitrary causal finite branching population against the
concrete first-`N` population is measurable and preserves the latter's
product step-field law. -/
theorem RootIndexed.rankInstalledField_causalPopulation_measurable_law
    {Root α Mark Position Value : Type*}
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (hadmits : ∀ (k : ℕ) (field : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (k + 1) field)
        (RootIndexed.childrenAtGeneration k parents field))
    (source : RootIndexed.CausalFinitePopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left) :
    let sourceValue := fun k
        (field : RootIndexed.StepField (Root ⊕ Root) α Mark) =>
      RootIndexed.observedPositionAtGeneration initial d φ k
        (field.reindex Sum.inl)
    let targetValue := fun k
        (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
        (field : RootIndexed.StepField Root α Mark) =>
      RootIndexed.observedPositionAtGeneration initial d φ k field
    let target := fun k
        (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
        (field : RootIndexed.StepField Root α Mark) =>
      RootIndexed.selectedPopulation N roots initial d φ hadmits k field
    ∀ n, Measurable
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n) ∧
      (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            RootIndexed.StepField.left RootIndexed.StepField.right n) =
        RootIndexed.stepFieldLaw (Root := Root) μ := by
  dsimp only
  let sourceValue := fun k
      (field : RootIndexed.StepField (Root ⊕ Root) α Mark) =>
    RootIndexed.observedPositionAtGeneration initial d φ k
      (field.reindex Sum.inl)
  apply RootIndexed.rankInstalledField_selectedPopulation_measurable_law
    μ N roots initial d hd
    φ hφ hadmits sourceValue source
  · exact source.depth
  · intro k s
    exact (source.adapted k) (measurableSet_singleton s)
  · intro k
    exact Set.to_countable _
  · intro k p q
    let _ : MeasurableSpace
        (RootIndexed.StepField (Root ⊕ Root) α Mark) :=
      RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k
    apply measurable_valueKey_lt
    intro r
    exact hφ.comp ((RootIndexed.positionAtGeneration_measurable
      initial d hd k r.1 r.2).comp
        (RootIndexed.StepField.reindex_filtration_measurable Sum.inl k))

/-- The common pre-sampled source field and its recursively rank-installed
target define an actual coupling of two copies of the root-indexed product
law.  The first marginal is the left root projection; the second marginal is
the measurable matched field. -/
noncomputable def RootIndexed.causalPopulationCoupling
    {Root α Mark Position Value : Type*}
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (hadmits : ∀ (k : ℕ) (field : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (k + 1) field)
        (RootIndexed.childrenAtGeneration k parents field))
    (source : RootIndexed.CausalFinitePopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left)
    (n : ℕ) :
    ProbabilityTheory.Coupling
      (RootIndexed.stepFieldLaw (Root := Root) μ)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  let sourceValue := fun k
      (field : RootIndexed.StepField (Root ⊕ Root) α Mark) =>
    RootIndexed.observedPositionAtGeneration initial d φ k
      (field.reindex Sum.inl)
  let targetValue := fun k
      (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
      (field : RootIndexed.StepField Root α Mark) =>
    RootIndexed.observedPositionAtGeneration initial d φ k field
  let target := fun k
      (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
      (field : RootIndexed.StepField Root α Mark) =>
    RootIndexed.selectedPopulation N roots initial d φ hadmits k field
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let U : RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark := RootIndexed.StepField.left
  let V := RootIndexed.rankInstalledField sourceValue targetValue source target
    RootIndexed.StepField.left RootIndexed.StepField.right n
  have hU : Measurable U := by
    change Measurable (RootIndexed.StepField.reindex Sum.inl)
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact (measurable_pi_apply u).comp (measurable_pi_apply (Sum.inl r))
  have hVlaw := RootIndexed.rankInstalledField_causalPopulation_measurable_law
    μ N roots initial d hd φ hφ hadmits source n
  exact ProbabilityTheory.Coupling.ofVariablesOfLaws P U V hU hVlaw.1
    (RootIndexed.stepFieldLaw (Root := Root) μ)
    (RootIndexed.stepFieldLaw (Root := Root) μ)
    (RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective)
    hVlaw.2

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
