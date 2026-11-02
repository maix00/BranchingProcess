/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.SelectedPopulation
public import Probability.BranchingRandomWalk.Population.Processes.Causal.Basic
public import Probability.Coupling.Basic
public import Probability.BranchingRandomWalk.Coupling.Field.Position

/-!
# Coupled product law for a causal branching population

The source of the equal-rank coupling may be any finite genealogical process
adapted to the generation domain flow.  Its killing rule may depend on time,
ancestral positions, and all information exposed by the current generation.


## Public declarations

For a finite causal source, recursive equal-rank installation preserves the
product field law and gives a slice-dominating injection on every sample whose
source slice has size at most \(N\):

\[
\mu\circ V_n^{-1}=\operatorname{offspringFieldLaw}(\mu),\qquad
|P_n(\omega)|\le N
\Longrightarrow
\exists\,\iota_n^\omega:P_n(\omega)\hookrightarrow Q_n(V_n(\omega)),
\quad
\phi(X_Q(\iota_n^\omega(p)))\le\phi(X_P(p)).
\]

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.rankInstalledField_causalPopulation_measurable_law`:
  for every stage `n`, the target field installed from a finite causal source
  is measurable and has the original product-field law,
  `μ.map Vₙ = offspringFieldLaw μ`.
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.causalPopulationCoupledInjection`:
  on each sample whose source slices have capacity at most `N`, constructs a
  `SliceDominatingMap` from that causal source slice to the selected target
  slice, assuming an initial slice map and monotonicity under translation.
* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.causalPopulationCoupling`:
  constructs a coupling of two copies of `offspringFieldLaw μ`, with one coordinate
  the source projection and the other the recursively rank-installed field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- Matching an arbitrary causal branching population with finite slices against the
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
    (source : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left)
    (hsourceFinite : source.FiniteSlices) :
    let sourceFinset := hsourceFinite.toFinset
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
      RootIndexed.selectedPopulationTotalized N roots initial d φ k field
    ∀ n, Measurable
        (RootIndexed.rankInstalledField sourceValue targetValue sourceFinset target
          RootIndexed.StepField.left RootIndexed.StepField.right n) ∧
      (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
          (RootIndexed.rankInstalledField sourceValue targetValue sourceFinset target
            RootIndexed.StepField.left RootIndexed.StepField.right n) =
        RootIndexed.stepFieldLaw (Root := Root) μ := by
  dsimp only
  let sourceFinset := hsourceFinite.toFinset
  let sourceValue := fun k
      (field : RootIndexed.StepField (Root ⊕ Root) α Mark) =>
    RootIndexed.observedPositionAtGeneration initial d φ k
      (field.reindex Sum.inl)
  apply RootIndexed.rankInstalledField_totalizedSelectedPopulation_measurable_law
    μ N roots initial d hd
    φ hφ sourceValue sourceFinset
  · intro k field p hp
    exact source.depth k field p ((hsourceFinite.mem_toFinset k field p).mp hp)
  · intro k s
    exact (hsourceFinite.measurable_toFinset k) (measurableSet_singleton s)
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

/-- A capacity-bounded causal population on the left pre-sampled field is
pathwise dominated by first-`N` selection on the recursively coupled field.
The causal successor axiom supplies the offspring-slot inclusion, so callers
do not need to expose an auxiliary selection mechanism. -/
noncomputable def RootIndexed.causalPopulationCoupledInjection
    {Root α Mark Position Value : Type*}
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark]
    [AddCommMonoid Position]
    [LinearOrder Value]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (k : ℕ) (field : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (k + 1) field)
        (Combinatorics.Branching.Population.childrenAtGeneration k parents field))
    (source : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left)
    (hsourceFinite : source.FiniteSlices)
    (initialInjection : ∀ field, Cloud.SliceDominatingMap φ
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial
          (RootIndexed.StepField.left field))
        (hsourceFinite.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial
          (RootIndexed.StepField.right field))
        (RootIndexed.coupledPopulation N roots (fun _ => initial) d φ
          (fun _ => hadmits) RootIndexed.StepField.left
          RootIndexed.StepField.right hsourceFinite.toFinset 0 field)) ())
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark)
    (hsourceCard : ∀ k < n, (hsourceFinite.toFinset (k + 1) field).card ≤ N) :
    Cloud.SliceDominatingMap φ
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial
          (RootIndexed.StepField.left field))
        (hsourceFinite.toFinset n field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial
          (RootIndexed.coupledField N roots (fun _ => initial) d φ
            (fun _ => hadmits) RootIndexed.StepField.left
            RootIndexed.StepField.right hsourceFinite.toFinset n field))
        (RootIndexed.coupledPopulation N roots (fun _ => initial) d φ
          (fun _ => hadmits) RootIndexed.StepField.left
          RootIndexed.StepField.right hsourceFinite.toFinset n field)) () := by
  apply RootIndexed.coupledInjection N roots (fun _ => initial) d φ
    (fun _ => hadmits) RootIndexed.StepField.left
    RootIndexed.StepField.right hsourceFinite.toFinset
    (fun _ field p => support (RootIndexed.StepField.left field p.1 p.2))
    initialInjection
  · intro k sample
    simpa only [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset] using
      source.successor k sample
  · intro k sample p hp i hi
    exact hi
  · exact htranslate
  · exact hsourceCard

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
    (source : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left)
    (hsourceFinite : source.FiniteSlices)
    (n : ℕ) :
    ProbabilityTheory.Coupling
      (RootIndexed.stepFieldLaw (Root := Root) μ)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  let sourceFinset := hsourceFinite.toFinset
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
    RootIndexed.selectedPopulationTotalized N roots initial d φ k field
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let U : RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark := RootIndexed.StepField.left
  let V := RootIndexed.rankInstalledField sourceValue targetValue sourceFinset target
    RootIndexed.StepField.left RootIndexed.StepField.right n
  have hU : Measurable U := by
    change Measurable (RootIndexed.StepField.reindex Sum.inl)
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact (measurable_pi_apply u).comp (measurable_pi_apply (Sum.inl r))
  have hVlaw := RootIndexed.rankInstalledField_causalPopulation_measurable_law
    μ N roots initial d hd φ hφ source hsourceFinite n
  exact ProbabilityTheory.Coupling.ofVariablesOfLaws P U V hU hVlaw.1
    (RootIndexed.stepFieldLaw (Root := Root) μ)
    (RootIndexed.stepFieldLaw (Root := Root) μ)
    (RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective)
    hVlaw.2

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
