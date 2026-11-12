/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Law
public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Observables

/-!
# Product law with a concrete first-\(N\) population

This file closes the causal induction for recursive rank matching from an
input selected population to the intrinsic first-\(N\) population of the
field built so far.  Abstract matching remains independent of countability.
Countability is used here only for the concrete enumerable particle labels,
which makes the finite-population range countable and supplies the existing
measurable-selection theorem.


## Public declarations

At every finite stage \(n\), recursive equal-rank installation is measurable
and preserves the product step-field law:

\[
\operatorname{Measurable}(V_n),\qquad
\mu\circ V_n^{-1}=\operatorname{offspringFieldLaw}(\mu).
\]

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.rankInstalledField_totalizedSelectedPopulation_measurable_law`:
  for every stage `n`, the rank-installed field is measurable and its image
  law under the product field measure equals the original one,
  `μ.map Vₙ = offspringFieldLaw μ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- Recursive equal-rank installation from a selected population into the
totalized first-`N` population is measurable and preserves the product
step-field law. Adaptedness of the input population remains explicit, so the
result applies to selected inputs, including restarted populations. -/
theorem RootIndexed.rankInstalledField_totalizedSelectedPopulation_measurable_law
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
    (selectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.TreeNode Root α → Value)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (hselectedBRWPopulationDepth : ∀ k field p, p ∈ selectedBRWPopulation k field → p.2.length = k)
    (hselectedBRWPopulationFiber : ∀ k s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) k]
      {field | selectedBRWPopulation k field = s})
    (hselectedBRWPopulationRange : ∀ k, (Set.range (selectedBRWPopulation k)).Countable)
    (hselectedBRWPopulationOrderKeyMeasurable : ∀ k p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) k]
      fun field => valueKey (selectedBRWPopulationOrderKey k field) q <
        valueKey (selectedBRWPopulationOrderKey k field) p) :
    let nSelectedBRWPopulationOrderKey := fun k
        (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
        (field : RootIndexed.StepField Root α Mark) =>
      RootIndexed.observedPositionAtGeneration initial d φ k field
    let nSelectedBRWPopulation := fun k
        (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
        (field : RootIndexed.StepField Root α Mark) =>
      RootIndexed.selectedPopulationTotalized N roots initial d φ k field
    ∀ n, Measurable
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n) ∧
      (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
          (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
            RootIndexed.StepField.left RootIndexed.StepField.right n) =
        RootIndexed.stepFieldLaw (Root := Root) μ := by
  dsimp only
  let nSelectedBRWPopulationOrderKey := fun k
      (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
      (field : RootIndexed.StepField Root α Mark) =>
    RootIndexed.observedPositionAtGeneration initial d φ k field
  let nSelectedBRWPopulation := fun k
      (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
      (field : RootIndexed.StepField Root α Mark) =>
    RootIndexed.selectedPopulationTotalized N roots initial d φ k field
  have hstage : ∀ n,
      (Set.range (RootIndexed.rankInstalledBlockChoice
        selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation n)).Countable ∧
      ∀ choices, MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n]
        {field | RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
          selectedBRWPopulation nSelectedBRWPopulation n field = choices} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hpriorCount : ∀ k, k < n → (Set.range
          (RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
            selectedBRWPopulation nSelectedBRWPopulation k)).Countable := fun k hk => (ih k hk).1
      have hpriorFiber : ∀ k, k < n → ∀ choices,
          MeasurableSet[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := Mark) k]
            {field | RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
              selectedBRWPopulation nSelectedBRWPopulation k field = choices} :=
        fun k hk => (ih k hk).2
      have hnSelectedBRWPopulationMeasurable : Measurable[RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := Mark) n]
          (fun field => nSelectedBRWPopulation n field
            (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field)) :=
        RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt
          N roots initial d hd φ hφ selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          hselectedBRWPopulationDepth n hpriorCount hpriorFiber
      have hnSelectedBRWPopulationFiber : ∀ s, MeasurableSet[RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := Mark) n]
          {field | nSelectedBRWPopulation n field
            (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field) = s} :=
        fun s => hnSelectedBRWPopulationMeasurable (measurableSet_singleton s)
      have hnSelectedBRWPopulationRange : (Set.range fun field => nSelectedBRWPopulation n field
          (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
            RootIndexed.StepField.left RootIndexed.StepField.right n field)
          ).Countable := Set.to_countable _
      have hnSelectedBRWPopulationOrderKeyMeasurable : ∀ p q, Measurable[RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := Mark) n]
          fun field => valueKey (nSelectedBRWPopulationOrderKey n field
            (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
            valueKey (nSelectedBRWPopulationOrderKey n field
              (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field)) p := by
        let _ : MeasurableSpace
            (RootIndexed.StepField (Root ⊕ Root) α Mark) :=
          RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := Mark) n
        intro p q
        exact measurable_valueKey_lt
          (fun field r => nSelectedBRWPopulationOrderKey n field
            (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field) r)
          (fun r => RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
            initial d hd φ hφ selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth
            n hpriorCount hpriorFiber r) p q
      constructor
      · exact RootIndexed.rankBlockChoice_range_countable_of_supports n
          (selectedBRWPopulationOrderKey n)
          (fun field => nSelectedBRWPopulationOrderKey n field
            (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field))
          (selectedBRWPopulation n)
          (fun field => nSelectedBRWPopulation n field
            (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field))
          (hselectedBRWPopulationRange n) hnSelectedBRWPopulationRange
      · intro choices
        exact RootIndexed.measurableSet_rankBlockChoice_eq_of_supports n
          (selectedBRWPopulationOrderKey n)
          (fun field => nSelectedBRWPopulationOrderKey n field
            (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field))
          (selectedBRWPopulation n)
          (fun field => nSelectedBRWPopulation n field
            (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field))
          (hselectedBRWPopulationFiber n) (hselectedBRWPopulationRange n) hnSelectedBRWPopulationFiber hnSelectedBRWPopulationRange
          (hselectedBRWPopulationOrderKeyMeasurable n) hnSelectedBRWPopulationOrderKeyMeasurable choices
  have hnSelectedBRWPopulationMeasurable (n : ℕ) : Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) n]
      (fun field => nSelectedBRWPopulation n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) :=
    RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt
      N roots initial d hd φ hφ selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
      hselectedBRWPopulationDepth n (fun k hk => (hstage k).1)
      (fun k hk => (hstage k).2)
  have hnSelectedBRWPopulationFiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n]
        {field | nSelectedBRWPopulation n field
          (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
            RootIndexed.StepField.left RootIndexed.StepField.right n field) = s} :=
    hnSelectedBRWPopulationMeasurable n (measurableSet_singleton s)
  have hnSelectedBRWPopulationRange (n : ℕ) : (Set.range fun field => nSelectedBRWPopulation n field
      (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
      ).Countable := Set.to_countable _
  have hnSelectedBRWPopulationOrderKeyMeasurable (n : ℕ) : ∀ p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) n]
      fun field => valueKey (nSelectedBRWPopulationOrderKey n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (nSelectedBRWPopulationOrderKey n field
          (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p := by
    let _ : MeasurableSpace
        (RootIndexed.StepField (Root ⊕ Root) α Mark) :=
      RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n
    intro p q
    exact measurable_valueKey_lt
      (fun field r => nSelectedBRWPopulationOrderKey n field
        (RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field) r)
      (fun r => RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
        initial d hd φ hφ selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth n
        (fun k hk => (hstage k).1) (fun k hk => (hstage k).2) r) p q
  have hmeas := RootIndexed.rankInstalledField_measurable_of_supports
    selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationFiber hselectedBRWPopulationRange
    hnSelectedBRWPopulationFiber hnSelectedBRWPopulationRange hselectedBRWPopulationOrderKeyMeasurable hnSelectedBRWPopulationOrderKeyMeasurable
  have hlaw := RootIndexed.rankInstalledField_law_of_supports μ selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
    selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth hselectedBRWPopulationFiber hselectedBRWPopulationRange hnSelectedBRWPopulationFiber
    hnSelectedBRWPopulationRange hselectedBRWPopulationOrderKeyMeasurable hnSelectedBRWPopulationOrderKeyMeasurable
  exact fun n => ⟨hmeas n, hlaw n⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
