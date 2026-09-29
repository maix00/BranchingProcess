import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Law
import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Observables

/-!
# Product law with a concrete selected target population

This file closes the causal induction for recursive rank matching when the
target population is the intrinsic first-`N` population of the field built so
far.  Abstract matching remains independent of countability.  Countability is
used here only for the concrete enumerable particle labels, which makes the
finite-population range countable and supplies the existing measurable
selection theorem.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- Recursive equal-rank installation into the concrete selected target is
measurable and preserves the product step-field law. Source-population
adaptedness remains explicit, so the result applies to selected, killed, and
restarted source processes alike. -/
theorem RootIndexed.rankInstalledField_selectedPopulation_measurable_law
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
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ k field p, p ∈ source k field → p.2.length = k)
    (hsourceFiber : ∀ k s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) k]
      {field | source k field = s})
    (hsourceRange : ∀ k, (Set.range (source k)).Countable)
    (hsourceKey : ∀ k p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) k]
      fun field => valueKey (sourceValue k field) q <
        valueKey (sourceValue k field) p) :
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
  let targetValue := fun k
      (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
      (field : RootIndexed.StepField Root α Mark) =>
    RootIndexed.observedPositionAtGeneration initial d φ k field
  let target := fun k
      (_ : RootIndexed.StepField (Root ⊕ Root) α Mark)
      (field : RootIndexed.StepField Root α Mark) =>
    RootIndexed.selectedPopulation N roots initial d φ hadmits k field
  have hstage : ∀ n,
      (Set.range (RootIndexed.rankInstalledBlockChoice
        sourceValue targetValue source target n)).Countable ∧
      ∀ choices, MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n]
        {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
          source target n field = choices} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hpriorCount : ∀ k, k < n → (Set.range
          (RootIndexed.rankInstalledBlockChoice sourceValue targetValue
            source target k)).Countable := fun k hk => (ih k hk).1
      have hpriorFiber : ∀ k, k < n → ∀ choices,
          MeasurableSet[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := Mark) k]
            {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
              source target k field = choices} :=
        fun k hk => (ih k hk).2
      have htargetMeas : Measurable[RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := Mark) n]
          (fun field => target n field
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              RootIndexed.StepField.left RootIndexed.StepField.right n field)) :=
        RootIndexed.selectedPopulation_rankInstalledField_measurable_of_lt
          N roots initial d hd φ hφ hadmits sourceValue targetValue source target
          hsourceDepth n hpriorCount hpriorFiber
      have htargetFiber : ∀ s, MeasurableSet[RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := Mark) n]
          {field | target n field
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              RootIndexed.StepField.left RootIndexed.StepField.right n field) = s} :=
        fun s => htargetMeas (measurableSet_singleton s)
      have htargetRange : (Set.range fun field => target n field
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            RootIndexed.StepField.left RootIndexed.StepField.right n field)
          ).Countable := Set.to_countable _
      have htargetKey : ∀ p q, Measurable[RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := Mark) n]
          fun field => valueKey (targetValue n field
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
            valueKey (targetValue n field
              (RootIndexed.rankInstalledField sourceValue targetValue source target
                RootIndexed.StepField.left RootIndexed.StepField.right n field)) p := by
        let _ : MeasurableSpace
            (RootIndexed.StepField (Root ⊕ Root) α Mark) :=
          RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := Mark) n
        intro p q
        exact measurable_valueKey_lt
          (fun field r => targetValue n field
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              RootIndexed.StepField.left RootIndexed.StepField.right n field) r)
          (fun r => RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
            initial d hd φ hφ sourceValue targetValue source target hsourceDepth
            n hpriorCount hpriorFiber r) p q
      constructor
      · exact RootIndexed.rankBlockChoice_range_countable_of_supports n
          (sourceValue n)
          (fun field => targetValue n field
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              RootIndexed.StepField.left RootIndexed.StepField.right n field))
          (source n)
          (fun field => target n field
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              RootIndexed.StepField.left RootIndexed.StepField.right n field))
          (hsourceRange n) htargetRange
      · intro choices
        exact RootIndexed.measurableSet_rankBlockChoice_eq_of_supports n
          (sourceValue n)
          (fun field => targetValue n field
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              RootIndexed.StepField.left RootIndexed.StepField.right n field))
          (source n)
          (fun field => target n field
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              RootIndexed.StepField.left RootIndexed.StepField.right n field))
          (hsourceFiber n) (hsourceRange n) htargetFiber htargetRange
          (hsourceKey n) htargetKey choices
  have htargetMeas (n : ℕ) : Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) n]
      (fun field => target n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) :=
    RootIndexed.selectedPopulation_rankInstalledField_measurable_of_lt
      N roots initial d hd φ hφ hadmits sourceValue targetValue source target
      hsourceDepth n (fun k hk => (hstage k).1)
      (fun k hk => (hstage k).2)
  have htargetFiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n]
        {field | target n field
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            RootIndexed.StepField.left RootIndexed.StepField.right n field) = s} :=
    htargetMeas n (measurableSet_singleton s)
  have htargetRange (n : ℕ) : (Set.range fun field => target n field
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
      ).Countable := Set.to_countable _
  have htargetKey (n : ℕ) : ∀ p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) n]
      fun field => valueKey (targetValue n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (targetValue n field
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p := by
    let _ : MeasurableSpace
        (RootIndexed.StepField (Root ⊕ Root) α Mark) :=
      RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) n
    intro p q
    exact measurable_valueKey_lt
      (fun field r => targetValue n field
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field) r)
      (fun r => RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
        initial d hd φ hφ sourceValue targetValue source target hsourceDepth n
        (fun k hk => (hstage k).1) (fun k hk => (hstage k).2) r) p q
  have hmeas := RootIndexed.rankInstalledField_measurable_of_supports
    sourceValue targetValue source target hsourceFiber hsourceRange
    htargetFiber htargetRange hsourceKey htargetKey
  have hlaw := RootIndexed.rankInstalledField_law_of_supports μ sourceValue targetValue
    source target hsourceDepth hsourceFiber hsourceRange htargetFiber
    htargetRange hsourceKey htargetKey
  exact fun n => ⟨hmeas n, hlaw n⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
