/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Measurability.Field

/-!
# Measurable observables of the recursive matched field

Concrete first-`N` populations and observed positions are measurable after the
matched field has been shown measurable for the generation domain flow.

## Public declarations

For `F_n = rankInstalledField n`, define the selected population
`P_n(ω) = selectedPopulationTotalized N roots initial d φ n (F_n ω)` and the
observed position `X_n(ω,p) = observedPositionAtGeneration initial d φ n
(F_n ω) p`. The declarations prove that `P_n` and `X_n(·,p)` are measurable
for the generation-`n` domain flow. Thus

\[\begin{aligned}
P_n(\omega)&=\operatorname{selectedPopulationTotalized}(
N,\mathrm{roots},\mathrm{initial},d,\phi,n,F_n(\omega)),\\
P_n&\text{ is measurable for the generation-}n\text{ domain flow},\\
X_n(\omega,p)&=\operatorname{observedPositionAtGeneration}(
\mathrm{initial},d,\phi,n,F_n(\omega))(p),\\
\omega&\mapsto X_n(\omega,p)\text{ is measurable for that domain flow}.
\end{aligned}\]

* `RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt`
  proves the selected-population assertion from hypotheses on the strictly
  earlier generation coordinate maps.
* `RootIndexed.observedPosition_rankInstalledField_measurable_of_lt` proves
  the observed-position assertion under the same hypotheses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- The totalized selected population evaluated on a stage-`n` matched field
is measurable using only the measurable lower-finite selector. -/
theorem RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt
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
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ k field p, p ∈ source k field → p.2.length = k)
    (n : ℕ)
    (hcount : ∀ k, k < n → (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target k)).Countable)
    (hfiber : ∀ k, k < n → ∀ choices,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k]
        {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
          source target k field = choices}) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) n]
      (fun field => RootIndexed.selectedPopulationTotalized N roots initial d φ n
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) := by
  have hprior := RootIndexed.rankInstalledField_domainFlow_measurable_of_lt
    sourceValue targetValue source target hsourceDepth n hcount hfiber
  have hselected := RootIndexed.selectedPopulationTotalized_adapted
    (Root := Root) (α := α) (Mark := Mark) (Position := Position)
    (Value := Value) N roots initial d hd φ hφ n
  exact hselected.comp hprior

/-- An observed generation position in the stage-`n` matched field is
measurable from predictability of the strictly earlier matching stages. -/
theorem RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
    {Root α Mark Position Value : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ)
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ k field p, p ∈ source k field → p.2.length = k)
    (n : ℕ)
    (hcount : ∀ k, k < n → (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target k)).Countable)
    (hfiber : ∀ k, k < n → ∀ choices,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k]
        {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
          source target k field = choices})
    (p : RootIndexed.TreeNode Root α) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := Mark) n]
      (fun field => RootIndexed.observedPositionAtGeneration initial d φ n
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field) p) := by
  have hprior := RootIndexed.rankInstalledField_domainFlow_measurable_of_lt
    sourceValue targetValue source target hsourceDepth n hcount hfiber
  exact hφ.comp ((RootIndexed.positionAtGeneration_measurable
    initial d hd n p.1 p.2).comp hprior)

end ProbabilityTheory.BranchingRandomWalk.Coupling
