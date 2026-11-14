/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SelectedPath.Completion.Horizon

/-!
# Terminal expectation from a successful growth trial

## Public declarations

* `integral_terminalPayoff_on_finite_completion` transfers the success-cell
  contribution to a terminal expectation. If the successful completion time is
  $\tau$, the endpoint positions are $V$, and the actual descendant field is
  $F$, the contribution of a measurable payoff $g$ at terminal generation $m$
  is
  \[\int_{\{\tau<\infty\}} g(m-\tau,V,F)\,dP
    = \int g(m-t,v,f)\,d(\lambda\otimes Q)(t,v,f),\]
  where $\lambda$ is the stopped joint law of $(\tau,V)$ restricted to
  finite completion and $Q$ is the fresh descendant field law.
-/

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open EndpointDeviation.SelectedPath

/-- Transfer the finite-completion part of a terminal payoff to the product
of the stopped endpoint law and the fresh field law. -/
theorem integral_terminalPayoff_on_finite_completion
    {Root α : Type*} (lower : ℕ) [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSingletonClass (Root ⊕ Root)]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin lower) α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin lower) α)]
    [Countable (RootIndexed.TreeNode (Fin lower) α)]
    [DecidableEq (RootIndexed.TreeNode (Fin lower) α)]
    [LinearOrder (RootIndexed.TreeNode (Fin lower) α)]
    (hnodePath : Measurable
      (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root)
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      Fin lower → ℝ)
    (hpositions : Measurable[
      (Completion.time_isStoppingTime
        R growth hR hgrowth lower upper duration r).measurableSpace]
      positions)
    (terminal : ℕ)
    (payoff : (ℕ × (Fin lower → ℝ)) × RootIndexed.StepField (Fin lower) α ℝ → ℝ)
    (hpayoff : Measurable payoff) :
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    let roots := fun field i => (Sum.inr r,
      (Completion.endpointNodesByRank N initialPosition R growth hR hgrowth
        lower upper duration r field i).2)
    (∫ field in {field | τ field ≠ ⊤},
      payoff ((terminal - (τ field).untopD 0, positions field),
        RootIndexed.selectedSubtreeStepFieldVector roots field) ∂P) =
      ∫ p, payoff ((terminal - p.1.1.untopD 0, p.1.2), p.2)
        ∂((((P.restrict {field | τ field ≠ ⊤}).map
          (fun field => (τ field, positions field))).prod Q)) := by
  intro τ P Q roots
  obtain ⟨hmeas, hlaw⟩ := Completion.timePositionFreshField_jointLaw_on_finite
    lower hnodePath μ hnorm N initialPosition R growth hR hgrowth upper duration
    hupper hbounded hcapacity r positions hpositions
  let f := fun field => ((τ field, positions field),
    RootIndexed.selectedSubtreeStepFieldVector roots field)
  let g := fun p : (WithTop ℕ × (Fin lower → ℝ)) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
    payoff ((terminal - p.1.1.untopD 0, p.1.2), p.2)
  have htime : Measurable (fun t : WithTop ℕ => terminal - t.untopD 0) :=
    measurable_of_countable _
  have hg : Measurable g := hpayoff.comp
    (((htime.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd)
  have hf : Measurable f := hmeas
  change (∫ field, g (f field) ∂(P.restrict {field | τ field ≠ ⊤})) = _
  rw [← integral_map hf.aemeasurable hg.aestronglyMeasurable, hlaw]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
