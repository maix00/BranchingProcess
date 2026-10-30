/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.EndpointFreshField
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.ReserveSpine
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Endpoint
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.FixedHorizon
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Fixed-horizon population law at a successful reserve-spine endpoint

On the finite endpoint event, a first-`N` population grown for a fixed horizon
from the actual endpoint roots has the law obtained by starting from the
endpoint positions and an independent fresh finite-root field. With $E$ the
finite endpoint event, $P$ the two-root field law, $Q$ the independent
$\mathrm{Fin}(\mathrm{lower})$-root field law, $V$ the stopped endpoint
positions, and $F$ the fresh descendant field, the identity is
\[
  (P|_E)\circ\bigl(f\mapsto\operatorname{Pop}_{N,H}(V(f),F(f))\bigr)^{-1}
  =\bigl(((P|_E)\circ V^{-1})\otimes Q\bigr)
    \circ\bigl((x,g)\mapsto\operatorname{Pop}_{N,H}(x,g)\bigr)^{-1}.
\]
The horizon $H$ is fixed. The reusable product-law result for endpoint positions
and a fresh field is in `Completion/EndpointFreshField.lean`; all measurability
and pushforward proof steps specific to this theorem are in
`Completion/Lemmas/FixedHorizon.lean`.

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.selectedReserveSpineRestartEndpointPopulation_law_on_finite`
  states the fixed-horizon population-law identity above under the displayed
  endpoint-capacity and measurability hypotheses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris

/-- Concrete fixed-horizon population law at the successful endpoint.
The endpoint positions need only be measurable in the stopping-time domain
flow. On the finite endpoint event, the first-`N` population grown for a
fixed number of generations from the actual rank-installed endpoint roots has
the law obtained from those positions and a fresh product field. -/
theorem selectedReserveSpineRestartEndpointPopulation_law_on_finite
    {Root α : Type*} (lower : ℕ) [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin lower) α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin lower) α)]
    [Countable (RootIndexed.TreeNode (Fin lower) α)]
    [instFinTreeDecidableEq : DecidableEq (RootIndexed.TreeNode (Fin lower) α)]
    [instFinTreeOrder : LinearOrder (RootIndexed.TreeNode (Fin lower) α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root)
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower → ℝ)
    (hpositions : Measurable[
      (selectedReserveSpineRestartEndpointTime_isStoppingTime
        R growth hR hgrowth lower upper duration r).measurableSpace] positions)
    (H : ℕ) :
    let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    (P.restrict {field | τ field ≠ ⊤}).map
      (fun field => @RootIndexed.selectedPopulationTotalized
        (Fin lower) α ℝ ℝ ℝ instFinTreeDecidableEq instFinTreeOrder
        (inferInstance : LinearOrder ℝ) (inferInstance : AddCommMonoid ℝ)
        N Finset.univ (positions field) id id H
        (RootIndexed.selectedSubtreeStepFieldVector
          (fun field i => (Sum.inr r,
            (selectedReserveSpineRestartEndpointRankVector N initialPosition
              R growth hR hgrowth lower upper duration r field i).2)) field)) =
    (((P.restrict {field | τ field ≠ ⊤}).map positions).prod Q).map
      (fun p => @RootIndexed.selectedPopulationTotalized
        (Fin lower) α ℝ ℝ ℝ instFinTreeDecidableEq instFinTreeOrder
        (inferInstance : LinearOrder ℝ) (inferInstance : AddCommMonoid ℝ)
        N Finset.univ p.1 id id H p.2) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode (Fin lower) α) := instFinTreeDecidableEq
  letI : LinearOrder (RootIndexed.TreeNode (Fin lower) α) := instFinTreeOrder
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hτ := selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ) := {field | τ field ≠ ⊤}
  let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r
  let roots : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower →
      (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α := fun field i =>
    (Sum.inr r, (target field i).2)
  let fresh := fun field => RootIndexed.selectedSubtreeStepFieldVector roots field
  have hsumSingleton : ∀ z : Root ⊕ Root,
      MeasurableSet ({z} : Set (Root ⊕ Root)) := by
    intro z
    cases z with
    | inl x =>
        rw [show ({Sum.inl x} : Set (Root ⊕ Root)) =
          Sum.inl '' ({x} : Set Root) by ext y; simp]
        exact (measurableSet_singleton x).inl_image
    | inr x =>
        rw [show ({Sum.inr x} : Set (Root ⊕ Root)) =
          Sum.inr '' ({x} : Set Root) by ext y; simp]
        exact (measurableSet_singleton x).inr_image
  letI : MeasurableSingletonClass (Root ⊕ Root) := ⟨hsumSingleton⟩
  have hτmeas : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)) τ := by
    simpa [τ] using hτ
  have htarget : Measurable[hτmeas.measurableSpace] target := by
    simpa [target, hτmeas] using
      selectedReserveSpineRestartEndpointRankVector_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hrootsStop : Measurable[hτmeas.measurableSpace] roots := by
    letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
      hτmeas.measurableSpace
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable[hτmeas.measurableSpace] (fun field => target field i) :=
      (measurable_pi_apply i).comp htarget
    exact measurable_const.prodMk (hnodePath.comp hi)
  have hrootsFull : Measurable roots := by
    have hle : hτmeas.measurableSpace ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le n)
    exact hrootsStop.mono hle le_rfl
  have hcount : (Set.range roots).Countable := by
    let encode : (Fin lower → RootIndexed.TreeNode Root α) →
        Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α :=
      fun v i => (Sum.inr r, (v i).2)
    have hsubset : Set.range roots ⊆ Set.range encode := by
      rintro q ⟨field, rfl⟩
      exact ⟨target field, rfl⟩
    exact (Set.countable_range encode).mono hsubset
  have hfresh : Measurable fresh := by
    change Measurable (fun field => RootIndexed.subtreeStepFieldVector
      (roots field) field)
    exact RootIndexed.subtreeStepFieldVector_measurable_of_measurable_roots roots hrootsFull hcount
  have hpositionsFull : Measurable positions := by
    have hle : hτmeas.measurableSpace ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le n)
    exact hpositions.mono hle le_rfl
  have hpair : Measurable (fun field => (positions field, fresh field)) :=
    hpositionsFull.prodMk hfresh
  have hjoint := selectedReserveSpineRestartEndpointPositionFreshField_jointLaw_on_finite
    hnodePath μ hnorm N initialPosition R growth hR hgrowth lower upper duration
    hupper hbounded hcapacity r positions hpositions
  have hpop := selectedReserveSpineRestartEndpointFixedHorizonPopulation_law_on_finite
    μ E positions fresh hpair hjoint N H
  simpa [τ, P, Q, E, roots, fresh] using hpop


end ProbabilityTheory.BranchingRandomWalk
