/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.EndpointFreshField
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.ReserveSpine
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Endpoint
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.RootFamily
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.Geometry
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.FreshField
public import Probability.Process.Stopping.Selection.Ranked
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Endpoint-dependent finite restart horizons

## Public declarations

* selectedReserveSpineRestartEndpointTimePositionFreshField_jointLaw_on_finite gives the
  product-law identity
  \[
    \mathcal L\bigl((\tau,\mathrm{positions}),\mathrm{fresh}\mid \tau<\infty\bigr)
    =
    \mathcal L\bigl((\tau,\mathrm{positions})\mid \tau<\infty\bigr)
      \otimes \mathcal L(\mathrm{fresh}),
  \]
  where \(\tau\) is the first successful candidate's completion generation and \mathrm{fresh}
  is the descendant field rooted at the selected endpoint particles.
* selectedReserveSpineRestartEndpointRandomHorizonObservable_law_on_finite pushes this law
  through every measurable observable of the stopped endpoint data and its fresh field,
  including an observable whose remaining horizon is read from \tau.
-/


@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

/-- The successful endpoint time, endpoint positions, and their actual
rank-installed first-`N` BRW descendant field have the joint law obtained by
attaching a fresh product field to the stopped endpoint data.  The first
coordinate is the `WithTop` completion time, which equals `σᵢ + duration` for
the successful candidate; the split's raw look-ahead generation is not used
as a stopping time. -/
theorem selectedReserveSpineRestartEndpointTimePositionFreshField_jointLaw_on_finite
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
      (selectedReserveSpineRestartEndpointTime_isStoppingTime
        R growth hR hgrowth lower upper duration r).measurableSpace]
      positions) :
    let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    let endpointData := fun field => (τ field, positions field)
    let nSelectedBRWEndpointRoots := fun field i =>
      (Sum.inr r, (selectedReserveSpineRestartNSelectedBRWEndpointRankVector N
        initialPosition R growth hR hgrowth lower upper duration r field i).2)
    let fresh := fun field =>
      RootIndexed.selectedSubtreeStepFieldVector nSelectedBRWEndpointRoots field
    Measurable (fun field => (endpointData field, fresh field)) ∧
    (P.restrict {field | τ field ≠ ⊤}).map
      (fun field => (endpointData field, fresh field)) =
    ((P.restrict {field | τ field ≠ ⊤}).map endpointData).prod Q := by
  classical
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hτ := selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
    {field | τ field ≠ ⊤}
  let endpointData : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      WithTop ℕ × (Fin lower → ℝ) := fun field => (τ field, positions field)
  let nSelectedBRWEndpointRankVector := selectedReserveSpineRestartNSelectedBRWEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r
  let nSelectedBRWEndpointRoots : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower →
      (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α := fun field i =>
    (Sum.inr r, (nSelectedBRWEndpointRankVector field i).2)
  let fresh := fun field =>
    RootIndexed.selectedSubtreeStepFieldVector nSelectedBRWEndpointRoots field
  let data := fun field => endpointData field
  have hτmeas : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)) τ := by
    simpa [τ] using hτ
  have htime : Measurable[hτmeas.measurableSpace] τ := by
    intro s hs
    exact hτmeas.measurable hs
  have hdataStop : Measurable[hτmeas.measurableSpace] data := by
    exact htime.prodMk (by simpa [hτmeas] using hpositions)
  have hle : hτmeas.measurableSpace ≤
      (inferInstance : MeasurableSpace
        (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
    hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
      (RootIndexed.stepFiltration (Root := Root ⊕ Root)
        (α := α) (X := ℝ)).le n)
  have hdata : Measurable data := hdataStop.mono hle le_rfl
  have hnSelectedBRWEndpointRankVector : Measurable[hτmeas.measurableSpace] nSelectedBRWEndpointRankVector := by
    simpa [nSelectedBRWEndpointRankVector, hτmeas] using
      selectedReserveSpineRestartNSelectedBRWEndpointRankVector_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hnSelectedBRWRootsStopped : Measurable[hτmeas.measurableSpace] nSelectedBRWEndpointRoots := by
    letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
      hτmeas.measurableSpace
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable[hτmeas.measurableSpace]
        (fun field => nSelectedBRWEndpointRankVector field i) :=
      (measurable_pi_apply i).comp hnSelectedBRWEndpointRankVector
    exact measurable_const.prodMk (hnodePath.comp hi)
  have hnSelectedBRWRootsMeasurable : Measurable nSelectedBRWEndpointRoots := hnSelectedBRWRootsStopped.mono hle le_rfl
  have hcount : (Set.range nSelectedBRWEndpointRoots).Countable := by
    let encode : (Fin lower → RootIndexed.TreeNode Root α) →
        Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α :=
      fun v i => (Sum.inr r, (v i).2)
    have hsubset : Set.range nSelectedBRWEndpointRoots ⊆ Set.range encode := by
      rintro q ⟨field, rfl⟩
      exact ⟨nSelectedBRWEndpointRankVector field, rfl⟩
    exact (Set.countable_range encode).mono hsubset
  have hfresh : Measurable fresh := by
    change Measurable (fun field =>
      RootIndexed.subtreeStepFieldVector (nSelectedBRWEndpointRoots field) field)
    exact RootIndexed.subtreeStepFieldVector_measurable_of_measurable_roots
      nSelectedBRWEndpointRoots hnSelectedBRWRootsMeasurable hcount
  have hpair : Measurable (fun field => (data field, fresh field)) :=
    hdata.prodMk hfresh
  have hrect : ∀ {S : Set (WithTop ℕ × (Fin lower → ℝ))}
      {T : Set (Fin lower → Combinatorics.UlamHarris.TreeNode α → Step α ℝ)},
      MeasurableSet S → MeasurableSet T →
      ((P.restrict E).map (fun field => (data field, fresh field)))
          (S ×ˢ T) =
        (((P.restrict E).map data).prod Q) (S ×ˢ T) := by
    intro S T hS hT
    rw [Measure.map_apply hpair (hS.prod hT)]
    have hA : MeasurableSet[hτmeas.measurableSpace] (data ⁻¹' S) :=
      hdataStop hS
    have hfactor := selectedReserveSpineRestartNSelectedBRWFreshField_factorization_on_finite
      hnodePath μ hnorm N initialPosition R growth hR hgrowth lower upper duration
      hupper hbounded hcapacity r (data ⁻¹' S) T hA hT
    rw [show (data ⁻¹' S ∩ E) ∩ fresh ⁻¹' T =
        E ∩ data ⁻¹' S ∩ fresh ⁻¹' T by
      ext field
      simp [and_assoc, and_left_comm, and_comm]] at hfactor
    rw [Measure.restrict_apply (hpair (hS.prod hT))]
    rw [show (fun field => (data field, fresh field)) ⁻¹' (S ×ˢ T) =
        data ⁻¹' S ∩ fresh ⁻¹' T by
      ext field
      simp]
    rw [Measure.prod_prod, Measure.map_apply hdata hS,
      Measure.restrict_apply (hdata hS)]
    simpa [P, Q, E, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hfactor
  have hjoint :
      (P.restrict E).map (fun field => (data field, fresh field)) =
        ((P.restrict E).map data).prod Q :=
    Measure.ext_prod hrect
  refine ⟨hpair, ?_⟩
  simpa [τ, P, Q, E, endpointData, data, nSelectedBRWEndpointRankVector, nSelectedBRWEndpointRoots, fresh] using hjoint

/-- Transfer any measurable continuation observable whose remaining horizon
is read from the successful endpoint time.  For a deterministic terminal
generation `m`, take `horizon t := m - t.untopD 0`; on the finite-endpoint
event this is exactly the remaining number of generations.  This is a
random-horizon law, obtained by including the stopped endpoint time in the
stopped data before applying the fresh-field product law. -/
theorem selectedReserveSpineRestartEndpointRandomHorizonObservable_law_on_finite
    {Root α Outcome : Type*} (lower : ℕ) [MeasurableSpace Outcome]
    [Countable α] [MeasurableSpace α]
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
      (selectedReserveSpineRestartEndpointTime_isStoppingTime
        R growth hR hgrowth lower upper duration r).measurableSpace]
      positions)
    (future : (WithTop ℕ × (Fin lower → ℝ)) ×
      RootIndexed.StepField (Fin lower) α ℝ → Outcome)
    (hfuture : Measurable future) :
    let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    (P.restrict {field | τ field ≠ ⊤}).map
      (fun field => future ((τ field, positions field),
        RootIndexed.selectedSubtreeStepFieldVector
          (fun field i => (Sum.inr r,
            (selectedReserveSpineRestartNSelectedBRWEndpointRankVector N initialPosition
              R growth hR hgrowth lower upper duration r field i).2)) field)) =
    ((((P.restrict {field | τ field ≠ ⊤}).map
      (fun field => (τ field, positions field))).prod Q).map future) := by
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let endpointData := fun field => (τ field, positions field)
  let fresh := fun field =>
    RootIndexed.selectedSubtreeStepFieldVector
      (fun field i => (Sum.inr r,
        (selectedReserveSpineRestartNSelectedBRWEndpointRankVector N initialPosition
          R growth hR hgrowth lower upper duration r field i).2)) field
  have ⟨hpair, hjoint⟩ := selectedReserveSpineRestartEndpointTimePositionFreshField_jointLaw_on_finite
    lower hnodePath μ hnorm N initialPosition R growth hR hgrowth upper duration
    hupper hbounded hcapacity r positions hpositions
  change (P.restrict {field | τ field ≠ ⊤}).map
      (future ∘ fun field => (endpointData field, fresh field)) =
    ((((P.restrict {field | τ field ≠ ⊤}).map endpointData).prod Q).map future)
  rw [← Measure.map_map hfuture hpair, hjoint]

end ProbabilityTheory.BranchingRandomWalk
