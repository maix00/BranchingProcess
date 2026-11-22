/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.FreshField
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Stopping
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EndpointHorizon.RootFamily
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EndpointHorizon.Geometry
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EndpointHorizon.FreshField
public import Probability.Process.Stopping.Selection.Ranked
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Endpoint-dependent finite restart horizons

## Public declarations

* `timePositionStoppedEntrance_jointLaw_on_finite` gives the product law
  $\mathcal L_{\{\tau<\infty\}}(\tau,X,\Phi)=
  \mathcal L_{\{\tau<\infty\}}(\tau,X)\otimes Q_m$, where $X$ is stopped
  measurable and $\Phi$ consists of the $m$ actual descendant subtrees after
  rank installation ends at $\tau$.
* ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.timePositionFreshField_jointLaw_on_finite gives the
  product-law identity
  \[
    \mathcal L\bigl((\tau,\mathrm{positions}),\mathrm{fresh}\mid \tau<\infty\bigr)
    =
    \mathcal L\bigl((\tau,\mathrm{positions})\mid \tau<\infty\bigr)
      \otimes \mathcal L(\mathrm{fresh}),
  \]
  where \(\tau\) is the first successful candidate's completion generation and \mathrm{fresh}
  is the descendant field rooted at the selected endpoint particles.
* ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.randomHorizonObservable_law_on_finite pushes this law
  through every measurable observable of the stopped endpoint data and its fresh field,
  including an observable whose remaining horizon is read from \tau.
-/


@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EndpointHorizon
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

/-- The successful endpoint time, endpoint positions, and their actual
rank-installed first-`N` BRW descendant field have the joint law obtained by
attaching a fresh product field to the stopped endpoint data.  The first
coordinate is the `WithTop` completion time, which equals `σᵢ + duration` for
the successful candidate; the split's raw look-ahead generation is not used
as a stopping time. -/
theorem timePositionFreshField_jointLaw_on_finite
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
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.time_isStoppingTime
        R growth hR hgrowth lower upper duration r).measurableSpace]
      positions) :
    let τ := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    let endpointData := fun field => (τ field, positions field)
    let nSelectedBRWEndpointRoots := fun field i =>
      (Sum.inr r, (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.endpointNodesByRank N
        initialPosition R growth hR hgrowth lower upper duration r field i).2)
    let fresh := fun field =>
      RootIndexed.selectedSubtreeStepFieldVector nSelectedBRWEndpointRoots field
    Measurable (fun field => (endpointData field, fresh field)) ∧
    (P.restrict {field | τ field ≠ ⊤}).map
      (fun field => (endpointData field, fresh field)) =
    ((P.restrict {field | τ field ≠ ⊤}).map endpointData).prod Q := by
  classical
  let τ := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.time R growth hR hgrowth
    lower upper duration r
  let hτ := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.time_isStoppingTime
    R growth hR hgrowth lower upper duration r
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
    {field | τ field ≠ ⊤}
  let endpointData : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      WithTop ℕ × (Fin lower → ℝ) := fun field => (τ field, positions field)
  let nSelectedBRWEndpointRankVector := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.endpointNodesByRank N initialPosition
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
      ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.endpointNodesByRank_measurable N initialPosition
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
    have hfactor := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EndpointHorizon.nSelectedBRWFreshField_factorization_on_finite
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

/-- The actual field that stops installing entrance marks at the successful
completion has fresh descendant fields at the retained ranks, conditional on
the stopped time and position data. -/
theorem timePositionStoppedEntrance_jointLaw_on_finite
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
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.time_isStoppingTime
        R growth hR hgrowth lower upper duration r).measurableSpace]
      positions) :
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration r
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N {r} initialPosition trials τ hτ
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    let data := fun field => (τ field, positions field)
    let roots := fun field (i : Fin lower) =>
      (r, (endpointNodesByRank N initialPosition R growth hR hgrowth
        lower upper duration r field i).2)
    let outcome := fun field => (data field,
      RootIndexed.subtreeStepFieldVector (roots field) (installed field))
    AEMeasurable outcome (P.restrict {field | τ field ≠ ⊤}) ∧
      (P.restrict {field | τ field ≠ ⊤}).map outcome =
        ((P.restrict {field | τ field ≠ ⊤}).map data).prod Q := by
  intro τ hτ trials installed P Q data roots outcome
  obtain ⟨hrawMeas, hraw⟩ := timePositionFreshField_jointLaw_on_finite lower hnodePath μ hnorm
    N initialPosition R growth hR hgrowth upper duration hupper hbounded hcapacity
    r positions hpositions
  let rightRoots := fun field (i : Fin lower) => ((Sum.inr r : Root ⊕ Root), (roots field i).2)
  change (P.restrict {field | τ field ≠ ⊤}).map
    (fun field => (data field, RootIndexed.subtreeStepFieldVector (rightRoots field) field)) =
    ((P.restrict {field | τ field ≠ ⊤}).map data).prod Q at hraw
  let rawOutcome := fun field => (data field, RootIndexed.subtreeStepFieldVector (rightRoots field) field)
  have hrawMeas' : Measurable rawOutcome := hrawMeas
  have hagree : outcome =ᵐ[P.restrict {field | τ field ≠ ⊤}] rawOutcome := by
    have hfinite : MeasurableSet {field | τ field ≠ ⊤} :=
      hτ.measurableSpace_le _ (hτ.measurable (measurableSet_singleton (⊤ : WithTop ℕ))).compl
    apply (ae_restrict_iff' hfinite).2
    have hroots := Lemmas.EndpointHorizon.endpointFreshRoots_eq_nSelectedBRW_ae μ hnorm
      N initialPosition R growth hR hgrowth lower upper duration hupper hbounded hcapacity r
    filter_upwards [hroots] with field hfield hfin
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    change (data field, RootIndexed.subtreeStepFieldVector (roots field) (installed field)) =
      (data field, RootIndexed.subtreeStepFieldVector (rightRoots field) field)
    congr 1
    funext i v
    have hdepth := Lemmas.EndpointHorizon.endpointFreshRoots_depth N initialPosition R growth
      hR hgrowth lower upper duration hupper r field n hn.symm i
    rw [hfield hfin i] at hdepth
    have hlen : n ≤ ((roots field i).2 ++ v).length := by
      rw [List.length_append]
      exact hdepth.ge.trans (Nat.le_add_right _ _)
    exact RootIndexed.stoppedRankInstalledTrajectoryField_apply_of_le_length
      N {r} initialPosition trials τ hτ field n hn.symm r _ hlen

  exact ⟨hrawMeas'.aemeasurable.congr hagree.symm, (Measure.map_congr hagree).trans hraw⟩

/-- Transfer any measurable continuation observable whose remaining horizon
is read from the successful endpoint time.  For a deterministic terminal
generation `m`, take `horizon t := m - t.untopD 0`; on the finite-endpoint
event this is exactly the remaining number of generations.  This is a
random-horizon law, obtained by including the stopped endpoint time in the
stopped data before applying the fresh-field product law. -/
theorem randomHorizonObservable_law_on_finite
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
      (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.time_isStoppingTime
        R growth hR hgrowth lower upper duration r).measurableSpace]
      positions)
    (future : (WithTop ℕ × (Fin lower → ℝ)) ×
      RootIndexed.StepField (Fin lower) α ℝ → Outcome)
    (hfuture : Measurable future) :
    let τ := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    (P.restrict {field | τ field ≠ ⊤}).map
      (fun field => future ((τ field, positions field),
        RootIndexed.selectedSubtreeStepFieldVector
          (fun field i => (Sum.inr r,
            (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.endpointNodesByRank N initialPosition
              R growth hR hgrowth lower upper duration r field i).2)) field)) =
    ((((P.restrict {field | τ field ≠ ⊤}).map
      (fun field => (τ field, positions field))).prod Q).map future) := by
  let τ := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.time R growth hR hgrowth
    lower upper duration r
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let endpointData := fun field => (τ field, positions field)
  let fresh := fun field =>
    RootIndexed.selectedSubtreeStepFieldVector
      (fun field i => (Sum.inr r,
        (ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.endpointNodesByRank N initialPosition
          R growth hR hgrowth lower upper duration r field i).2)) field
  have ⟨hpair, hjoint⟩ := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.timePositionFreshField_jointLaw_on_finite
    lower hnodePath μ hnorm N initialPosition R growth hR hgrowth upper duration
    hupper hbounded hcapacity r positions hpositions
  change (P.restrict {field | τ field ≠ ⊤}).map
      (future ∘ fun field => (endpointData field, fresh field)) =
    ((((P.restrict {field | τ field ≠ ⊤}).map endpointData).prod Q).map future)
  rw [← Measure.map_map hfuture hpair, hjoint]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion
