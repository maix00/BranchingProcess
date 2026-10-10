/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling

/-!
# Endpoint-dependent finite restart horizons

The fixed-horizon endpoint theorem can be pushed through observables whose
horizon is a measurable function of the successful endpoint time.  The
endpoint time is the first completion of the pre-sampled candidate family;
split marks are exposed at their observable completion generations.  This
file does not identify the candidate-union source with the retrospective
restart frontier, and it makes no stopping-time claim about a raw split label.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris

private theorem measurable_subtreeStepFieldVector_of_measurable_roots
    {Root κ α X : Type*} [MeasurableSpace X]
    [MeasurableSpace κ] [MeasurableSpace Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable κ] [MeasurableSingletonClass Root]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    (roots : RootIndexed.StepField Root α X →
      κ → RootIndexed.TreeNode Root α)
    (hroots : Measurable roots)
    (hcount : (Set.range roots).Countable) :
    Measurable (fun ω => RootIndexed.subtreeStepFieldVector (roots ω) ω) := by
  classical
  let S : Set (κ → RootIndexed.TreeNode Root α) := Set.range roots
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  intro B hB
  have hpre :
      (fun ω => RootIndexed.subtreeStepFieldVector (roots ω) ω) ⁻¹' B =
        ⋃ q : S, {ω | roots ω = q.1} ∩
          RootIndexed.subtreeStepFieldVector q.1 ⁻¹' B := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⟨roots ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨q, hq, h⟩
      simpa [hq] using h
  rw [hpre]
  exact MeasurableSet.iUnion fun q =>
    (hroots (measurableSet_singleton q.1)).inter
      ((RootIndexed.subtreeStepFieldVector_measurable q.1) hB)

/-- The successful endpoint time, endpoint positions, and their actual
rank-installed target descendant field have the joint law obtained by
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
    let targetRoots := fun field i =>
      (Sum.inr r, (selectedReserveSpineRestartEndpointRankVector N
        initialPosition R growth hR hgrowth lower upper duration r field i).2)
    let fresh := fun field =>
      RootIndexed.selectedSubtreeStepFieldVector targetRoots field
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
  let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r
  let targetRoots : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower →
      (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α := fun field i =>
    (Sum.inr r, (target field i).2)
  let fresh := fun field =>
    RootIndexed.selectedSubtreeStepFieldVector targetRoots field
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
  have htarget : Measurable[hτmeas.measurableSpace] target := by
    simpa [target, hτmeas] using
      selectedReserveSpineRestartEndpointRankVector_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hrootsStop : Measurable[hτmeas.measurableSpace] targetRoots := by
    letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
      hτmeas.measurableSpace
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable[hτmeas.measurableSpace]
        (fun field => target field i) :=
      (measurable_pi_apply i).comp htarget
    exact measurable_const.prodMk (hnodePath.comp hi)
  have hroots : Measurable targetRoots := hrootsStop.mono hle le_rfl
  have hcount : (Set.range targetRoots).Countable := by
    let encode : (Fin lower → RootIndexed.TreeNode Root α) →
        Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α :=
      fun v i => (Sum.inr r, (v i).2)
    have hsubset : Set.range targetRoots ⊆ Set.range encode := by
      rintro q ⟨field, rfl⟩
      exact ⟨target field, rfl⟩
    exact (Set.countable_range encode).mono hsubset
  have hfresh : Measurable fresh := by
    change Measurable (fun field =>
      RootIndexed.subtreeStepFieldVector (targetRoots field) field)
    exact measurable_subtreeStepFieldVector_of_measurable_roots
      targetRoots hroots hcount
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
    have hfactor := selectedReserveSpineRestartEndpointTargetFreshField_factorization_on_finite
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
  simpa [τ, P, Q, E, endpointData, data, target, targetRoots, fresh] using hjoint

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
            (selectedReserveSpineRestartEndpointRankVector N initialPosition
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
        (selectedReserveSpineRestartEndpointRankVector N initialPosition
          R growth hR hgrowth lower upper duration r field i).2)) field
  have ⟨hpair, hjoint⟩ := selectedReserveSpineRestartEndpointTimePositionFreshField_jointLaw_on_finite
    lower hnodePath μ hnorm N initialPosition R growth hR hgrowth upper duration
    hupper hbounded hcapacity r positions hpositions
  change (P.restrict {field | τ field ≠ ⊤}).map
      (future ∘ fun field => (endpointData field, fresh field)) =
    ((((P.restrict {field | τ field ≠ ⊤}).map endpointData).prod Q).map future)
  rw [← Measure.map_map hfuture hpair, hjoint]

end ProbabilityTheory.BranchingRandomWalk
