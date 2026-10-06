/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Compactness.Compact
public import Topology.Cadlag.Skorokhod.TimeChange.FinitePartition.Homeomorph

/-!
# Compact families of step paths with moving partitions

Finite step paths depend continuously in `J₁` on their partition points and
cell values when the partition gaps have a uniform positive lower bound.
-/

@[expose] public section

namespace Skorokhod

open Filter

/-- The uniform distance between two step paths on a fixed partition is
bounded by the supremum distance between their finite vectors of values. -/
theorem OscillationPartition.uniformEDist_stepPath_le
    {E : Type*} [EMetricSpace E] (partition : OscillationPartition)
    (v w : Fin (partition.size + 1) → E) :
    uniformEDist (partition.stepPath v) (partition.stepPath w) ≤ edist v w := by
  rw [uniformEDist_eq_edist, UniformFun.edist_def]
  apply iSup_le
  intro t
  by_cases ht : t = ⊤
  · subst t
    simp [OscillationPartition.stepPath]
    exact edist_le_pi_edist v w (Fin.last partition.size)
  · simp [OscillationPartition.stepPath, ht]
    exact edist_le_pi_edist v w (partition.index t).castSucc

/-- A finite vector of time points with fixed endpoints, nondecreasing
adjacent points, and a lower bound on each adjacent gap. -/
def IsSeparatedPartitionPoints {n : ℕ} (gap : ℝ)
    (points : Fin (n + 1) → unitInterval) : Prop :=
  points ⟨0, by omega⟩ = ⊥ ∧ points ⟨n, by omega⟩ = ⊤ ∧
    ∀ i : Fin n,
      points i.castSucc ≤ points i.succ ∧
        gap ≤ dist (points i.castSucc) (points i.succ)

/-- Positive gaps and nondecreasing adjacent points imply strict ordering. -/
theorem IsSeparatedPartitionPoints.strictMono {n : ℕ} {gap : ℝ}
    (hgap : 0 < gap) {points : Fin (n + 1) → unitInterval}
    (hpoints : IsSeparatedPartitionPoints gap points) : StrictMono points := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  have hdist : 0 < dist (points i.castSucc) (points i.succ) :=
    hgap.trans_le (hpoints.2.2 i).2
  exact lt_of_le_of_ne (hpoints.2.2 i).1 (dist_pos.mp hdist)

/-- The set of point vectors with fixed endpoints and lower gap bound is
closed in the finite product of unit intervals. -/
theorem isClosed_setOf_isSeparatedPartitionPoints {n : ℕ} (gap : ℝ) :
    IsClosed {points : Fin (n + 1) → unitInterval | IsSeparatedPartitionPoints gap points} := by
  have hfirst : IsClosed {points : Fin (n + 1) → unitInterval |
      points ⟨0, by omega⟩ = ⊥} :=
    isClosed_eq (continuous_apply _) continuous_const
  have hlast : IsClosed {points : Fin (n + 1) → unitInterval |
      points ⟨n, by omega⟩ = ⊤} :=
    isClosed_eq (continuous_apply _) continuous_const
  have hadjacent (i : Fin n) : IsClosed {points : Fin (n + 1) → unitInterval |
      points i.castSucc ≤ points i.succ ∧
        gap ≤ dist (points i.castSucc) (points i.succ)} := by
    have hmono : IsClosed {points : Fin (n + 1) → unitInterval |
        points i.castSucc ≤ points i.succ} :=
      isClosed_le (continuous_apply _) (continuous_apply _)
    have hgap : IsClosed {points : Fin (n + 1) → unitInterval |
        gap ≤ dist (points i.castSucc) (points i.succ)} :=
      isClosed_le continuous_const <|
        continuous_dist.comp₂ (continuous_apply _) (continuous_apply _)
    exact hmono.inter hgap
  have hset :
      {points : Fin (n + 1) → unitInterval | IsSeparatedPartitionPoints gap points} =
        {points : Fin (n + 1) → unitInterval | points ⟨0, by omega⟩ = ⊥} ∩
          ({points : Fin (n + 1) → unitInterval | points ⟨n, by omega⟩ = ⊤} ∩
            ⋂ i : Fin n, {points : Fin (n + 1) → unitInterval |
              points i.castSucc ≤ points i.succ ∧
                gap ≤ dist (points i.castSucc) (points i.succ)}) := by
    ext points
    simp [IsSeparatedPartitionPoints]
  rw [hset]
  exact hfirst.inter (hlast.inter (isClosed_iInter fun i => hadjacent i))

/-- Point vectors with a positive uniform gap form a compact parameter space. -/
theorem isCompact_setOf_isSeparatedPartitionPoints {n : ℕ} (gap : ℝ) :
    IsCompact {points : Fin (n + 1) → unitInterval |
      IsSeparatedPartitionPoints gap points} := by
  have hcompact : IsCompact (Set.univ : Set (Fin (n + 1) → unitInterval)) := by
    simpa using isCompact_univ_pi (fun _ : Fin (n + 1) =>
      (isCompact_univ : IsCompact (Set.univ : Set unitInterval)))
  apply IsCompact.of_isClosed_subset hcompact
    (isClosed_setOf_isSeparatedPartitionPoints gap)
  exact Set.subset_univ _

/-- Moving the partition points and the step values by small amounts gives a
small `J₁` distance. The partition motion is absorbed by a piecewise-affine
time change; the remaining error is the value-vector distance. -/
theorem j1EDist_stepPath_le_ofMatchingPartitions_value {n : ℕ}
    {E : Type*} [MetricSpace E]
    (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target)
    (value₁ value₂ : Fin (n + 1) → E) (ε : ℝ)
    (hpoints : ∀ j, dist (target j) (source j) ≤ ε) :
    j1EDist ((TimeChange.FinitePartition.ofPoints hn source hsourceFirst hsourceLast
        hsourceStrict).stepPath value₁)
      ((TimeChange.FinitePartition.ofPoints hn target htargetFirst htargetLast
        htargetStrict).stepPath value₂) ≤
      max (ENNReal.ofReal ε) (edist value₁ value₂) := by
  let sourcePartition := TimeChange.FinitePartition.ofPoints hn source hsourceFirst
    hsourceLast hsourceStrict
  let targetPartition := TimeChange.FinitePartition.ofPoints hn target htargetFirst
    htargetLast htargetStrict
  let change := TimeChange.FinitePartition.ofMatchingPartitions hn target source
    htargetFirst htargetLast htargetStrict hsourceFirst hsourceLast hsourceStrict
  have hdistortion : change.distortion ≤ ε :=
    TimeChange.FinitePartition.ofMatchingPartitions_distortion_le hn target source
      htargetFirst htargetLast htargetStrict hsourceFirst hsourceLast hsourceStrict ε hpoints
  have hact : change.act (sourcePartition.stepPath value₁) =
      targetPartition.stepPath value₁ :=
    TimeChange.FinitePartition.act_ofMatchingPartitions_stepPath hn source target
      hsourceFirst hsourceLast hsourceStrict htargetFirst htargetLast htargetStrict value₁
  calc
    j1EDist (sourcePartition.stepPath value₁) (targetPartition.stepPath value₂) ≤
        j1Cost (sourcePartition.stepPath value₁) (targetPartition.stepPath value₂) change :=
      j1EDist_le_cost _ _ _
    _ = max (ENNReal.ofReal change.distortion)
        (uniformEDist (targetPartition.stepPath value₁)
          (targetPartition.stepPath value₂)) := by
      simp [j1Cost, hact]
    _ ≤ max (ENNReal.ofReal ε) (edist value₁ value₂) := by
      apply max_le
      · exact (ENNReal.ofReal_le_ofReal hdistortion).trans (le_max_left _ _)
      · exact (OscillationPartition.uniformEDist_stepPath_le targetPartition value₁ value₂).trans
          (le_max_right _ _)

/-- Parameters for a step path whose time knots have a fixed positive lower
gap and whose values lie in a common compact-range candidate. -/
def StepPathParameters {E : Type*} [TopologicalSpace E] {n : ℕ} (gap : ℝ)
    (range : Set E)
    (p : (Fin (n + 1) → unitInterval) × (Fin (n + 1) → E)) : Prop :=
  IsSeparatedPartitionPoints gap p.1 ∧
    p.2 ∈ Set.pi Set.univ (fun _ : Fin (n + 1) => range)

/-- The parameter set for moving-partition step paths is compact whenever the
common range set is compact. -/
theorem isCompact_setOf_stepPathParameters {E : Type*} [TopologicalSpace E]
    {n : ℕ} (gap : ℝ) (range : Set E) (hrange : IsCompact range) :
    IsCompact {p : (Fin (n + 1) → unitInterval) × (Fin (n + 1) → E) |
      StepPathParameters gap range p} := by
  have htimes : IsCompact {points : Fin (n + 1) → unitInterval |
      IsSeparatedPartitionPoints gap points} :=
    isCompact_setOf_isSeparatedPartitionPoints gap
  have hvalues : IsCompact (Set.pi Set.univ (fun _ : Fin (n + 1) => range)) :=
    isCompact_univ_pi fun _ => hrange
  have hprod := htimes.prod hvalues
  have hset : {p : (Fin (n + 1) → unitInterval) × (Fin (n + 1) → E) |
      StepPathParameters gap range p} =
      {points : Fin (n + 1) → unitInterval |
        IsSeparatedPartitionPoints gap points} ×ˢ
        Set.pi Set.univ (fun _ : Fin (n + 1) => range) := by
    ext p
    simp [StepPathParameters, Set.mem_prod]
  rw [hset]
  exact hprod

/-- Turn separated partition points and their values into a càdlàg step path. -/
noncomputable def stepPathOfParameters {n : ℕ} (hn : 0 < n)
    {E : Type*} [TopologicalSpace E] {gap : ℝ} (range : Set E) (hgap : 0 < gap)
    (p : {q : (Fin (n + 1) → unitInterval) × (Fin (n + 1) → E) //
      StepPathParameters gap range q}) : CadlagPath unitInterval E := by
  let hp := p.property.1
  exact (TimeChange.FinitePartition.ofPoints hn p.val.1 hp.1 hp.2.1
    (hp.strictMono hgap)).stepPath p.val.2

/-- The step-path map on the compact moving-partition parameter set is
nonexpansive for the product metric and the `J₁` metric. -/
theorem j1EDist_stepPathOfParameters_le {n : ℕ} (hn : 0 < n)
    {E : Type*} [MetricSpace E] {gap : ℝ} (range : Set E) (hgap : 0 < gap)
    (p q : {r : (Fin (n + 1) → unitInterval) × (Fin (n + 1) → E) //
      StepPathParameters gap range r}) :
    j1EDist (stepPathOfParameters hn range hgap p) (stepPathOfParameters hn range hgap q) ≤
      edist p q := by
  let hp := p.property.1
  let hq := q.property.1
  have hvalues : edist p.val.2 q.val.2 ≤ edist p.val q.val := by
    calc
      edist p.val.2 q.val.2 = ENNReal.ofReal (dist p.val.2 q.val.2) := edist_dist _ _
      _ ≤ ENNReal.ofReal (dist p.val q.val) :=
        ENNReal.ofReal_le_ofReal (by
          rw [Prod.dist_eq]
          exact le_max_right _ _)
      _ = edist p.val q.val := (edist_dist _ _).symm
  have htimes' : edist q.val.1 p.val.1 ≤ edist p.val q.val := by
    calc
      edist q.val.1 p.val.1 ≤ edist q.val p.val := by
        rw [Prod.edist_eq]
        exact le_max_left _ _
      _ = edist p.val q.val := edist_comm _ _
  have htimeReal : ENNReal.ofReal (dist q.val.1 p.val.1) ≤ edist p.val q.val := by
    calc
      ENNReal.ofReal (dist q.val.1 p.val.1) = edist q.val.1 p.val.1 := (edist_dist _ _).symm
      _ ≤ edist p.val q.val := htimes'
  change j1EDist
      ((TimeChange.FinitePartition.ofPoints hn p.val.1 hp.1 hp.2.1
        (hp.strictMono hgap)).stepPath p.val.2)
      ((TimeChange.FinitePartition.ofPoints hn q.val.1 hq.1 hq.2.1
        (hq.strictMono hgap)).stepPath q.val.2) ≤ edist p q
  calc
    _ ≤ max (ENNReal.ofReal (dist q.val.1 p.val.1)) (edist p.val.2 q.val.2) := by
      exact j1EDist_stepPath_le_ofMatchingPartitions_value hn p.val.1 q.val.1
        hp.1 hp.2.1 (hp.strictMono hgap) hq.1 hq.2.1 (hq.strictMono hgap)
        p.val.2 q.val.2 (dist q.val.1 p.val.1) (fun i =>
          dist_le_pi_dist q.val.1 p.val.1 i)
    _ ≤ edist p.val q.val := max_le htimeReal hvalues

/-- The moving-partition step-path map is continuous. -/
theorem continuous_stepPathOfParameters {n : ℕ} (hn : 0 < n)
    {E : Type*} [MetricSpace E] {gap : ℝ} (range : Set E) (hgap : 0 < gap) :
    Continuous (stepPathOfParameters hn range hgap) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  have hsource : Tendsto (fun q => edist q p) (nhds p) (nhds 0) :=
    tendsto_iff_edist_tendsto_0.1 continuousAt_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsource
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun q => by
      rw [edist_cadlagPath_eq_j1EDist]
      exact j1EDist_stepPathOfParameters_le hn range hgap q p

/-- The set of step paths with a fixed number of cells, a positive minimum
partition gap, and bounded values is compact in `J₁`. -/
theorem isCompact_stepPathOfParameters_image {n : ℕ} (hn : 0 < n)
    {E : Type*} [MetricSpace E] {gap : ℝ} (range : Set E) (hrange : IsCompact range)
    (hgap : 0 < gap) :
    IsCompact (Set.range (stepPathOfParameters (E := E) hn range hgap)) := by
  have hcompact : CompactSpace {p : (Fin (n + 1) → unitInterval) × (Fin (n + 1) → E) //
      StepPathParameters gap range p} :=
    isCompact_iff_compactSpace.mp (isCompact_setOf_stepPathParameters gap range hrange)
  exact @isCompact_range _ _ inferInstance inferInstance hcompact _
    (continuous_stepPathOfParameters hn range hgap)

end Skorokhod

end
