/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Compactness.Compact
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Measurability
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Existence

/-!
# Compact families of fixed-partition step paths

For a fixed finite time partition, the map from its finite vector of values to
the associated càdlàg step path is nonexpansive from the supremum metric to
the Skorokhod `J₁` metric. Consequently, restricting every value to a compact
subset of the state space gives a compact family of paths.

This finite-dimensional compactness result is one ingredient for a general
Skorokhod compactness criterion; it does not state that criterion. This
module also proves the necessary range-boundedness condition for compact path
families.
-/

@[expose] public section

open Filter

namespace Skorokhod

/-- The fixed-partition step-path map does not increase the extended distance.
The identity time change bounds `J₁` by uniform distance, and the latter is
bounded by the supremum distance between the finite vectors of values. -/
theorem OscillationPartition.edist_stepPath_le
    {E : Type*} [MetricSpace E] (partition : OscillationPartition)
    (v w : Fin (partition.size + 1) → E) :
    edist (partition.stepPath v) (partition.stepPath w) ≤ edist v w := by
  rw [edist_cadlagPath_eq_j1EDist]
  refine (j1EDist_le_uniformEDist _ _).trans ?_
  rw [uniformEDist_eq_edist, UniformFun.edist_def]
  apply iSup_le
  intro t
  by_cases ht : t = ⊤
  · subst t
    simp [OscillationPartition.stepPath]
    exact edist_le_pi_edist v w (Fin.last partition.size)
  · simp [OscillationPartition.stepPath, ht]
    exact edist_le_pi_edist v w (partition.index t).castSucc

/-- The fixed-partition step-path map is continuous for the `J₁` topology. -/
theorem OscillationPartition.continuous_stepPath
    {E : Type*} [MetricSpace E] (partition : OscillationPartition) :
    Continuous (fun v : Fin (partition.size + 1) → E => partition.stepPath v) := by
  rw [continuous_iff_continuousAt]
  intro v
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  have hsource : Tendsto (fun w : Fin (partition.size + 1) → E => edist w v)
      (nhds v) (nhds 0) :=
    tendsto_iff_edist_tendsto_0.1 continuousAt_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsource
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun w =>
      partition.edist_stepPath_le w v

/-- Step paths on a fixed finite partition whose values lie in a compact set
form a compact subset of Skorokhod space. -/
theorem OscillationPartition.isCompact_stepPath_image
    {E : Type*} [MetricSpace E] (partition : OscillationPartition)
    {K : Set E} (hK : IsCompact K) :
    IsCompact
      ((fun v : Fin (partition.size + 1) → E => partition.stepPath v) ''
        Set.pi Set.univ (fun _ : Fin (partition.size + 1) => K)) := by
  apply (isCompact_univ_pi fun _ => hK).image
  exact partition.continuous_stepPath

def zeroPath : CadlagPath unitInterval ℝ :=
  ⟨fun _ => 0, by simp⟩

private theorem TimeChange.act_zeroPath (change : TimeChange) :
    change.act zeroPath = zeroPath := by
  ext t
  simp [zeroPath, TimeChange.act_apply]

/-- The `J₁` distance from a path to zero is its uniform distance from zero.
Every time change preserves the range of a path, and the identity time change
has zero distortion. -/
theorem j1EDist_eq_uniformEDist_zero (path : CadlagPath unitInterval ℝ) :
    j1EDist path zeroPath = uniformEDist path zeroPath := by
  apply le_antisymm
  · calc
      j1EDist path zeroPath ≤ j1Cost path zeroPath TimeChange.refl :=
        j1EDist_le_cost path zeroPath TimeChange.refl
      _ = uniformEDist path zeroPath := by simp [j1Cost]
  · unfold j1EDist
    refine le_iInf fun change => ?_
    change uniformEDist path zeroPath ≤
      max (ENNReal.ofReal change.distortion)
        (uniformEDist (change.act path) zeroPath)
    rw [← change.act_zeroPath, uniformEDist_act]
    exact le_max_right _ _

/-- A compact family in Skorokhod space has uniformly bounded path ranges.
The range seminorm is exactly the `J₁` distance to the zero path. -/
theorem isBounded_pathRange_of_isCompact
    {K : Set (CadlagPath unitInterval ℝ)} (hK : IsCompact K) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ path ∈ K, ∀ t : unitInterval, |path t| ≤ bound := by
  by_cases hEmpty : K = ∅
  · refine ⟨0, le_rfl, ?_⟩
    simp [hEmpty]
  · have hNonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hBounded : Bornology.IsBounded K := hK.isBounded
    obtain ⟨bound, hClosedBall⟩ :=
      (Metric.isBounded_iff_subset_closedBall zeroPath).mp hBounded
    have hboundNonneg : 0 ≤ bound := by
      obtain ⟨path, hpath⟩ := hNonempty
      have hdist := Metric.mem_closedBall.mp (hClosedBall hpath)
      exact le_trans dist_nonneg hdist
    refine ⟨bound, hboundNonneg, ?_⟩
    intro path hpath t
    have hdistPath : dist path zeroPath ≤ bound :=
      Metric.mem_closedBall.mp (hClosedBall hpath)
    have hpoint : edist (path t) 0 ≤ edist path zeroPath := by
      calc
        edist (path t) 0 ≤ uniformEDist path zeroPath :=
          edist_apply_le_uniformEDist path zeroPath t
        _ = j1EDist path zeroPath :=
          (j1EDist_eq_uniformEDist_zero path).symm
        _ = edist path zeroPath := edist_cadlagPath_eq_j1EDist path zeroPath
    have hpoint' : dist (path t) 0 ≤ dist path zeroPath := by
      rw [edist_dist, edist_dist] at hpoint
      exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hpoint
    rw [Real.dist_eq] at hpoint'
    simpa only [sub_zero, abs_of_nonneg (abs_nonneg _)] using
      (le_trans hpoint' hdistPath)

/-- On a compact path family, a pathwise oscillation-partition bound can be
made uniform. This isolates the compactness step from the separate theorem
that constructs such a partition for each individual càdlàg path. -/
theorem exists_uniform_admitsOscillationPartition_of_isCompact
    {K : Set (CadlagPath unitInterval ℝ)} (hK : IsCompact K)
    (maximumOscillation : ℝ)
    (hpointwise : ∀ path ∈ K,
      ∃ minimumGap > 0,
        path ∈ admitsOscillationPartition minimumGap maximumOscillation) :
    ∃ minimumGap > 0, ∀ path ∈ K,
      path ∈ admitsOscillationPartition minimumGap maximumOscillation := by
  let Gap := {gap : ℝ // 0 < gap}
  let U : Gap → Set (CadlagPath unitInterval ℝ) := fun gap =>
    admitsOscillationPartition gap.1 maximumOscillation
  have hopen (gap : Gap) : IsOpen (U gap) :=
    isOpen_admitsOscillationPartition gap.1 maximumOscillation
  have hcover : K ⊆ ⋃ gap : Gap, U gap := by
    intro path hpath
    obtain ⟨gap, hgap, hadmit⟩ := hpointwise path hpath
    exact Set.mem_iUnion.mpr ⟨⟨gap, hgap⟩, hadmit⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover U hopen hcover
  have hfiniteGap : ∀ s : Finset Gap,
      ∃ gap : ℝ, 0 < gap ∧ ∀ i ∈ s, gap ≤ i.1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨gap, hgap, hgaple⟩ := ih
        refine ⟨min gap i.1, lt_min hgap i.2, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hgaple j hj)
  obtain ⟨minimumGap, hminimumGap, hgaple⟩ := hfiniteGap F
  refine ⟨minimumGap, hminimumGap, ?_⟩
  intro path hpath
  have hpathCover := hF hpath
  rcases Set.mem_iUnion.mp hpathCover with ⟨gap, hgap⟩
  rcases Set.mem_iUnion.mp hgap with ⟨hgapMem, hadmit⟩
  change path ∈ admitsOscillationPartition gap.1 maximumOscillation at hadmit
  obtain ⟨partition, hpartitionGap, bound, hbound, hosc⟩ := hadmit
  exact ⟨partition, lt_of_le_of_lt (hgaple gap hgapMem) hpartitionGap,
    bound, hbound, hosc⟩

/-- A compact family of càdlàg paths has a uniform positive partition gap at
every positive oscillation tolerance. The pathwise finite-partition theorem
supplies the hypothesis of the finite-subcover argument above. -/
theorem exists_uniform_admitsOscillationPartition_of_isCompact_of_pos
    {K : Set (CadlagPath unitInterval ℝ)} (hK : IsCompact K)
    {maximumOscillation : ℝ} (hmaximumOscillation : 0 < maximumOscillation) :
    ∃ minimumGap > 0, ∀ path ∈ K,
      path ∈ admitsOscillationPartition minimumGap maximumOscillation := by
  apply exists_uniform_admitsOscillationPartition_of_isCompact hK
  intro path _
  exact CadlagPath.exists_admits_oscillation_partition path hmaximumOscillation

end Skorokhod

end
