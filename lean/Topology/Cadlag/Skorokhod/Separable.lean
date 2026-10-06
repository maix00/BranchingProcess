/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Compactness.Approximation
public import Topology.Cadlag.Skorokhod.Compactness.StepPath
public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.Completeness
public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.TopologyComparison
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Separability of Skorokhod path space
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal Topology

namespace Skorokhod

private abbrev StepParameterSpace {E : Type*} [TopologicalSpace E]
    (n : ℕ) (gap : ℝ) :=
  {p : (Fin (n + 1) → unitInterval) × (Fin (n + 1) → E) //
    StepPathParameters gap Set.univ p}

set_option linter.style.haveILetI false in
private theorem stepParameterSpace_secondCountable {E : Type*} [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] (n : ℕ) (gap : ℝ) :
    SecondCountableTopology (StepParameterSpace (E := E) n gap) := by
  letI : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  infer_instance

private noncomputable def stepGap (k : ℕ) : ℝ := ((k : ℝ) + 1)⁻¹

private theorem stepGap_pos (k : ℕ) : 0 < stepGap k := by
  dsimp [stepGap]
  positivity

set_option linter.style.haveILetI false in
private noncomputable def denseStepParameters {E : Type*} [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] (n : ℕ) (k : ℕ) :
    Set (StepParameterSpace (E := E) n (stepGap k)) := by
  letI : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  letI : SecondCountableTopology (StepParameterSpace (E := E) n (stepGap k)) :=
    stepParameterSpace_secondCountable n (stepGap k)
  letI : TopologicalSpace.SeparableSpace (StepParameterSpace (E := E) n (stepGap k)) :=
    inferInstance
  exact Classical.choose <| TopologicalSpace.exists_countable_dense _

set_option linter.style.haveILetI false in
private theorem countable_denseStepParameters {E : Type*} [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] (n : ℕ) (k : ℕ) :
    (denseStepParameters (E := E) n k).Countable := by
  letI : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  letI : SecondCountableTopology (StepParameterSpace (E := E) n (stepGap k)) :=
    stepParameterSpace_secondCountable n (stepGap k)
  letI : TopologicalSpace.SeparableSpace (StepParameterSpace (E := E) n (stepGap k)) :=
    inferInstance
  exact (Classical.choose_spec <| TopologicalSpace.exists_countable_dense
    (StepParameterSpace (E := E) n (stepGap k))).1

set_option linter.style.haveILetI false in
private theorem dense_denseStepParameters {E : Type*} [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] (n : ℕ) (k : ℕ) :
    Dense (denseStepParameters (E := E) n k) := by
  letI : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  letI : SecondCountableTopology (StepParameterSpace (E := E) n (stepGap k)) :=
    stepParameterSpace_secondCountable n (stepGap k)
  letI : TopologicalSpace.SeparableSpace (StepParameterSpace (E := E) n (stepGap k)) :=
    inferInstance
  exact (Classical.choose_spec <| TopologicalSpace.exists_countable_dense
    (StepParameterSpace (E := E) n (stepGap k))).2

private noncomputable def denseStepPathFamily {E : Type*} [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] : Set (CadlagPath unitInterval E) :=
  ⋃ n : {n : ℕ // 0 < n}, ⋃ k : ℕ,
    (fun p : StepParameterSpace (E := E) n.1 (stepGap k) =>
      stepPathOfParameters n.2 Set.univ (stepGap_pos k) p) '' denseStepParameters n.1 k

private theorem countable_denseStepPathFamily {E : Type*} [PseudoMetricSpace E]
    [TopologicalSpace.SeparableSpace E] : denseStepPathFamily (E := E).Countable := by
  unfold denseStepPathFamily
  refine Set.countable_iUnion fun n => Set.countable_iUnion fun k => ?_
  exact (countable_denseStepParameters (E := E) n.1 k).image _

private theorem exists_stepGap_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, stepGap k < δ := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hn : ∀ᶠ n : ℕ in atTop, b ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (Ici_mem_atTop b)
    filter_upwards [hn] with n hn
    exact hn.trans (by norm_num)
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hev : ∀ᶠ k : ℕ in atTop, stepGap k < δ := by
    filter_upwards [hinv.eventually (Iio_mem_nhds hδ)] with k hk
    simpa [stepGap] using hk
  obtain ⟨k, hk⟩ := (eventually_atTop.1 hev)
  exact ⟨k, hk k le_rfl⟩

private theorem dense_denseStepPathFamily {E : Type*} [MetricSpace E]
    [TopologicalSpace.SeparableSpace E] : Dense (denseStepPathFamily (E := E)) := by
  rw [Metric.dense_iff]
  intro path ε hε
  let radius := ε / 3
  have hradius : 0 < radius := by dsimp [radius]; positivity
  obtain ⟨partition, bound, hbound, hosc⟩ :=
    IsCadlag.exists_oscillation_partition path.isCadlag_toFun hradius
  have hbound_nonneg : 0 ≤ bound := by
    have h := hosc ⊥ ⊥ (ne_of_lt bot_lt_top) (ne_of_lt bot_lt_top) rfl
    simpa [OscillationBoundedOnPartition, dist_self] using h
  obtain ⟨k, hk⟩ := exists_stepGap_lt partition.mesh_pos
  let n : {n : ℕ // 0 < n} := ⟨partition.size, partition.size_pos⟩
  let values : Fin (partition.size + 1) → E :=
    Fin.lastCases (path ⊤) (fun i => path (partition.points i.castSucc))
  have hpoints : IsSeparatedPartitionPoints (stepGap k) partition.points := by
    refine ⟨partition.first, partition.last, ?_⟩
    intro i
    refine ⟨le_of_lt (partition.strictMono_points i.castSucc_lt_succ), ?_⟩
    exact (le_of_lt hk).trans (partition.gap_lower i)
  have hvalues : values ∈ Set.pi Set.univ (fun _ : Fin (partition.size + 1) => Set.univ) := by
    simp
  let p : StepParameterSpace (E := E) partition.size (stepGap k) :=
    ⟨(partition.points, values), ⟨hpoints, hvalues⟩⟩
  let sourcePath := stepPathOfParameters partition.size_pos Set.univ (stepGap_pos k) p
  have hsourcePath : sourcePath = partition.stepApproximation path := by
    dsimp [sourcePath, stepPathOfParameters, p]
    exact (partition.stepApproximation_eq_ofPoints_stepPath path).symm
  obtain ⟨q, hq, hqball⟩ :=
    (dense_denseStepParameters (E := E) partition.size k).inter_open_nonempty
      (Metric.ball p radius) Metric.isOpen_ball ⟨p, Metric.mem_ball_self hradius⟩
  have hqdist : dist p q < radius := by
    simpa [dist_comm] using (Metric.mem_ball.mp hq)
  let closePath := stepPathOfParameters partition.size_pos Set.univ (stepGap_pos k) q
  have hclose : dist sourcePath closePath < radius := by
    have hdistED : edist sourcePath closePath ≤ edist p q := by
      rw [edist_cadlagPath_eq_j1EDist]
      exact j1EDist_stepPathOfParameters_le partition.size_pos Set.univ
        (stepGap_pos k) p q
    have hdist : ENNReal.ofReal (dist sourcePath closePath) ≤
        ENNReal.ofReal (dist p q) := by
      simpa only [edist_dist] using hdistED
    exact ((ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hdist).trans_lt hqdist
  have hsourceApprox : dist path sourcePath ≤ bound := by
    rw [hsourcePath, dist_edist, edist_cadlagPath_eq_j1EDist]
    have hj1 := partition.j1EDist_stepApproximation_le path hosc
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hj1
      |>.trans_eq (ENNReal.toReal_ofReal hbound_nonneg)
  have hcloseMem : closePath ∈ denseStepPathFamily (E := E) := by
    rw [denseStepPathFamily]
    refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨k, ?_⟩⟩
    exact ⟨q, hqball, rfl⟩
  refine ⟨closePath, ?_, hcloseMem⟩
  apply Metric.mem_ball.mpr
  calc
    dist closePath path = dist path closePath := dist_comm _ _
    _ ≤ dist path sourcePath + dist sourcePath closePath :=
      dist_triangle _ _ _
    _ < ε := by dsimp [radius] at *; linarith

/-- The Skorokhod `J₁` space of càdlàg paths is separable when the state space
is separable. -/
noncomputable instance instSeparableSpaceCadlagPath {E : Type*} [MetricSpace E]
    [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (CadlagPath unitInterval E) := by
  exact ⟨⟨denseStepPathFamily (E := E),
    countable_denseStepPathFamily, dense_denseStepPathFamily⟩⟩

set_option linter.style.haveILetI false in
/-- The Skorokhod `J₁` space of càdlàg paths is completely metrizable when the
state space is complete. -/
noncomputable instance instIsCompletelyMetrizableSpaceCadlagPath
    {E : Type*} [MetricSpace E] [CompleteSpace E] :
    TopologicalSpace.IsCompletelyMetrizableSpace (CadlagPath unitInterval E) := by
  let e := billingsleyPathHomeomorph (E := E)
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace (BillingsleyPath E) := inferInstance
  exact Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace e.isClosedEmbedding

end Skorokhod

end
