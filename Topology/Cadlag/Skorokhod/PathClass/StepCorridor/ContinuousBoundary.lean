/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.TerminalLeft
public import Topology.Cadlag.Skorokhod.ContinuousMap
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Basic
public import Order.Interval.UniformGrid
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Continuous path corridors

This file records the deterministic target associated to two continuous
boundaries, and the compactness consequence that a strictly separated pair
has a continuous center with a uniform positive margin. The time interval is
the unit interval because the source path space `D₀` is defined there.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Skorokhod.PathClass.StepCorridor

/-- Convert the usual `Fin (blocks + 1)` index to the index type carried by
the grid object. -/
noncomputable def uniformGridIndex (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin (blocks + 1)) : (UniformGrid.unit (K := ℝ) blocks hblocks).Index :=
  Fin.cast (by simp [UniformGrid.unit]) i

/-- The grid index immediately after a cell index. -/
noncomputable def uniformGridSuccessorIndex (blocks : ℕ) (hblocks : 0 < blocks)
    (j : Fin blocks) : (UniformGrid.unit (K := ℝ) blocks hblocks).Index :=
  ⟨j.val + 1, by change j.val + 1 < blocks + 1; omega⟩

/-- A uniform-grid coordinate represented as a point of the unit interval. -/
noncomputable def uniformGridTime (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin (blocks + 1)) : unitInterval :=
  ⟨(UniformGrid.unit (K := ℝ) blocks hblocks).point
      (uniformGridIndex blocks hblocks i),
    by simpa [UniformGrid.unit] using
      UniformGrid.point_mem_Icc (UniformGrid.unit (K := ℝ) blocks hblocks)
        (uniformGridIndex blocks hblocks i)⟩

/-- The uniform-grid knot immediately after the initial endpoint. -/
noncomputable def uniformGridSuccessorTime (blocks : ℕ) (hblocks : 0 < blocks)
    (j : Fin blocks) : unitInterval :=
  ⟨(UniformGrid.unit (K := ℝ) blocks hblocks).point
      (uniformGridSuccessorIndex blocks hblocks j),
    by simpa [UniformGrid.unit] using
      UniformGrid.point_mem_Icc (UniformGrid.unit (K := ℝ) blocks hblocks)
        (uniformGridSuccessorIndex blocks hblocks j)⟩

/-- The internal knots of the standard uniform partition with `blocks`
subintervals. The terminal endpoint is included, while the initial endpoint
is omitted as required by `StepBoundary`. -/
noncomputable def uniformCorridorKnots (blocks : ℕ) (hblocks : 0 < blocks) : Finset unitInterval :=
  Finset.univ.image (uniformGridSuccessorTime blocks hblocks)

theorem uniformCorridorKnots_card (blocks : ℕ) (hblocks : 0 < blocks) :
    (uniformCorridorKnots blocks hblocks).card = blocks := by
  classical
  unfold uniformCorridorKnots
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have hstrict : StrictMono
        ((UniformGrid.unit (K := ℝ) blocks hblocks).point) :=
      UniformGrid.strictMono_point (by norm_num [UniformGrid.unit])
    have htime := congrArg Subtype.val hij
    have heq : (UniformGrid.unit (K := ℝ) blocks hblocks).point
          (uniformGridSuccessorIndex blocks hblocks i) =
        (UniformGrid.unit (K := ℝ) blocks hblocks).point
          (uniformGridSuccessorIndex blocks hblocks j) := by
      simpa [uniformGridSuccessorTime, uniformGridTime] using htime
    have hindex := hstrict.injective heq
    apply Fin.ext
    have hval := congrArg Fin.val hindex
    change i.val + 1 = j.val + 1 at hval
    omega

/-- Uniform-grid knots never contain the initial endpoint. -/
theorem bot_not_mem_uniformCorridorKnots (blocks : ℕ) (hblocks : 0 < blocks) :
    (⊥ : unitInterval) ∉ uniformCorridorKnots blocks hblocks := by
  classical
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨j, -, hj⟩
  have hstrict : StrictMono
      ((UniformGrid.unit (K := ℝ) blocks hblocks).point) :=
    UniformGrid.strictMono_point (by norm_num [UniformGrid.unit])
  have hidx : (0 : (UniformGrid.unit (K := ℝ) blocks hblocks).Index) <
      uniformGridSuccessorIndex blocks hblocks j :=
    Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
  have hlt := hstrict hidx
  have hzero : uniformGridTime blocks hblocks 0 = ⊥ := by
    apply Subtype.ext
    simp [uniformGridTime, uniformGridIndex, UniformGrid.unit, UniformGrid.point]
  have hpos : (⊥ : unitInterval) < uniformGridSuccessorTime blocks hblocks j := by
    apply Subtype.mk_lt_mk.mpr
    have hleft : (UniformGrid.unit (K := ℝ) blocks hblocks).point 0 = 0 := by
      simp [UniformGrid.unit, UniformGrid.point]
    rw [← hleft]
    exact hlt
  have : (⊥ : unitInterval) = uniformGridSuccessorTime blocks hblocks j := hj.symm
  exact (ne_of_lt hpos) this

/-- The step boundary obtained by sampling a continuous function at the left
end of each uniform cell (and at the terminal endpoint). -/
noncomputable def uniformGridStepBoundary (blocks : ℕ) (hblocks : 0 < blocks)
    (f : C(unitInterval, ℝ)) (offset : ℝ) : StepBoundary := by
  let knots := uniformCorridorKnots blocks hblocks
  have hcard : knots.card = blocks := by
    exact uniformCorridorKnots_card blocks hblocks
  refine ⟨knots, ?_, ?_⟩
  · exact bot_not_mem_uniformCorridorKnots blocks hblocks
  · intro i
    let gridI : Fin (blocks + 1) := Fin.cast (by rw [hcard]) i
    exact ((f (uniformGridTime blocks hblocks gridI) + offset : ℝ) : EReal)

/-- Evaluation of a sampled boundary is the continuous function at the grid
index recorded by the boundary's level count. -/
theorem uniformGridStepBoundary_eval (blocks : ℕ) (hblocks : 0 < blocks)
    (f : C(unitInterval, ℝ)) (offset : ℝ) (t : unitInterval) :
    let b := uniformGridStepBoundary blocks hblocks f offset
    b.eval t = ((f (uniformGridTime blocks hblocks
      (Fin.cast (by rw [show b.knots.card = blocks by
        simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks])
        (b.levelIndex t))) + offset : ℝ) : EReal) := by
  let b := uniformGridStepBoundary blocks hblocks f offset
  have hcard : b.knots.card = blocks := by
    simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks
  let i : Fin (blocks + 1) := Fin.cast (by rw [hcard]) (b.levelIndex t)
  change b.levels (b.levelIndex t) = ((f (uniformGridTime blocks hblocks i) + offset : ℝ) : EReal)
  rfl

/-- Explicit-index form of `uniformGridStepBoundary_eval`, convenient when
comparing several sampled boundaries built on the same mesh. -/
theorem uniformGridStepBoundary_eval_eq_sample (blocks : ℕ) (hblocks : 0 < blocks)
    (f : C(unitInterval, ℝ)) (offset : ℝ) (t : unitInterval) :
    let b := uniformGridStepBoundary blocks hblocks f offset
    let i : Fin (blocks + 1) := Fin.cast
      (by simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks)
      (b.levelIndex t)
    b.eval t = ((f (uniformGridTime blocks hblocks i) + offset : ℝ) : EReal) := by
  exact uniformGridStepBoundary_eval blocks hblocks f offset t

private theorem card_filter_antitone_index {n : ℕ} (P : Fin n → Prop)
    [DecidablePred P] (hP : ∀ i j, i ≤ j → P j → P i) (k : ℕ)
    (hk : (Finset.univ.filter P).card = k) :
    ∀ i : Fin n, (i.val < k → P i) ∧ (k ≤ i.val → ¬ P i) := by
  intro i
  constructor
  · intro hik
    by_contra hi
    have hsubset : Finset.univ.filter P ⊆ Finset.univ.filter (fun j : Fin n => j < i) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra hji
      exact hi (hP i j (Fin.mk_le_mk.mpr (le_of_not_gt hji)) hj)
    have hcard := Finset.card_le_card hsubset
    have hIio : (Finset.univ.filter (fun j : Fin n => j < i)).card = i.val := by
      have heq : Finset.univ.filter (fun j : Fin n => j < i) = Finset.Iio i := by
        ext j
        simp [Finset.mem_Iio]
      rw [heq, Fin.card_Iio]
    rw [hk, hIio] at hcard
    omega
  · intro hik
    by_contra hi
    have hsubset : Finset.univ.filter (fun j : Fin n => j ≤ i) ⊆ Finset.univ.filter P := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hP j i (Fin.mk_le_mk.mpr hj) hi
    have hcard := Finset.card_le_card hsubset
    have hIic : (Finset.univ.filter (fun j : Fin n => j ≤ i)).card = i.val + 1 := by
      have heq : Finset.univ.filter (fun j : Fin n => j ≤ i) = Finset.Iic i := by
        ext j
        simp [Finset.mem_Iic]
      rw [heq, Fin.card_Iic]
    rw [hIic, hk] at hcard
    omega

private theorem uniformGridStepBoundary_levelIndex_card (blocks : ℕ)
    (hblocks : 0 < blocks) (f : C(unitInterval, ℝ)) (offset : ℝ)
    (t : unitInterval) :
    ((uniformGridStepBoundary blocks hblocks f offset).levelIndex t).val =
      (Finset.univ.filter fun j : Fin blocks =>
        uniformGridSuccessorTime blocks hblocks j ≤ t).card := by
  classical
  change ((uniformCorridorKnots blocks hblocks).filter fun s => s ≤ t).card = _
  rw [uniformCorridorKnots, Finset.filter_image]
  have hinj : Function.Injective (uniformGridSuccessorTime blocks hblocks) := by
    intro i j hij
    have hstrict : StrictMono
        ((UniformGrid.unit (K := ℝ) blocks hblocks).point) :=
      UniformGrid.strictMono_point (by norm_num [UniformGrid.unit])
    have htime := congrArg Subtype.val hij
    have heq : (UniformGrid.unit (K := ℝ) blocks hblocks).point
          (uniformGridSuccessorIndex blocks hblocks i) =
        (UniformGrid.unit (K := ℝ) blocks hblocks).point
          (uniformGridSuccessorIndex blocks hblocks j) := by
      simpa [uniformGridSuccessorTime] using htime
    have hindex := hstrict.injective heq
    apply Fin.ext
    have hval := congrArg Fin.val hindex
    change i.val + 1 = j.val + 1 at hval
    omega
  rw [Finset.card_image_of_injective _ hinj]

/-- The level selected by a sampled uniform-grid boundary lies between the
corresponding grid points. This is the mesh estimate needed to transfer
uniform continuity of the sampled function to the step boundary. -/
theorem uniformGridStepBoundary_levelIndex_mem_cell (blocks : ℕ)
    (hblocks : 0 < blocks) (f : C(unitInterval, ℝ)) (offset : ℝ)
    (t : unitInterval) :
    let b := uniformGridStepBoundary blocks hblocks f offset
    let i : Fin (blocks + 1) := Fin.cast
      (by simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks)
      (b.levelIndex t)
    uniformGridTime blocks hblocks i ≤ t ∧
      (∀ hi : i.val < blocks, t < uniformGridSuccessorTime blocks hblocks
        ⟨i.val, hi⟩) := by
  classical
  let b := uniformGridStepBoundary blocks hblocks f offset
  have hcard : b.knots.card = blocks := by
    simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks
  let i : Fin (blocks + 1) := Fin.cast (by rw [hcard]) (b.levelIndex t)
  have hiCard : i.val = (Finset.univ.filter fun j : Fin blocks =>
      uniformGridSuccessorTime blocks hblocks j ≤ t).card := by
    rw [Fin.val_cast]
    simpa [b, uniformGridStepBoundary] using
      uniformGridStepBoundary_levelIndex_card blocks hblocks f offset t
  have hP : ∀ j k : Fin blocks, j ≤ k →
      uniformGridSuccessorTime blocks hblocks k ≤ t →
        uniformGridSuccessorTime blocks hblocks j ≤ t := by
    intro j k hj hk
    have hidx : uniformGridSuccessorIndex blocks hblocks j ≤
        uniformGridSuccessorIndex blocks hblocks k := by
      apply Fin.mk_le_mk.mpr
      exact Nat.succ_le_succ (Fin.mk_le_mk.mp hj)
    have hmono := UniformGrid.monotone_point
      (UniformGrid.unit (K := ℝ) blocks hblocks) hidx
    apply Subtype.mk_le_mk.mpr
    exact hmono.trans (Subtype.mk_le_mk.mp hk)
  have hcounts := card_filter_antitone_index
    (fun j : Fin blocks => uniformGridSuccessorTime blocks hblocks j ≤ t)
    hP i.val hiCard.symm
  change uniformGridTime blocks hblocks i ≤ t ∧
    (∀ hi : i.val < blocks, t < uniformGridSuccessorTime blocks hblocks ⟨i.val, hi⟩)
  constructor
  · by_cases hi0 : i.val = 0
    · have hzero : i = 0 := Fin.ext hi0
      change uniformGridTime blocks hblocks i ≤ t
      rw [hzero]
      have hbot : uniformGridTime blocks hblocks 0 = ⊥ := by
        apply Subtype.ext
        simp [uniformGridTime, uniformGridIndex, UniformGrid.unit, UniformGrid.point]
      rw [hbot]
      exact bot_le
    · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi0
      let j : Fin blocks := ⟨i.val - 1, by omega⟩
      have hjlt : j.val < i.val := by dsimp [j]; omega
      have hPj := (hcounts j).1 hjlt
      have htime : uniformGridSuccessorTime blocks hblocks j =
          uniformGridTime blocks hblocks i := by
        apply Subtype.ext
        change (UniformGrid.unit (K := ℝ) blocks hblocks).point
            (uniformGridSuccessorIndex blocks hblocks j) =
          (UniformGrid.unit (K := ℝ) blocks hblocks).point
            (uniformGridIndex blocks hblocks i)
        congr 1
        apply Fin.ext
        change j.val + 1 = i.val
        dsimp [j]
        omega
      rw [← htime]
      exact hPj
  · intro hiBlocks
    have hiFin : i.val < blocks := hiBlocks
    let j : Fin blocks := ⟨i.val, hiFin⟩
    have hnotP := (hcounts j).2 (le_of_eq rfl)
    have htime : uniformGridSuccessorTime blocks hblocks j =
        uniformGridSuccessorTime blocks hblocks ⟨i.val, hiBlocks⟩ := rfl
    have hnot : ¬ uniformGridSuccessorTime blocks hblocks
        ⟨i.val, hiBlocks⟩ ≤ t := by simpa [j] using hnotP
    exact lt_of_not_ge hnot

@[simp]
theorem uniformGridTime_val (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin (blocks + 1)) :
    (uniformGridTime blocks hblocks i : ℝ) = (i : ℝ) / blocks := by
  simp [uniformGridTime, uniformGridIndex, UniformGrid.unit_point]

@[simp]
theorem uniformGridSuccessorTime_val (blocks : ℕ) (hblocks : 0 < blocks)
    (j : Fin blocks) :
    (uniformGridSuccessorTime blocks hblocks j : ℝ) = (j.val + 1 : ℝ) / blocks := by
  simp [uniformGridSuccessorTime, uniformGridSuccessorIndex,
    UniformGrid.unit_point]

/-- The selected sample is at most one grid spacing from the queried time. -/
theorem uniformGridStepBoundary_time_error_le (blocks : ℕ)
    (hblocks : 0 < blocks) (f : C(unitInterval, ℝ)) (offset : ℝ)
    (t : unitInterval) :
    let b := uniformGridStepBoundary blocks hblocks f offset
    let i : Fin (blocks + 1) := Fin.cast
      (by simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks)
      (b.levelIndex t)
    |(t : ℝ) - (uniformGridTime blocks hblocks i : ℝ)| ≤ 1 / blocks := by
  classical
  let b := uniformGridStepBoundary blocks hblocks f offset
  have hcard : b.knots.card = blocks := by
    simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks
  let i : Fin (blocks + 1) := Fin.cast (by rw [hcard]) (b.levelIndex t)
  have hcell := uniformGridStepBoundary_levelIndex_mem_cell
    blocks hblocks f offset t
  change uniformGridTime blocks hblocks i ≤ t ∧
    (∀ hi : i.val < blocks, t < uniformGridSuccessorTime blocks hblocks ⟨i.val, hi⟩)
    at hcell
  have hleft : uniformGridTime blocks hblocks i ≤ t := by
    exact hcell.1
  have hright : (t : ℝ) ≤ (uniformGridTime blocks hblocks i : ℝ) + 1 / blocks := by
    by_cases hi : i.val < blocks
    · have hnext : (t : ℝ) <
          (uniformGridSuccessorTime blocks hblocks ⟨i.val, hi⟩ : ℝ) :=
        Subtype.mk_lt_mk.mp (hcell.2 hi)
      rw [uniformGridSuccessorTime_val] at hnext
      rw [uniformGridTime_val]
      push_cast at hnext ⊢
      have hsplit : ((i : ℝ) + 1) / blocks = (i : ℝ) / blocks + 1 / blocks := by
        ring
      rw [hsplit] at hnext
      exact le_of_lt hnext
    · have hiLast : i.val = blocks := by omega
      rw [uniformGridTime_val]
      have htle : (t : ℝ) ≤ 1 := t.property.2
      have hbpos : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
      have hbne : (blocks : ℝ) ≠ 0 := ne_of_gt hbpos
      have hiReal : (i : ℝ) = blocks := by exact_mod_cast hiLast
      rw [hiReal, div_self hbne]
      have hstep : 0 < 1 / (blocks : ℝ) := by positivity
      linarith
  have hnonneg : 0 ≤ (t : ℝ) - (uniformGridTime blocks hblocks i : ℝ) := by
    exact sub_nonneg.mpr (Subtype.mk_le_mk.mp hleft)
  have hle : (t : ℝ) - (uniformGridTime blocks hblocks i : ℝ) ≤ 1 / blocks := by
    linarith [hright]
  change |(t : ℝ) - (uniformGridTime blocks hblocks i : ℝ)| ≤ 1 / blocks
  rw [abs_of_nonneg hnonneg]
  exact hle

/-- Uniform continuity makes the sampled step boundary uniformly close to
its continuous source as the grid mesh tends to zero. The conclusion is
formulated with an explicit mesh threshold, so applications can choose a
single grid fine enough for finitely many boundaries. -/
theorem exists_uniformGridStepBoundary_uniform_sample_error
    (f : C(unitInterval, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (blocks : ℕ) (hblocks : 0 < blocks),
      1 / (blocks : ℝ) < δ → ∀ (offset : ℝ) (t : unitInterval),
        let b := uniformGridStepBoundary blocks hblocks f offset
        let i : Fin (blocks + 1) := Fin.cast
          (by simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks)
          (b.levelIndex t)
        |f t - f (uniformGridTime blocks hblocks i)| < ε := by
  have huc : UniformContinuous (fun t : unitInterval => f t) :=
    CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff.mp huc) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro blocks hblocks hmesh offset t
  let b := uniformGridStepBoundary blocks hblocks f offset
  let i : Fin (blocks + 1) := Fin.cast (by
    simpa [b, uniformGridStepBoundary] using uniformCorridorKnots_card blocks hblocks)
    (b.levelIndex t)
  have htime := uniformGridStepBoundary_time_error_le blocks hblocks f offset t
  have hdist : dist t (uniformGridTime blocks hblocks i) < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    exact lt_of_le_of_lt (by simpa [b, i] using htime) hmesh
  have hmap := hmod hdist
  rw [Real.dist_eq] at hmap
  simpa [b, i] using hmap

/-- The paths starting at zero and lying strictly between two continuous
real-valued boundaries at every time. -/
def continuousBoundaryCorridorSet (lower upper : C(unitInterval, ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  {path | path ⊥ = 0 ∧ ∀ t : unitInterval, lower t < path t ∧ path t < upper t}

/-- The same corridor considered inside the endpoint convention `D₀`. -/
def relativeContinuousBoundaryCorridorSet (lower upper : C(unitInterval, ℝ)) :
    Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.terminalLeftPathSpace ∩ continuousBoundaryCorridorSet lower upper

/-- A step corridor with inward boundaries is contained in the continuous
boundary corridor. The statement is pointwise and does not depend on the
choice of a partition. -/
theorem corridorSet_subset_continuousBoundaryCorridorSet
    (stepUpper stepLower : StepBoundary)
    (lower upper : C(unitInterval, ℝ))
    (hinward : ∀ t, (lower t : EReal) < stepLower.eval t ∧
      stepUpper.eval t < (upper t : EReal)) :
    corridorSet stepUpper stepLower ⊆ continuousBoundaryCorridorSet lower upper := by
  intro path hpath
  rcases hpath with ⟨hzero, hcorridor⟩
  refine ⟨hzero, ?_⟩
  intro t
  constructor
  · apply EReal.coe_lt_coe_iff.mp
    exact (hinward t).1.trans (hcorridor t).1
  · apply EReal.coe_lt_coe_iff.mp
    exact (hcorridor t).2.trans (hinward t).2

/-- The continuous boundary corridor is contained in a step corridor with
outward boundaries. -/
theorem continuousBoundaryCorridorSet_subset_corridorSet
    (stepUpper stepLower : StepBoundary)
    (lower upper : C(unitInterval, ℝ))
    (houtward : ∀ t, stepLower.eval t < (lower t : EReal) ∧
      (upper t : EReal) < stepUpper.eval t) :
    continuousBoundaryCorridorSet lower upper ⊆ corridorSet stepUpper stepLower := by
  intro path hpath
  rcases hpath with ⟨hzero, hcorridor⟩
  refine ⟨hzero, ?_⟩
  intro t
  constructor
  · exact (houtward t).1.trans (EReal.coe_lt_coe_iff.mpr (hcorridor t).1)
  · exact (EReal.coe_lt_coe_iff.mpr (hcorridor t).2).trans (houtward t).2

/-- A continuous path strictly between two finite-step boundaries witnesses
continuous admissibility of the corresponding step corridor. -/
theorem hasContinuousAdmissiblePath_of_witness
    (stepUpper stepLower : StepBoundary) (center : C(unitInterval, ℝ))
    (hcenterZero : center ⊥ = 0)
    (hcenter : ∀ t, stepLower.eval t < (center t : EReal) ∧
      (center t : EReal) < stepUpper.eval t) :
    HasContinuousAdmissiblePath stepUpper stepLower := by
  refine ⟨center, hcenterZero, ?_⟩
  refine ⟨hcenterZero, ?_⟩
  intro t
  exact hcenter t

/-- The same inward containment, restricted to `D₀`. -/
theorem relative_corridorSet_subset_relativeContinuousBoundaryCorridorSet
    (stepUpper stepLower : StepBoundary)
    (lower upper : C(unitInterval, ℝ))
    (hinward : ∀ t, (lower t : EReal) < stepLower.eval t ∧
      stepUpper.eval t < (upper t : EReal)) :
    Skorokhod.terminalLeftPathSpace ∩ corridorSet stepUpper stepLower ⊆
      relativeContinuousBoundaryCorridorSet lower upper := by
  intro path hpath
  rcases hpath with ⟨hD₀, hcorridor⟩
  exact ⟨hD₀,
    corridorSet_subset_continuousBoundaryCorridorSet stepUpper stepLower lower upper
      hinward hcorridor⟩

/-- The same outward containment, restricted to `D₀`. -/
theorem relativeContinuousBoundaryCorridorSet_subset_relative_corridorSet
    (stepUpper stepLower : StepBoundary)
    (lower upper : C(unitInterval, ℝ))
    (houtward : ∀ t, stepLower.eval t < (lower t : EReal) ∧
      (upper t : EReal) < stepUpper.eval t) :
    relativeContinuousBoundaryCorridorSet lower upper ⊆
      Skorokhod.terminalLeftPathSpace ∩ corridorSet stepUpper stepLower := by
  intro path hpath
  rcases hpath with ⟨hD₀, hcorridor⟩
  exact ⟨hD₀,
    continuousBoundaryCorridorSet_subset_corridorSet stepUpper stepLower lower upper
      houtward hcorridor⟩

/-- Strictly separated continuous boundaries admit a continuous center which
starts at zero and stays a uniform positive distance from both boundaries.
This is the compactness input for constructing finite step-corridor
approximations. -/
theorem exists_continuousCorridorCenter_with_uniformMargin
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ center : C(unitInterval, ℝ), ∃ margin : ℝ,
      0 < margin ∧ center ⊥ = 0 ∧
        ∀ t, lower t + margin ≤ center t ∧ center t + margin ≤ upper t := by
  let θ : ℝ := - lower ⊥ / (upper ⊥ - lower ⊥)
  have hden : 0 < upper ⊥ - lower ⊥ := by linarith [hstartLower, hstartUpper]
  have hθ : 0 < θ ∧ θ < 1 := by
    dsimp [θ]
    constructor
    · exact div_pos (neg_pos.mpr hstartLower) hden
    · rw [div_lt_one hden]
      linarith [hstartUpper]
  let center : C(unitInterval, ℝ) :=
    ⟨fun t => lower t + θ * (upper t - lower t),
      lower.continuous.add (continuous_const.mul (upper.continuous.sub lower.continuous))⟩
  have hwidthContinuous : Continuous fun t : unitInterval => upper t - lower t :=
    upper.continuous.sub lower.continuous
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set unitInterval).Nonempty from ⟨⊥, Set.mem_univ _⟩)
    hwidthContinuous.continuousOn
  have hwidth₀ : 0 < upper t₀ - lower t₀ := by
    have := hwidth t₀
    linarith
  let m₀ : ℝ := upper t₀ - lower t₀
  let margin : ℝ := min θ (1 - θ) * m₀ / 2
  have hm₀ : 0 < m₀ := by dsimp [m₀]; exact hwidth₀
  have hmargin : 0 < margin := by
    dsimp [margin]
    have hmin : 0 < min θ (1 - θ) := lt_min hθ.1 (by linarith [hθ.2])
    positivity
  refine ⟨center, margin, hmargin, ?_, ?_⟩
  · change lower ⊥ + θ * (upper ⊥ - lower ⊥) = 0
    dsimp [θ]
    field_simp [ne_of_gt hden]
    ring
  · intro t
    have hwidtht : m₀ ≤ upper t - lower t := by
      dsimp [m₀]
      exact ht₀ (Set.mem_univ t)
    have hleft : lower t + margin ≤ center t := by
      change lower t + margin ≤ lower t + θ * (upper t - lower t)
      have hθmin : min θ (1 - θ) ≤ θ := min_le_left _ _
      dsimp [margin]
      nlinarith [hwidtht, hθ.1, hθ.2]
    have hright : center t + margin ≤ upper t := by
      change lower t + θ * (upper t - lower t) + margin ≤ upper t
      have hθmin : min θ (1 - θ) ≤ 1 - θ := min_le_right _ _
      dsimp [margin]
      nlinarith [hwidtht, hθ.1, hθ.2]
    exact ⟨hleft, hright⟩

/-- A continuous path has no terminal jump, so it belongs to the source path
space `D₀`. -/
theorem ofContinuousMap_mem_terminalLeftPathSpace
    (path : C(unitInterval, ℝ)) :
    Skorokhod.ofContinuousMap path ∈ Skorokhod.terminalLeftPathSpace := by
  change Skorokhod.ofContinuousMap path ⊤ =
    Function.leftLim (fun t : unitInterval => Skorokhod.ofContinuousMap path t) ⊤
  have htop : (⊥ : unitInterval) < ⊤ := by norm_num [unitInterval]
  have hcontinuous : Tendsto (fun t : unitInterval => path t)
      (𝓝[<] (⊤ : unitInterval)) (𝓝 (path ⊤)) :=
    Filter.Tendsto.mono_left path.continuous.continuousAt.tendsto nhdsWithin_le_nhds
  have hleft := leftLim_eq_of_tendsto
    (h := nhdsLT_neBot_of_exists_lt ⟨⊥, htop⟩) hcontinuous
  simpa only [Skorokhod.ofContinuousMap_apply] using hleft.symm

/-- A strictly separated continuous corridor satisfying the pinned start
condition is nonempty even after restriction to `D₀`. -/
theorem exists_mem_relativeContinuousBoundaryCorridorSet
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ path, path ∈ relativeContinuousBoundaryCorridorSet lower upper := by
  obtain ⟨center, margin, hmargin, hcenter₀, hcenter⟩ :=
    exists_continuousCorridorCenter_with_uniformMargin lower upper hwidth
      hstartLower hstartUpper
  let path := Skorokhod.ofContinuousMap center
  refine ⟨path, ?_⟩
  constructor
  · exact ofContinuousMap_mem_terminalLeftPathSpace center
  · refine ⟨?_, ?_⟩
    · simpa [path, Skorokhod.ofContinuousMap_apply] using hcenter₀
    · intro t
      have ht := hcenter t
      constructor
      · exact lt_of_lt_of_le (lt_add_of_pos_right _ hmargin) ht.1
      · exact lt_of_lt_of_le (lt_add_of_pos_right _ hmargin) ht.2

private theorem sample_lt_add_two_of_abs {x y ε : ℝ} (hε : 0 < ε)
    (h : |x - y| < ε) : x < y + 2 * ε := by
  have hxy := (abs_lt.mp h).2
  linarith

private theorem sub_two_lt_sample_of_abs {x y ε : ℝ} (hε : 0 < ε)
    (h : |x - y| < ε) : y - 2 * ε < x := by
  have hxy := (abs_lt.mp h).1
  linarith

/-- Every strictly separated continuous corridor admits arbitrarily fine
uniform-grid inner and outer step corridors. The inner corridor lies inside
the continuous corridor and has a continuous witness; the target lies inside
the outer corridor. The conclusions remain valid after restriction to `D₀`.
This proves the deterministic set-sandwich part of continuous-boundary
approximation by the source's finite step corridors. -/
theorem exists_fine_uniformGrid_relativeCorridor_sandwich
    (lower upper : C(unitInterval, ℝ))
    (hwidth : ∀ t, lower t < upper t)
    (hstartLower : lower ⊥ < 0) (hstartUpper : 0 < upper ⊥) :
    ∃ center : C(unitInterval, ℝ), ∃ margin : ℝ,
      0 < margin ∧ center ⊥ = 0 ∧
        (∀ t, lower t + margin ≤ center t ∧ center t + margin ≤ upper t) ∧
        ∀ ε, 0 < ε → 3 * ε < margin →
          ∃ δ > 0, ∀ (blocks : ℕ) (hblocks : 0 < blocks),
            1 / (blocks : ℝ) < δ →
            let innerLower := uniformGridStepBoundary blocks hblocks lower (2 * ε)
            let innerUpper := uniformGridStepBoundary blocks hblocks upper (-2 * ε)
            let outerLower := uniformGridStepBoundary blocks hblocks lower (-2 * ε)
            let outerUpper := uniformGridStepBoundary blocks hblocks upper (2 * ε)
            (∀ t, (lower t : EReal) < innerLower.eval t ∧
              innerUpper.eval t < (upper t : EReal)) ∧
            (∀ t, outerLower.eval t < (lower t : EReal) ∧
              (upper t : EReal) < outerUpper.eval t) ∧
            HasContinuousAdmissiblePath innerUpper innerLower ∧
            HasContinuousAdmissiblePath outerUpper outerLower ∧
            Skorokhod.terminalLeftPathSpace ∩ corridorSet innerUpper innerLower ⊆
              relativeContinuousBoundaryCorridorSet lower upper ∧
            relativeContinuousBoundaryCorridorSet lower upper ⊆
              Skorokhod.terminalLeftPathSpace ∩ corridorSet outerUpper outerLower := by
  obtain ⟨center, margin, hmargin, hcenterZero, hcenter⟩ :=
    exists_continuousCorridorCenter_with_uniformMargin lower upper hwidth
      hstartLower hstartUpper
  refine ⟨center, margin, hmargin, hcenterZero, hcenter, ?_⟩
  intro ε hε hsmall
  obtain ⟨δL, hδL, herrorL⟩ :=
    exists_uniformGridStepBoundary_uniform_sample_error lower ε hε
  obtain ⟨δU, hδU, herrorU⟩ :=
    exists_uniformGridStepBoundary_uniform_sample_error upper ε hε
  let δ := min δL δU
  have hδ : 0 < δ := lt_min hδL hδU
  refine ⟨δ, hδ, ?_⟩
  intro blocks hblocks hmesh
  let innerLower := uniformGridStepBoundary blocks hblocks lower (2 * ε)
  let innerUpper := uniformGridStepBoundary blocks hblocks upper (-2 * ε)
  let outerLower := uniformGridStepBoundary blocks hblocks lower (-2 * ε)
  let outerUpper := uniformGridStepBoundary blocks hblocks upper (2 * ε)
  have hmeshL : 1 / (blocks : ℝ) < δL := hmesh.trans_le (min_le_left _ _)
  have hmeshU : 1 / (blocks : ℝ) < δU := hmesh.trans_le (min_le_right _ _)
  have hinward : ∀ t, (lower t : EReal) < innerLower.eval t ∧
      innerUpper.eval t < (upper t : EReal) := by
    intro t
    let iL : Fin (blocks + 1) := Fin.cast
      (by simpa [innerLower, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerLower.levelIndex t)
    let iU : Fin (blocks + 1) := Fin.cast
      (by simpa [innerUpper, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerUpper.levelIndex t)
    have hsL := herrorL blocks hblocks hmeshL (2 * ε) t
    have hsU := herrorU blocks hblocks hmeshU (-2 * ε) t
    change |lower t - lower (uniformGridTime blocks hblocks iL)| < ε at hsL
    change |upper t - upper (uniformGridTime blocks hblocks iU)| < ε at hsU
    have hevalL : innerLower.eval t =
        ((lower (uniformGridTime blocks hblocks iL) + 2 * ε : ℝ) : EReal) := by
      simpa [innerLower, iL, uniformGridStepBoundary] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks lower (2 * ε) t
    have hevalU : innerUpper.eval t =
        ((upper (uniformGridTime blocks hblocks iU) - 2 * ε : ℝ) : EReal) := by
      simpa [innerUpper, iU, uniformGridStepBoundary, sub_eq_add_neg] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks upper (-2 * ε) t
    constructor
    · rw [hevalL]
      exact EReal.coe_lt_coe_iff.mpr (sample_lt_add_two_of_abs hε hsL)
    · rw [hevalU]
      exact EReal.coe_lt_coe_iff.mpr (sub_two_lt_sample_of_abs hε hsU)
  have houtward : ∀ t, outerLower.eval t < (lower t : EReal) ∧
      (upper t : EReal) < outerUpper.eval t := by
    intro t
    let iL : Fin (blocks + 1) := Fin.cast
      (by simpa [outerLower, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (outerLower.levelIndex t)
    let iU : Fin (blocks + 1) := Fin.cast
      (by simpa [outerUpper, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (outerUpper.levelIndex t)
    have hsL := herrorL blocks hblocks hmeshL (-2 * ε) t
    have hsU := herrorU blocks hblocks hmeshU (2 * ε) t
    change |lower t - lower (uniformGridTime blocks hblocks iL)| < ε at hsL
    change |upper t - upper (uniformGridTime blocks hblocks iU)| < ε at hsU
    have hevalL : outerLower.eval t =
        ((lower (uniformGridTime blocks hblocks iL) - 2 * ε : ℝ) : EReal) := by
      simpa [outerLower, iL, uniformGridStepBoundary, sub_eq_add_neg] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks lower (-2 * ε) t
    have hevalU : outerUpper.eval t =
        ((upper (uniformGridTime blocks hblocks iU) + 2 * ε : ℝ) : EReal) := by
      simpa [outerUpper, iU, uniformGridStepBoundary] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks upper (2 * ε) t
    constructor
    · rw [hevalL]
      exact EReal.coe_lt_coe_iff.mpr (sub_two_lt_sample_of_abs hε hsL)
    · rw [hevalU]
      exact EReal.coe_lt_coe_iff.mpr (sample_lt_add_two_of_abs hε hsU)
  have hadmissible : HasContinuousAdmissiblePath innerUpper innerLower := by
    apply hasContinuousAdmissiblePath_of_witness innerUpper innerLower center
      hcenterZero
    intro t
    let iL : Fin (blocks + 1) := Fin.cast
      (by simpa [innerLower, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerLower.levelIndex t)
    let iU : Fin (blocks + 1) := Fin.cast
      (by simpa [innerUpper, uniformGridStepBoundary] using
        uniformCorridorKnots_card blocks hblocks) (innerUpper.levelIndex t)
    have hsL := herrorL blocks hblocks hmeshL (2 * ε) t
    have hsU := herrorU blocks hblocks hmeshU (-2 * ε) t
    change |lower t - lower (uniformGridTime blocks hblocks iL)| < ε at hsL
    change |upper t - upper (uniformGridTime blocks hblocks iU)| < ε at hsU
    have hevalL : innerLower.eval t =
        ((lower (uniformGridTime blocks hblocks iL) + 2 * ε : ℝ) : EReal) := by
      simpa [innerLower, iL, uniformGridStepBoundary] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks lower (2 * ε) t
    have hevalU : innerUpper.eval t =
        ((upper (uniformGridTime blocks hblocks iU) - 2 * ε : ℝ) : EReal) := by
      simpa [innerUpper, iU, uniformGridStepBoundary, sub_eq_add_neg] using
        uniformGridStepBoundary_eval_eq_sample blocks hblocks upper (-2 * ε) t
    constructor
    · rw [hevalL]
      apply EReal.coe_lt_coe_iff.mpr
      have hfirst := (abs_lt.mp hsL).1
      calc
        lower (uniformGridTime blocks hblocks iL) + 2 * ε < lower t + 3 * ε := by linarith
        _ < lower t + margin := by linarith
        _ ≤ center t := (hcenter t).1
    · rw [hevalU]
      apply EReal.coe_lt_coe_iff.mpr
      have hsecond := (abs_lt.mp hsU).2
      have hcenterUpper : center t ≤ upper t - margin := by linarith [(hcenter t).2]
      calc
        center t ≤ upper t - margin := hcenterUpper
        _ < upper t - 3 * ε := by linarith
        _ < upper (uniformGridTime blocks hblocks iU) - 2 * ε := by linarith
  have hadmissibleOuter : HasContinuousAdmissiblePath outerUpper outerLower := by
    apply hasContinuousAdmissiblePath_of_witness outerUpper outerLower center hcenterZero
    intro t
    constructor
    · exact (houtward t).1.trans
        (EReal.coe_lt_coe_iff.mpr
          (lt_of_lt_of_le (lt_add_of_pos_right _ hmargin) (hcenter t).1))
    · exact (EReal.coe_lt_coe_iff.mpr
        (lt_of_lt_of_le (lt_add_of_pos_right _ hmargin) (hcenter t).2)).trans
        (houtward t).2
  exact ⟨hinward, houtward, hadmissible,
    hadmissibleOuter,
    relative_corridorSet_subset_relativeContinuousBoundaryCorridorSet
      innerUpper innerLower lower upper hinward,
    relativeContinuousBoundaryCorridorSet_subset_relative_corridorSet
      outerUpper outerLower lower upper houtward⟩

end Skorokhod.PathClass.StepCorridor

end
