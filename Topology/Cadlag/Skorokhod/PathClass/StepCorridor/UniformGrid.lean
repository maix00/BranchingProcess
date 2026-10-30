/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Basic
public import Order.Interval.UniformGrid
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform-grid approximation of continuous boundaries

The definitions encode the standard partition of $[0,1]$ into $m$ cells,
sample a continuous boundary at the left endpoint of each cell (and at $1$),
and control the sampling error by the grid mesh.

## Public declarations

- `uniformGridIndex`, `uniformGridSuccessorIndex`, `uniformGridTime`,
  `uniformGridSuccessorTime`, and `uniformCorridorKnots` encode the grid;
  the times satisfy $t_i=i/m$ and $t_{j+1}=(j+1)/m$, and the knot set has
  cardinality $m$ and omits $0$.
- `uniformGridStepBoundary` samples $f$ at those grid times and adds an
  offset. `uniformGridStepBoundary_eval` and
  `uniformGridStepBoundary_eval_eq_sample` identify its value with that
  sample; `uniformGridStepBoundary_levelIndex_mem_cell` places each sample
  in the associated cell.
- `uniformGridTime_val`, `uniformGridSuccessorTime_val`, and
  `uniformGridStepBoundary_time_error_le` give the coordinate and mesh bounds.
- `exists_uniformGridStepBoundary_uniform_sample_error` states that for each
  $\varepsilon>0$ there is $\delta>0$ such that mesh $1/m<\delta$ makes every
  sampled value differ from $f(t)$ by less than $\varepsilon$, uniformly in
  the offset and time.
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

private lemma card_filter_antitone_index {n : ℕ} (P : Fin n → Prop)
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

private lemma uniformGridStepBoundary_levelIndex_card (blocks : ℕ)
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


end Skorokhod.PathClass.StepCorridor

end
