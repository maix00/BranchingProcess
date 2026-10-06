/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Basic
public import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort

/-!
# Partitions from finite ordered time points

Turn a finite strictly increasing sequence of times with the correct
endpoints into the indexed half-open partition used by Skorokhod oscillation
arguments. The cell index is the greatest left endpoint not exceeding the
time, with the terminal point assigned to the last cell.
-/

@[expose] public section

open Set
open scoped Topology

namespace Skorokhod

namespace OscillationPartition

/-- The set of cell indices whose left endpoint is at or before `t`. -/
noncomputable def predecessorIndices {n : ℕ}
    (points : Fin (n + 1) → unitInterval) (t : unitInterval) : Finset (Fin n) :=
  Finset.univ.filter fun i => points i.castSucc ≤ t

/-- The first cell always starts at or before every time. -/
theorem predecessorIndices_nonempty {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval)
    (hfirst : points ⟨0, by omega⟩ = ⊥) (t : unitInterval) :
    (predecessorIndices points t).Nonempty := by
  classical
  refine ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have hzero : (⟨0, hn⟩ : Fin n).castSucc = ⟨0, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [hzero, hfirst]
  exact bot_le

/-- The cell containing `t`, defined as the greatest left endpoint at or
before `t`. -/
noncomputable def finitePointIndex {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval)
    (hfirst : points ⟨0, by omega⟩ = ⊥) (t : unitInterval) : Fin n :=
  (predecessorIndices points t).max'
    (predecessorIndices_nonempty hn points hfirst t)

/-- The selected cell starts at or before the queried time. -/
theorem finitePointIndex_lower {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval)
    (hfirst : points ⟨0, by omega⟩ = ⊥) (t : unitInterval) :
    points (finitePointIndex hn points hfirst t).castSucc ≤ t := by
  classical
  let P := predecessorIndices points t
  have hP : P.Nonempty := predecessorIndices_nonempty hn points hfirst t
  have hmem : finitePointIndex hn points hfirst t ∈ P := by
    change P.max' hP ∈ P
    exact Finset.max'_mem P hP
  exact (Finset.mem_filter.mp hmem).2

/-- The selected cell ends after the queried time, unless it is the final cell. -/
theorem finitePointIndex_upper {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval)
    (hfirst : points ⟨0, by omega⟩ = ⊥)
    (t : unitInterval) :
    t < points (finitePointIndex hn points hfirst t).succ ∨
      (finitePointIndex hn points hfirst t).val + 1 = n := by
  classical
  let i := finitePointIndex hn points hfirst t
  change t < points i.succ ∨ i.val + 1 = n
  by_cases hlast : i.val + 1 = n
  · exact Or.inr hlast
  · by_cases htime : t < points i.succ
    · exact Or.inl htime
    · have hnextle : points i.succ ≤ t := le_of_not_gt htime
      let j : Fin n := ⟨i.val + 1, by omega⟩
      have hj : j.castSucc = i.succ := by
        apply Fin.ext
        simp [j]
      let P := predecessorIndices points t
      have hP : P.Nonempty := predecessorIndices_nonempty hn points hfirst t
      have hjmem : j ∈ P := by
        change j ∈ predecessorIndices points t
        rw [predecessorIndices, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hj ▸ hnextle⟩
      have hji : j ≤ i := Finset.le_max' P j hjmem
      have hij : i < j := by
        apply Fin.lt_def.mpr
        simp [j]
      exact (not_le_of_gt hij hji).elim

/-- Every partition point is assigned to the cell starting there. -/
theorem finitePointIndex_start {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval)
    (hfirst : points ⟨0, by omega⟩ = ⊥)
    (hstrict : StrictMono points) (i : Fin n) :
    finitePointIndex hn points hfirst (points i.castSucc) = i := by
  classical
  let P := predecessorIndices points (points i.castSucc)
  have hP : P.Nonempty :=
    predecessorIndices_nonempty hn points hfirst (points i.castSucc)
  have hi : i ∈ P := by
    change i ∈ predecessorIndices points (points i.castSucc)
    rw [predecessorIndices, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, le_rfl⟩
  change P.max' hP = i
  apply Fin.le_antisymm
  · apply Finset.max'_le
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    by_contra hji
    have hij : i < j := lt_of_not_ge hji
    have hcast : i.castSucc < j.castSucc := by
      apply Fin.lt_def.mpr
      simpa using hij
    have hpoints : points i.castSucc < points j.castSucc := by
      exact hstrict hcast
    exact (not_lt_of_ge hj') hpoints
  · exact Finset.le_max' P i hi

/-- The finite set of distances between consecutive points. -/
noncomputable def finitePointGaps {n : ℕ}
    (points : Fin (n + 1) → unitInterval) : Finset ℝ :=
  Finset.univ.image fun i : Fin n => dist (points i.castSucc) (points i.succ)

/-- A nonempty list of consecutive cells has a nonempty set of gaps. -/
theorem finitePointGaps_nonempty {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval) :
    (finitePointGaps points).Nonempty := by
  classical
  refine ⟨dist (points (Fin.castSucc ⟨0, hn⟩))
      (points (Fin.succ ⟨0, hn⟩)), ?_⟩
  exact Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩

/-- The minimum length among consecutive cells. -/
noncomputable def finitePointMesh {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval) : ℝ :=
  (finitePointGaps points).min' (finitePointGaps_nonempty hn points)

/-- Construct an `OscillationPartition` from a strictly increasing finite
sequence of time points with endpoints `0` and `1`. -/
noncomputable def ofFinitePoints {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval)
    (hfirst : points ⟨0, by omega⟩ = ⊥)
    (hlast : points ⟨n, by omega⟩ = ⊤)
    (hstrict : StrictMono points) : OscillationPartition where
  size := n
  size_pos := hn
  points := points
  first := hfirst
  last := hlast
  strictMono_points := hstrict
  index := finitePointIndex hn points hfirst
  index_lower := finitePointIndex_lower hn points hfirst
  index_upper := finitePointIndex_upper hn points hfirst
  index_start := finitePointIndex_start hn points hfirst hstrict
  mesh := finitePointMesh hn points
  mesh_pos := by
    classical
    change 0 < (finitePointGaps points).min'
      (finitePointGaps_nonempty hn points)
    have hminMem := (finitePointGaps points).min'_mem
      (finitePointGaps_nonempty hn points)
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hminMem
    rw [← hi]
    exact dist_pos.mpr (ne_of_lt (hstrict i.castSucc_lt_succ))
  gap_lower := by
    intro i
    change (finitePointGaps points).min'
      (finitePointGaps_nonempty hn points) ≤
        dist (points i.castSucc) (points i.succ)
    exact Finset.min'_le (finitePointGaps points)
      (dist (points i.castSucc) (points i.succ))
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- A finite set of unit-interval points containing both endpoints determines
an oscillation partition with exactly those partition points. -/
theorem exists_ofFinset
    (pointsSet : Finset unitInterval)
    (hbottom : (⊥ : unitInterval) ∈ pointsSet)
    (htop : (⊤ : unitInterval) ∈ pointsSet) :
    ∃ partition : OscillationPartition, Set.range partition.points = pointsSet ∧
      partition.mesh = OscillationPartition.finitePointMesh partition.size_pos partition.points := by
  classical
  have hendpoints : ({(⊥ : unitInterval), ⊤} : Finset unitInterval) ⊆ pointsSet := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hbottom
    · exact htop
  have hcard : 2 ≤ pointsSet.card := by
    have hpair : ({(⊥ : unitInterval), ⊤} : Finset unitInterval).card = 2 :=
      Finset.card_pair bot_ne_top
    exact hpair ▸ Finset.card_le_card hendpoints
  let size := pointsSet.card - 1
  have hsizeCard : size + 1 = pointsSet.card :=
    Nat.sub_add_cancel (by omega : 1 ≤ pointsSet.card)
  let orderedPoints : Fin pointsSet.card → unitInterval :=
    pointsSet.orderEmbOfFin rfl
  let points : Fin (size + 1) → unitInterval := fun i =>
    orderedPoints (Fin.cast hsizeCard i)
  have hpointsStrict : StrictMono points := by
    apply StrictMono.comp (pointsSet.orderEmbOfFin rfl).strictMono
    intro i j hij
    apply Fin.lt_def.mpr
    simpa [Fin.val_cast] using (Fin.lt_def.mp hij)
  have hpointsBottom : points ⟨0, by omega⟩ = ⊥ := by
    have hmem : (⊥ : unitInterval) ∈ (pointsSet : Set unitInterval) := hbottom
    rw [← pointsSet.range_orderEmbOfFin rfl] at hmem
    obtain ⟨i, hi⟩ := hmem
    let zeroIndex : Fin pointsSet.card := ⟨0, by omega⟩
    have hzero : zeroIndex ≤ i := Fin.le_iff_val_le_val.mpr (by simp [zeroIndex])
    have hle := (pointsSet.orderEmbOfFin rfl).monotone hzero
    have hraw : (pointsSet.orderEmbOfFin rfl) zeroIndex ≤ ⊥ := by
      simpa [hi] using hle
    change orderedPoints (Fin.cast hsizeCard ⟨0, by omega⟩) = ⊥
    have hcast : Fin.cast hsizeCard (⟨0, by omega⟩ : Fin (size + 1)) = zeroIndex := by
      apply Fin.ext
      simp [zeroIndex, Fin.val_cast]
    rw [hcast]
    exact le_antisymm hraw bot_le
  have hpointsTop : points ⟨size, by omega⟩ = ⊤ := by
    have hmem : (⊤ : unitInterval) ∈ (pointsSet : Set unitInterval) := htop
    rw [← pointsSet.range_orderEmbOfFin rfl] at hmem
    obtain ⟨i, hi⟩ := hmem
    let hlast : Fin pointsSet.card := ⟨size, by omega⟩
    have hiSize : i.val < size + 1 := by simp [hsizeCard]
    have hlastVal : hlast.val = size := rfl
    have hle : i ≤ hlast := Fin.le_iff_val_le_val.mpr (by
      rw [hlastVal]
      exact Nat.le_of_lt_succ hiSize)
    have hmono := (pointsSet.orderEmbOfFin rfl).monotone hle
    have htop' : (pointsSet.orderEmbOfFin rfl) i = ⊤ := hi
    have hraw : ⊤ ≤ (pointsSet.orderEmbOfFin rfl) hlast := by
      simpa [htop'] using hmono
    have hupper : (pointsSet.orderEmbOfFin rfl) hlast ≤ ⊤ := le_top
    have hlastEq : (pointsSet.orderEmbOfFin rfl) hlast = ⊤ :=
      le_antisymm hupper hraw
    change orderedPoints (Fin.cast hsizeCard ⟨size, by omega⟩) = ⊤
    have hlastCast :
        Fin.cast hsizeCard (⟨size, by omega⟩ : Fin (size + 1)) = hlast := by
      apply Fin.ext
      simp [hlast]
    rw [hlastCast]
    exact hlastEq
  have hsizePos : 0 < size := by omega
  let partition := OscillationPartition.ofFinitePoints hsizePos points
    hpointsBottom hpointsTop hpointsStrict
  have hrangePoints : Set.range points = pointsSet := by
    rw [← pointsSet.range_orderEmbOfFin rfl]
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hsizeCard i, rfl⟩
    · rintro ⟨i, hi⟩
      refine ⟨Fin.cast hsizeCard.symm i, ?_⟩
      change orderedPoints (Fin.cast hsizeCard (Fin.cast hsizeCard.symm i)) = z
      have hcast : Fin.cast hsizeCard (Fin.cast hsizeCard.symm i) = i := by
        apply Fin.ext
        simp
      rw [hcast]
      exact hi
  refine ⟨partition, ?_, ?_⟩
  · change Set.range points = pointsSet
    exact hrangePoints
  · rfl


end OscillationPartition

end Skorokhod

end
