/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.UniformGrid
public import Probability.Process.RandomWalk.Path.Cadlag
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Finite
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Measurability

/-!
# Oscillation partitions for finite random-walk paths

The deterministic normalized step path has no within-cell oscillation on its
own time grid. For each fixed step count, this gives a common positive mesh
for every choice of increments; the mesh may shrink with the step count.
-/

@[expose] public section

open Skorokhod

namespace ProbabilityTheory.RandomWalk

/-- The points of the uniform partition used by an `n`-step path. -/
noncomputable def normalizedStepGridPoints (n : ℕ) (hn : 0 < n)
    (j : Fin (n + 1)) : unitInterval := by
  let grid := UniformGrid.unit (K := ℝ) n hn
  refine ⟨grid.point j, ?_⟩
  change 0 ≤ grid.point j ∧ grid.point j ≤ 1
  simpa [grid, UniformGrid.unit, Set.mem_Icc] using (grid.point_mem_Icc j)

@[simp]
private theorem normalizedStepGridPoints_coe (n : ℕ) (hn : 0 < n)
    (j : Fin (n + 1)) :
    (normalizedStepGridPoints n hn j : ℝ) = (j : ℝ) / n := by
  simp [normalizedStepGridPoints, UniformGrid.point, UniformGrid.unit]

theorem normalizedStepGridPoints_first (n : ℕ) (hn : 0 < n) :
    normalizedStepGridPoints n hn ⟨0, by omega⟩ = ⊥ := by
  apply Subtype.ext
  simp [normalizedStepGridPoints, UniformGrid.point, UniformGrid.unit]

theorem normalizedStepGridPoints_last (n : ℕ) (hn : 0 < n) :
    normalizedStepGridPoints n hn ⟨n, by omega⟩ = ⊤ := by
  apply Subtype.ext
  simp [normalizedStepGridPoints, UniformGrid.point, UniformGrid.unit,
    Nat.cast_ne_zero.mpr hn.ne']

theorem normalizedStepGridPoints_strictMono (n : ℕ) (hn : 0 < n) :
    StrictMono (normalizedStepGridPoints n hn) := by
  intro i j hij
  apply Subtype.mk_lt_mk.mpr
  simpa [normalizedStepGridPoints] using
    (UniformGrid.strictMono_point
      (grid := UniformGrid.unit n hn) (by simp [UniformGrid.unit]) hij)

/-- The finite partition whose cells are the steps of an `n`-step path. -/
noncomputable def normalizedStepOscillationPartition (n : ℕ)
    (hn : 0 < n) : OscillationPartition :=
  OscillationPartition.ofFinitePoints hn (normalizedStepGridPoints n hn)
    (normalizedStepGridPoints_first n hn)
    (normalizedStepGridPoints_last n hn)
    (normalizedStepGridPoints_strictMono n hn)

/-- On a nonterminal time, the cell index in the step partition is the
integer part of the rescaled time. -/
private theorem natFloor_mul_eq_stepPartitionIndex (n : ℕ) (hn : 0 < n)
    (t : unitInterval) (ht : t ≠ ⊤) :
    ⌊(n : ℝ) * t⌋₊ =
      ((normalizedStepOscillationPartition n hn).index t).val := by
  let partition := normalizedStepOscillationPartition n hn
  have hi : (partition.index t).val < n := by
    exact (partition.index t).is_lt
  let i : Fin n := ⟨(partition.index t).val, hi⟩
  have hindex : partition.index t = i := by
    apply Fin.ext
    rfl
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hleftPoint :
      (partition.points i.castSucc : ℝ) = (i.val : ℝ) / n := by
    change (normalizedStepGridPoints n hn i.castSucc : ℝ) = _
    rw [normalizedStepGridPoints_coe]
    simp
  have hlowerPoint : (i.val : ℝ) / n ≤ t := by
    have hlower := partition.index_lower t
    rw [hindex] at hlower
    have hlowerReal :
        (partition.points i.castSucc : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast hlower
    rw [hleftPoint] at hlowerReal
    exact hlowerReal
  have hlow : (i.val : ℝ) ≤ (n : ℝ) * t := by
    have hmul := (div_le_iff₀ hnReal).mp hlowerPoint
    nlinarith [hmul]
  have hhigh : (n : ℝ) * t < (i.val : ℝ) + 1 := by
    have hupperIndex := partition.index_upper t
    rw [hindex] at hupperIndex
    rcases hupperIndex with hupper | hlast
    · have hnextPoint :
          (partition.points i.succ : ℝ) = ((i.val : ℝ) + 1) / n := by
        change (normalizedStepGridPoints n hn i.succ : ℝ) = _
        rw [normalizedStepGridPoints_coe]
        simp
      have hupperPoint : t < ((i.val : ℝ) + 1) / n := by
        rw [← hnextPoint]
        have hupperReal : (t : ℝ) < (partition.points i.succ : ℝ) := by
          exact_mod_cast hupper
        exact hupperReal
      have hmul := (lt_div_iff₀ hnReal).mp hupperPoint
      nlinarith [hmul]
    · have htlt : (t : ℝ) < 1 := by
        by_contra hnot
        have heq : (t : ℝ) = 1 := le_antisymm t.property.2
          (le_of_not_gt hnot)
        apply ht
        exact Subtype.ext heq
      have hlastN : i.val + 1 = n := by
        exact hlast
      have hlastReal : (i.val : ℝ) + 1 = n := by exact_mod_cast hlastN
      nlinarith [htlt, hnReal]
  apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg n) t.property.1)).2
  exact ⟨hlow, hhigh⟩

/-- Every `n`-step normalized path is constant on the cells of its uniform
step partition, away from the terminal value. -/
theorem normalizedStepCadlagPathIcc_oscillationBoundedOnStepPartition
    (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (increment : ℕ → ℝ) :
    OscillationBoundedOnPartition (normalizedStepOscillationPartition n hn)
      (normalizedStepCadlagPathIcc scale n increment) 0 := by
  intro s t hs ht hindex
  have hsFloor := natFloor_mul_eq_stepPartitionIndex n hn s hs
  have htFloor := natFloor_mul_eq_stepPartitionIndex n hn t ht
  have hfloor : (⌊(n : ℝ) * s⌋₊ : ℕ) = ⌊(n : ℝ) * t⌋₊ := by
    calc
      _ = ((normalizedStepOscillationPartition n hn).index s).val := hsFloor
      _ = ((normalizedStepOscillationPartition n hn).index t).val :=
        congrArg Fin.val hindex
      _ = _ := htFloor.symm
  simp [normalizedStepCadlagPathIcc_apply, normalizedStepPath, hfloor]

/-- For each fixed step count, all normalized step paths admit a common
positive-gap partition with zero cell oscillation. The gap depends only on
the step count, so this absorbs any finite prefix in an asymptotic tightness
argument. -/
theorem exists_pos_uniform_admitsOscillationPartition_normalizedStepPath
    (scale : ℕ → ℝ) (n : ℕ) (hn : 0 < n) {maximumOscillation : ℝ}
    (hoscillation : 0 < maximumOscillation) :
    ∃ minimumGap > 0, ∀ increment : ℕ → ℝ,
      normalizedStepCadlagPathIcc scale n increment ∈
        admitsOscillationPartition minimumGap maximumOscillation := by
  let partition := normalizedStepOscillationPartition n hn
  refine ⟨partition.mesh / 2, half_pos partition.mesh_pos, fun increment => ?_⟩
  change ∃ p : OscillationPartition,
    partition.mesh / 2 < p.mesh ∧
      ∃ bound < maximumOscillation,
        OscillationBoundedOnPartition p
          (normalizedStepCadlagPathIcc scale n increment) bound
  refine ⟨partition, by dsimp [partition]; linarith [partition.mesh_pos],
    0, hoscillation, ?_⟩
  exact normalizedStepCadlagPathIcc_oscillationBoundedOnStepPartition
    scale n hn increment

end ProbabilityTheory.RandomWalk

end
