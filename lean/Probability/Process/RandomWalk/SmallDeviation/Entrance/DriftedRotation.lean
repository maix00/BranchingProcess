/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.LinearTubeRotation

/-!
# Cyclic shifts after removing a linear drift

The entrance estimate has a boundary that moves linearly in discrete time.
Subtracting that drift before choosing the cyclic origin turns it into a
static corridor. This file records the deterministic identity that makes this
change compatible with cyclically rotated increments.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- Remove a constant drift per step from the partial-sum path. -/
def removeLinearDrift {n : ℕ} (drift : ℝ) (s : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun j => s j - drift * (j.val : ℝ)

/-- Cyclic rotation commutes with removing the corresponding elapsed-time
drift. In the wrapped case the elapsed time is the wrapped prefix length. -/
theorem cyclicPartialSum_removeLinearDrift {n : ℕ}
    (s : Fin (n + 1) → ℝ) (drift : ℝ) (k : Fin n)
    (j : Fin (n + 1)) :
    cyclicPartialSum (removeLinearDrift drift s) k j =
      cyclicPartialSum s k j - drift * (j.val : ℝ) := by
  unfold cyclicPartialSum removeLinearDrift
  split_ifs with h
  · simp only [Fin.val_castSucc, Fin.val_mk]
    have hadd : ((k.val + j.val : ℕ) : ℝ) =
        (k.val : ℝ) + (j.val : ℝ) := by exact_mod_cast Nat.cast_add k.val j.val
    rw [hadd]
    ring
  · let p : ℕ := k.val + j.val - n
    have hle : n ≤ k.val + j.val := by omega
    have htime : ((k.val + j.val - n : ℕ) : ℝ) =
        (k.val : ℝ) + (j.val : ℝ) - (n : ℝ) := by
      simpa [Nat.cast_add] using
        (Nat.cast_sub hle : ((k.val + j.val - n : ℕ) : ℝ) =
          ((k.val + j.val : ℕ) : ℝ) - (n : ℝ))
    simp only [Fin.val_castSucc, Fin.val_mk]
    dsimp [p]
    rw [htime]
    ring

/-- A static offset-corridor conclusion for a drift-removed path yields the
same moving corridor conclusion for the original cyclically shifted path. -/
theorem cyclicPartialSum_mem_movingOffsetCorridor_of_removeLinearDrift
    {n : ℕ} (s : Fin (n + 1) → ℝ) (drift : ℝ) (k : Fin n)
    {u : ℝ} {j : Fin (n + 1)}
    (h : cyclicPartialSum (removeLinearDrift drift s) k j ∈
      Set.Icc (-u) (1 - u)) :
    cyclicPartialSum s k j - drift * (j.val : ℝ) ∈
      Set.Icc (-u) (1 - u) := by
  rw [← cyclicPartialSum_removeLinearDrift]
  exact h

/-- A line-tube path whose drift-removed version is near the increasing line
has a cyclic shift satisfying the corresponding moving offset corridor. -/
theorem exists_movingOffsetCorridor_of_linearTube_lowerEdge
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Set.Icc 0 (1 / 10))
    (s : Fin (n + 1) → ℝ) (hs0 : s 0 = 0) (drift : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε16 : ε < 1 / 16)
    (htube : ∀ j, |removeLinearDrift drift s j - normalizedTime j / 2| < ε) :
    ∃ k : Fin n,
      (∀ j, cyclicPartialSum s k j - drift * (j.val : ℝ) ∈
        Set.Icc (-u) (1 - u)) ∧
      cyclicPartialSum s k (Fin.last n) - drift * (n : ℝ) ∈
        Set.Icc (1 / 3 - u) (2 / 3 - u) := by
  have hsdrift0 : removeLinearDrift drift s 0 = 0 := by
    simp [removeLinearDrift, hs0]
  obtain ⟨k, hk⟩ := exists_offsetCorridorPath_of_linearTube_lowerEdge
    hn hu (removeLinearDrift drift s) hsdrift0 hε hε16 htube
  refine ⟨k, ?_, ?_⟩
  · intro j
    have hj := hk.1 j
    exact cyclicPartialSum_mem_movingOffsetCorridor_of_removeLinearDrift
      s drift k hj
  · have hlast := hk.2
    change cyclicPartialSum (removeLinearDrift drift s) k (Fin.last n) ∈
      Set.Icc (1 / 3 - u) (2 / 3 - u) at hlast
    have heq := cyclicPartialSum_removeLinearDrift s drift k (Fin.last n)
    rw [Fin.val_last] at heq
    rw [← heq]
    exact hlast

/-- The decreasing-line version for offsets near the upper edge. -/
theorem exists_movingOffsetCorridor_of_linearTube_upperEdge
    {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : u ∈ Set.Icc (9 / 10) 1)
    (s : Fin (n + 1) → ℝ) (hs0 : s 0 = 0) (drift : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε16 : ε < 1 / 16)
    (htube : ∀ j, |removeLinearDrift drift s j + normalizedTime j / 2| < ε) :
    ∃ k : Fin n,
      (∀ j, cyclicPartialSum s k j - drift * (j.val : ℝ) ∈
        Set.Icc (-u) (1 - u)) ∧
      cyclicPartialSum s k (Fin.last n) - drift * (n : ℝ) ∈
        Set.Icc (1 / 3 - u) (2 / 3 - u) := by
  have hsdrift0 : removeLinearDrift drift s 0 = 0 := by
    simp [removeLinearDrift, hs0]
  obtain ⟨k, hk⟩ := exists_offsetCorridorPath_of_linearTube_upperEdge
    hn hu (removeLinearDrift drift s) hsdrift0 hε hε16 htube
  refine ⟨k, ?_, ?_⟩
  · intro j
    have hj := hk.1 j
    exact cyclicPartialSum_mem_movingOffsetCorridor_of_removeLinearDrift
      s drift k hj
  · have hlast := hk.2
    change cyclicPartialSum (removeLinearDrift drift s) k (Fin.last n) ∈
      Set.Icc (1 / 3 - u) (2 / 3 - u) at hlast
    have heq := cyclicPartialSum_removeLinearDrift s drift k (Fin.last n)
    rw [Fin.val_last] at heq
    rw [← heq]
    exact hlast

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
