/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Basic
public import Probability.Process.RandomWalk.Rademacher
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Integer coordinates of Rademacher paths

The range estimate covers a Rademacher path by translated lattice intervals.
This file records the integer-lattice and linear-growth facts needed for
that finite cover.
-/

open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Integer version of a Boolean Rademacher increment. -/
def rademacherIntIncrement (branch : Bool) : ℤ :=
  if branch then 1 else -1

@[simp]
theorem rademacherOfBool_eq_intCast (branch : Bool) :
    ProbabilityTheory.rademacherOfBool branch =
      (rademacherIntIncrement branch : ℝ) := by
  cases branch <;> simp [rademacherIntIncrement,
    ProbabilityTheory.rademacherOfBool]

/-- The canonical partial sum of the project's Rademacher increment path. -/
abbrev rademacherPartialSum (n : ℕ) (branch : ℕ → Bool) : ℝ :=
  Combinatorics.Branching.Walk.partialSum n
    (ProbabilityTheory.RandomWalk.rademacherIncrementPath branch)

/-- The real partial sum is the cast of an integer lattice sum. -/
theorem rademacherPartialSum_eq_intCast
    (n : ℕ) (branch : ℕ → Bool) :
    rademacherPartialSum n branch =
      (∑ k ∈ Finset.range n, rademacherIntIncrement (branch k) : ℤ) := by
  simp only [rademacherPartialSum, Combinatorics.Branching.Walk.partialSum,
    ProbabilityTheory.RandomWalk.rademacherIncrementPath]
  simp only [rademacherOfBool_eq_intCast]
  norm_cast

@[simp]
theorem rademacherPartialSum_zero (branch : ℕ → Bool) :
    rademacherPartialSum 0 branch = 0 := by
  simp [rademacherPartialSum]

theorem rademacherPartialSum_succ (n : ℕ) (branch : ℕ → Bool) :
    rademacherPartialSum (n + 1) branch =
      rademacherPartialSum n branch +
        ProbabilityTheory.rademacherOfBool (branch n) := by
  rw [rademacherPartialSum, Combinatorics.Branching.Walk.partialSum_succ]
  rfl

/-- A length-`n` Rademacher partial sum lies in the lattice interval
`[-n,n]`. -/
theorem abs_rademacherRealPartialSum_le
    (n : ℕ) (branch : ℕ → Bool) :
    |rademacherPartialSum n branch| ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rademacherPartialSum_succ]
      have hstep :
          |ProbabilityTheory.rademacherOfBool (branch n)| = 1 := by
        cases branch n <;> simp [ProbabilityTheory.rademacherOfBool]
      calc
        |rademacherPartialSum n branch +
            ProbabilityTheory.rademacherOfBool (branch n)| ≤
            |rademacherPartialSum n branch| +
              |ProbabilityTheory.rademacherOfBool (branch n)| := abs_add_le _ _
        _ ≤ (n : ℝ) + 1 := add_le_add ih hstep.le
        _ = (↑(n + 1) : ℝ) := by norm_cast

/-- Finite-time range event for a Boolean Rademacher path. -/
def RademacherOscillationBounded (n : ℕ) (width : ℝ)
    (branch : ℕ → Bool) : Prop :=
  ∀ i j : Fin (n + 1),
    |rademacherPartialSum (i : ℕ) branch -
      rademacherPartialSum (j : ℕ) branch| ≤ width

/-- Any Rademacher path with range at most an integer `width` fits in one of
the `width + 1` translates of the standard lattice interval.  Its shift is
minus the path minimum, which is an integer because every partial sum is. -/
theorem exists_shift_of_rademacherOscillation
    (n width : ℕ) (branch : ℕ → Bool)
    (hosc : RademacherOscillationBounded n width branch) :
  ∃ shift : Fin (width + 1), ∀ k : Fin (n + 1),
      ((shift : Fin (width + 1)).val : ℝ) +
        rademacherPartialSum (k : ℕ) branch ∈
          Set.Icc (0 : ℝ) (width : ℝ) := by
  let position : Fin (n + 1) → ℝ := fun k =>
    rademacherPartialSum (k : ℕ) branch
  let zero : Fin (n + 1) := ⟨0, by omega⟩
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ position
    ⟨zero, Finset.mem_univ _⟩
  have hminZero : position imin ≤ 0 := by
    have h := hmin zero (Finset.mem_univ _)
    simpa [position, zero, rademacherPartialSum_zero] using h
  let z : ℤ := ∑ k ∈ Finset.range (imin : ℕ),
    rademacherIntIncrement (branch k)
  have hz : (z : ℝ) = position imin := by
    dsimp [z, position]
    rw [rademacherPartialSum_eq_intCast]
  have hzNonpos : z ≤ 0 := by
    have hreal : (z : ℝ) ≤ 0 := by rw [hz]; exact hminZero
    exact_mod_cast hreal
  have hoscZero := hosc imin zero
  have hnegzLe : -(z : ℝ) ≤ width := by
    have hminAbs : |position imin| ≤ width := by
      simpa [position, zero, rademacherPartialSum_zero,
        abs_sub_comm] using hoscZero
    rw [abs_of_nonpos hminZero] at hminAbs
    rw [hz]
    exact hminAbs
  have htoNat : ((Int.toNat (-z) : ℕ) : ℝ) = -(z : ℝ) := by
    have hnonneg : 0 ≤ -z := by omega
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have htoNatLe : Int.toNat (-z) ≤ width := by
    have hreal : ((Int.toNat (-z) : ℕ) : ℝ) ≤ width := by
      rw [htoNat]
      exact hnegzLe
    exact_mod_cast hreal
  let shift : Fin (width + 1) :=
    ⟨Int.toNat (-z), Nat.lt_succ_of_le htoNatLe⟩
  have hshift : (shift.val : ℝ) = -(z : ℝ) := by
    simp [shift, htoNat]
  refine ⟨shift, ?_⟩
  intro t
  have hminT : (z : ℝ) ≤ position t := by
    have h := hmin t (Finset.mem_univ _)
    rw [← hz] at h
    exact h
  have hoscT : |position t - (z : ℝ)| ≤ width := by
    have h := hosc t imin
    change |position t - position imin| ≤ width at h
    rw [← hz] at h
    exact h
  have hdiff : position t - (z : ℝ) ≤ width := by
    have hnonneg : 0 ≤ position t - (z : ℝ) := sub_nonneg.mpr hminT
    rw [abs_of_nonneg hnonneg] at hoscT
    exact hoscT
  rw [hshift]
  constructor <;> nlinarith [hminT, hdiff]

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
