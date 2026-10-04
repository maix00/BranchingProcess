/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite corridor covers for real-valued functions

This file contains the order-theoretic part of a finite range cover. It uses
only a distinguished zero value and a uniform bound on pairwise differences;
the index type carries no topology or probability structure.
-/

@[expose] public section

namespace Order.Bounds

/-- A zero-based function with range diameter strictly less than `2`. -/
def UnitRangeTube {T : Type*} (root : T) (f : T → ℝ) : Prop :=
  f root = 0 ∧ ∃ margin > 0, ∀ s t, |f s - f t| ≤ 2 - margin

/-- A function lies uniformly inside an interval. -/
def UniformCorridor {T : Type*} (f : T → ℝ) (lower upper : ℝ) : Prop :=
  ∃ margin > 0, ∀ t, lower + margin ≤ f t ∧ f t ≤ upper - margin

/-- A unit range tube is covered by finitely many translated corridors. This
is a statement about functions on an arbitrary index type, not just paths. -/
theorem unitRangeTube_exists_corridor
    {T : Type*} (root : T) (f : T → ℝ)
    (k : ℕ) (hk : 0 < k) (hf : UnitRangeTube root f) :
    ∃ j ∈ Finset.range (2 * k + 1),
      UniformCorridor f
        (((j : ℝ) / k - 1) - (1 + 2 / k))
        (((j : ℝ) / k - 1) + (1 + 2 / k)) := by
  obtain ⟨hzero, margin, hmargin, hosc⟩ := hf
  have hupper : ∀ t, f t ≤ 2 - margin := by
    intro t
    have h := hosc t root
    rw [hzero, sub_zero, abs_le] at h
    linarith [h.2]
  have hbounded : BddAbove (Set.range f) := ⟨2 - margin, by
    rintro y ⟨t, rfl⟩
    exact hupper t⟩
  have hnonempty : (Set.range f).Nonempty := ⟨f root, ⟨root, rfl⟩⟩
  let U : ℝ := sSup (Set.range f)
  have hUpos : 0 ≤ U := by
    rw [← hzero]
    exact le_csSup hbounded ⟨root, rfl⟩
  have hUtop : U ≤ 2 - margin :=
    csSup_le hnonempty (by rintro y ⟨t, rfl⟩; exact hupper t)
  have hU : ∀ t, f t ≤ U := fun t => le_csSup hbounded ⟨t, rfl⟩
  have hUlower : ∀ t, U - (2 - margin) ≤ f t := by
    intro t
    have hbdd : ∀ s, f s ≤ f t + (2 - margin) := by
      intro s
      have h := hosc s t
      have hs := (abs_le.mp h).2
      linarith
    have hsup : U ≤ f t + (2 - margin) := by
      apply csSup_le hnonempty
      rintro y ⟨s, rfl⟩
      exact hbdd s
    linarith
  let j : ℕ := Nat.floor ((k : ℝ) * U)
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnonneg : 0 ≤ (k : ℝ) * U := mul_nonneg hkreal.le hUpos
  have hjlow : (j : ℝ) ≤ (k : ℝ) * U := Nat.floor_le hnonneg
  have hjhigh : (k : ℝ) * U < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjbound : j < 2 * k + 1 := by
    have hcast : (j : ℝ) < (2 * k + 1 : ℕ) := by
      push_cast
      nlinarith [hUtop, mul_pos hkreal hmargin]
    exact_mod_cast hcast
  refine ⟨j, Finset.mem_range.mpr hjbound, ?_⟩
  let m : ℝ := min (margin / 2) (1 / (2 * (k : ℝ)))
  have hm : 0 < m := lt_min (half_pos hmargin) (one_div_pos.mpr (by positivity))
  have hmMargin : m ≤ margin / 2 := min_le_left _ _
  have hmGrid : m ≤ 1 / (2 * (k : ℝ)) := min_le_right _ _
  have hmGrid' : m ≤ 1 / (k : ℝ) := by
    have hhalf : 1 / (2 * (k : ℝ)) = (1 / (k : ℝ)) / 2 := by ring
    rw [hhalf] at hmGrid
    have hpos : 0 ≤ 1 / (k : ℝ) := (one_div_pos.mpr hkreal).le
    linarith
  refine ⟨m, hm, ?_⟩
  intro t
  have hl := hUlower t
  have hu := hU t
  have hgridLow : (j : ℝ) / k ≤ U := (div_le_iff₀ hkreal).2 (by simpa [mul_comm] using hjlow)
  have hgridHigh : U < (j : ℝ) / k + 1 / k := by
    have h : U < ((j : ℝ) + 1) / k :=
      (lt_div_iff₀ hkreal).2 (by nlinarith [hjhigh])
    convert h using 1
    ring
  have htwo : 2 / (k : ℝ) = 2 * (1 / (k : ℝ)) := by ring
  constructor
  · rw [htwo]
    nlinarith [hmGrid', hgridLow, hl, one_div_pos.mpr hkreal]
  · rw [htwo]
    nlinarith [hmGrid', hgridHigh, hu, one_div_pos.mpr hkreal]

end Order.Bounds

end
