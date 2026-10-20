/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Finite product bounds for measures

Iterated measure factorizations multiply lower bounds on each new factor. The
initial mass is retained explicitly, so the result applies to arbitrary
measures; probability measures are the specialization where the initial mass
is one.
-/

@[expose] public section

namespace MeasureTheory

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A finite intersection recurrence with each new factor of mass at least
`q` has mass at least `q ^ n` times the initial mass. -/
theorem mul_pow_le_measure_prefix_inter_of_factorization
    (pref nextEvent : ℕ → Set Ω) (q : ℝ≥0∞) (n : ℕ)
    (hrec : ∀ m < n, pref (m + 1) = pref m ∩ nextEvent m)
    (hfactor : ∀ m < n,
      μ (pref m ∩ nextEvent m) = μ (pref m) * μ (nextEvent m))
    (hlower : ∀ m < n, q ≤ μ (nextEvent m)) :
    q ^ n * μ (pref 0) ≤ μ (pref n) := by
  have hbound : ∀ m : ℕ, m ≤ n → q ^ m * μ (pref 0) ≤ μ (pref m) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp
    | succ m ih =>
        intro hm
        have hmn : m < n := by omega
        rw [hrec m hmn]
        calc
          q ^ (m + 1) * μ (pref 0) = q * (q ^ m * μ (pref 0)) := by
            rw [pow_succ']
            simp [mul_assoc]
          _ ≤ q * μ (pref m) := by
            exact mul_le_mul_of_nonneg_left (ih (by omega)) zero_le
          _ = μ (pref m) * q := mul_comm _ _
          _ ≤ μ (pref m) * μ (nextEvent m) :=
            mul_le_mul_of_nonneg_left (hlower m hmn) zero_le
          _ = μ (pref m ∩ nextEvent m) := (hfactor m hmn).symm
  exact hbound n le_rfl

end MeasureTheory

end
