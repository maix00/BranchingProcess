/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Uniform grids on the unit time interval

The public definition and theorems in this file are:

- `ProbabilityTheory.unitIntervalGridTime`: the time $i/(n+1)$ for
  $i\in\{0,\ldots,n+1\}$.
- `ProbabilityTheory.unitIntervalGridTime_mono`: grid times increase
  with their indices.
- `ProbabilityTheory.unitIntervalGridTime_last`: the last grid time is $1$.
- `ProbabilityTheory.unitIntervalGridTime_dense`: for $0\le\tau\le1$ and
  $b>\tau$, sufficiently fine grids contain a point in $[\tau,b)$.

The grid supplies finite-valued stopping-time approximations in
Theorem 2.1 of S. J. Dilworth and Duncan Wright, *A direct proof of the
reflection principle for Brownian motion*, Theory Stoch. Process.
21(37):2 (2016), 1--3, arXiv:1810.01783.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- The $i$-th point of the uniform grid with mesh $1/(n+1)$ on $[0,1]$. -/
noncomputable def unitIntervalGridTime (n : ℕ) (i : Fin (n + 2)) : ℝ≥0 :=
  (i.val : ℝ≥0) / (n + 1 : ℕ)

/-- Uniform grid times increase with their indices. -/
theorem unitIntervalGridTime_mono (n : ℕ) : Monotone (unitIntervalGridTime n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

/-- The final time of the uniform unit-interval grid is $1$. -/
theorem unitIntervalGridTime_last (n : ℕ) :
    unitIntervalGridTime n (Fin.last (n + 1)) = 1 := by
  unfold unitIntervalGridTime
  simp

/-- For each $\tau\le1$ and $b>\tau$, all sufficiently fine grids
contain a point between $\tau$ and $b$. -/
theorem unitIntervalGridTime_dense (τ b : ℝ≥0) (hτ : τ ≤ 1) (hb : τ < b) :
    ∀ᶠ n in Filter.atTop, ∃ i : Fin (n + 2),
      τ ≤ unitIntervalGridTime n i ∧ unitIntervalGridTime n i < b := by
  have hmesh : Filter.Tendsto (fun n : ℕ => (1 : ℝ≥0) / (n + 1 : ℕ))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hδ : 0 < b - τ := tsub_pos_iff_lt.mpr hb
  filter_upwards [(tendsto_order.1 hmesh).2 (b - τ) hδ] with n hn
  let m : ℝ≥0 := (n + 1 : ℕ)
  have hmpos : 0 < m := by simp [m]
  let k : ℕ := Nat.ceil (τ * m)
  have hk_le : k ≤ n + 1 := by
    apply Nat.ceil_le.mpr
    have hmul : τ * m ≤ 1 * m := mul_le_mul_of_nonneg_right hτ (by positivity)
    simpa [m] using hmul
  let i : Fin (n + 2) := ⟨k, Nat.lt_succ_of_le hk_le⟩
  refine ⟨i, ?_, ?_⟩
  · change τ ≤ (k : ℝ≥0) / m
    exact (le_div_iff₀ hmpos).2 (Nat.le_ceil (τ * m))
  · have hk_lt : (k : ℝ≥0) < τ * m + 1 := Nat.ceil_lt_add_one (by positivity)
    have hgrid : (k : ℝ≥0) / m < τ + 1 / m := by
      apply (div_lt_iff₀ hmpos).2
      calc
        (k : ℝ≥0) < τ * m + 1 := hk_lt
        _ = (τ + 1 / m) * m := by field_simp
    have hsum : τ + 1 / m < b := by
      calc
        τ + 1 / m < τ + (b - τ) := by simpa [m] using add_lt_add_left hn τ
        _ = b := add_tsub_cancel_of_le hb.le
    exact hgrid.trans hsum

end ProbabilityTheory

end
