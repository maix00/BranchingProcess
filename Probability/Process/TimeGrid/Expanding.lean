/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Expanding uniform observation grids

The public declarations in this file are:

- `ProbabilityTheory.expandingGridCount`:
  $N_n=(n+1)^2$.
- `ProbabilityTheory.expandingGridTime`:
  $r_n(i)=i/(n+1)$ for $0\le i\le N_n$.
- `ProbabilityTheory.expandingGridTime_mono`:
  $i\le j\Rightarrow r_n(i)\le r_n(j)$.
- `ProbabilityTheory.expandingGridTime_last`:
  $r_n(N_n)=n+1$.
- `ProbabilityTheory.expandingGridTime_eventually_cover`:
  every finite $\tau$ eventually lies before the last grid point.
- `ProbabilityTheory.expandingGridTime_dense`:
  every $[\tau,b)$ with $\tau<b$ eventually contains a grid point.

The grids approximate finite Brownian first-passage times in the
strong-Markov step used by the Lévy decomposition cited in Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.3, equation (2.2), Ann.
Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter
open scoped NNReal

/-- Number of intervals in the expanding grid of mesh `1/(n+1)`. -/
def expandingGridCount (n : ℕ) : ℕ := (n + 1) ^ 2

/-- The `i`-th observation time on `[0,n+1]`. -/
noncomputable def expandingGridTime (n : ℕ)
    (i : Fin (expandingGridCount n + 1)) : ℝ≥0 :=
  (i.val : ℝ≥0) / (n + 1 : ℕ)

/-- Grid times increase with the index. -/
theorem expandingGridTime_mono (n : ℕ) :
    Monotone (expandingGridTime n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

/-- The last observation time is `n+1`. -/
theorem expandingGridTime_last (n : ℕ) :
    expandingGridTime n (Fin.last (expandingGridCount n)) = n + 1 := by
  unfold expandingGridTime expandingGridCount
  simp [pow_two, mul_div_cancel_right₀]

/-- Every finite time eventually falls within the expanding grid. -/
theorem expandingGridTime_eventually_cover (τ : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop,
      τ ≤ expandingGridTime n (Fin.last (expandingGridCount n)) := by
  obtain ⟨m, hm⟩ := exists_nat_ge τ
  filter_upwards [eventually_ge_atTop m] with n hmn
  rw [expandingGridTime_last]
  exact hm.trans (by exact_mod_cast Nat.le_succ_of_le hmn)

/-- Any interval strictly to the right of a finite time eventually
contains an observation time. -/
theorem expandingGridTime_dense (τ b : ℝ≥0) (hb : τ < b) :
    ∀ᶠ n : ℕ in atTop,
      ∃ i : Fin (expandingGridCount n + 1),
        τ ≤ expandingGridTime n i ∧ expandingGridTime n i < b := by
  have hmesh : Tendsto (fun n : ℕ => (1 : ℝ≥0) / (n + 1 : ℕ))
      atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hδ : 0 < b - τ := tsub_pos_iff_lt.mpr hb
  filter_upwards [expandingGridTime_eventually_cover τ,
    (tendsto_order.1 hmesh).2 (b - τ) hδ] with n hcover hn
  let m : ℝ≥0 := (n + 1 : ℕ)
  have hmpos : 0 < m := by simp [m]
  have hτbound : τ ≤ m := by
    simpa [m, expandingGridTime_last] using hcover
  let k : ℕ := Nat.ceil (τ * m)
  have hk_le : k ≤ expandingGridCount n := by
    apply Nat.ceil_le.mpr
    have hmul : τ * m ≤ m * m := mul_le_mul_of_nonneg_right hτbound (by positivity)
    simpa [expandingGridCount, m, pow_two] using hmul
  let i : Fin (expandingGridCount n + 1) := ⟨k, Nat.lt_succ_of_le hk_le⟩
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
