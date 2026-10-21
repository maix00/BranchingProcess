/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Expansion
public import Analysis.SpecificLimits.Geometric

/-!
# Geometric upper bounds for killed-kernel row mass

This file combines the finite spectral expansion with the mode-depth estimate
to obtain the width-uniform geometric row-mass bound used by corridor proofs.
For $N>0$, let $K_N$ be the killed simple symmetric transition matrix and
$q_N=\cos(\pi/(N+1))$.  The public declarations are:

* `intervalKernel_pow_rowSum_le_geometric` proves, for every $t$ and start
  $i$, $\sum_j K_N^t(i,j)\le4\sum_{k=0}^{N-1}(q_N^t)^{k+1}$.
* `intervalKernel_pow_rowSum_le_four_mul_div_one_sub` proves, when $t>0$,
  $\sum_j K_N^t(i,j)\le4q_N^t/(1-q_N^t)$.
-/

open scoped Matrix
@[expose] public section

namespace ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

/-- The surviving row mass is bounded by a finite geometric progression in
the elapsed-time power of the principal eigenvalue.  Its prefactor is
independent of the interval width. -/
theorem intervalKernel_pow_rowSum_le_geometric {interiorCount : ℕ}
    (hcount : 0 < interiorCount) (n : ℕ) (start : Fin interiorCount) :
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
      4 * ∑ mode : Fin interiorCount,
        (Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^
          (mode.val + 1) := by
  exact (intervalKernel_pow_rowSum_le_two_mul_sum_absEigenvaluePow
    interiorCount n start).trans
      (sum_two_mul_abs_intervalModeEigenvalue_pow_le_geometric hcount n)

/-- Closed-form, width-uniform upper bound for the surviving row mass. -/
theorem intervalKernel_pow_rowSum_le_four_mul_div_one_sub
    {interiorCount n : ℕ} (hcount : 0 < interiorCount) (hn : 0 < n)
    (start : Fin interiorCount) :
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
      4 * (Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n /
        (1 - Real.cos (Real.pi /
          ((interiorCount + 1 : ℕ) : ℝ)) ^ n)) := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  have hwidth : (2 : ℝ) ≤ ((interiorCount + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hcount
  have hanglePos : 0 < Real.pi / ((interiorCount + 1 : ℕ) : ℝ) := by
    positivity
  have hangleLeHalf : Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ≤
      Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hwidth
  have hq₀ : 0 ≤ q := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith [Real.pi_pos]
    · exact hangleLeHalf
  have hq₁ : q < 1 := by
    have hanti := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith [Real.pi_pos])
      (show Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ∈
          Set.Icc 0 Real.pi by
        constructor
        · exact hanglePos.le
        · exact hangleLeHalf.trans (by linarith [Real.pi_pos]))
      hanglePos
    simpa [q] using hanti
  have hgeom := Finset.sum_range_pow_succ_le_div_one_sub
    (pow_nonneg hq₀ n) (pow_lt_one₀ hq₀ hq₁ hn.ne') interiorCount
  calc
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
        4 * ∑ mode : Fin interiorCount, (q ^ n) ^ (mode.val + 1) := by
      simpa [q] using intervalKernel_pow_rowSum_le_geometric hcount n start
    _ = 4 * ∑ i ∈ Finset.range interiorCount, (q ^ n) ^ (i + 1) := by
      congr 1
      simpa using (Fin.sum_univ_eq_sum_range
        (fun i => (q ^ n) ^ (i + 1)) interiorCount)
    _ ≤ 4 * (q ^ n / (1 - q ^ n)) :=
      mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ = _ := by rfl

end ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

end
