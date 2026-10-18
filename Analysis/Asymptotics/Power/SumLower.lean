/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A lower bound for a finite power sum

The public theorem in this file is:

- `Asymptotics.rpow_sum_lower`: for $0<\gamma\le1$ and $m\in\mathbb N$,
  $((m+2)^\gamma-1)/\gamma\le
  \sum_{k=0}^{m}(k+1)^{\gamma-1}$.

The proof compares the sum with the integral of the decreasing function
$x\mapsto x^{\gamma-1}$ on $[1,m+2]$.
-/

@[expose] public section

namespace Asymptotics

/-- The left Riemann sum for $x^{\gamma-1}$ dominates its integral on
$[1,m+2]$ when $0<\gamma\le1$. -/
theorem rpow_sum_lower {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (m : ℕ) :
    (((m + 2 : ℕ) : ℝ) ^ γ - 1) / γ ≤
      ∑ k ∈ Finset.range (m + 1), (((k + 1 : ℕ) : ℝ) ^ (γ - 1)) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (γ - 1))
      (Set.Icc 1 ((m + 2 : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
      (by intro x hx; exact lt_of_lt_of_le zero_lt_one hx.1)
  have hbound := (show AntitoneOn (fun x : ℝ => x ^ (γ - 1))
      (Set.Icc (↑(1 : ℕ)) (↑(m + 2 : ℕ))) by simpa using hanti).integral_le_sum_Ico
        (show 1 ≤ m + 2 by omega)
  rw [integral_rpow (Or.inl (by linarith : -1 < γ - 1))] at hbound
  convert hbound using 1
  · simp
  · rw [Finset.sum_Ico_eq_sum_range]
    have hm : m + 2 - 1 = m + 1 := by omega
    simp [hm, Nat.add_comm]

end Asymptotics

end
