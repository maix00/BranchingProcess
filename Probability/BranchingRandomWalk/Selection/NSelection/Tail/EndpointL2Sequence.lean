/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointL2Closure
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.SelectedEndpointSublevel

/-!
# Logarithmic-scale endpoint fourth moments

This module converts the fixed-horizon endpoint moment estimate to the
logarithmic horizon used in the trajectory theorem. It is an intermediate
sequence estimate: the final theorem adapter derives its scale bounds from the
paper's parameters.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris

/-- A horizon asymptotic to `t * log N ^ 3` gives logarithmic-eighth growth of
the centered, normalized endpoint fourth moment. The positive-integer and
population-size bounds are supplied separately so that final theorem
adapters can derive them from their displayed parameters. -/
theorem countableRootEndpointMinimum_div_sub_fourthMoment_eventually_le_log_eighth
    {m N H : ℕ → ℕ} {t : ℝ}
    (hm : ∀ n, 0 < m n)
    (hNlarge : ∀ n, 1 < N n)
    (hm_le : ∀ n, m n ≤ N n)
    (hN : Tendsto N atTop atTop)
    (ht : 0 < t)
    (hH : Tendsto
      (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3)
      atTop (𝓝 t))
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : HasLeftmostFourthMoment L) (c : ℝ) :
    (∀ n, MemLp
      (fun field => @countableRootEndpointMinimum (m n) (N n) (H n)
          (root_address_linear_order (m n)) field /
          Real.log (N n : ℝ) - c)
      (4 : ℝ≥0∞)
      (RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ field,
        (@countableRootEndpointMinimum (m n) (N n) (H n)
          (root_address_linear_order (m n)) field /
          Real.log (N n : ℝ) - c) ^ 4
        ∂RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage) ≤
        C * (1 + Real.log (N n : ℝ) ^ 8) := by
  let μ := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
  let A : ℝ := ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw
  have hA_nonneg : 0 ≤ A := by
    exact integral_nonneg (fun ξ => by positivity)
  have hNcast : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hlog : Tendsto (fun n => Real.log (N n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNcast
  have hlog_ge_one : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (N n : ℝ) := hlog.eventually_ge_atTop 1
  have hratio_lt : ∀ᶠ n : ℕ in atTop,
      (H n : ℝ) / Real.log (N n : ℝ) ^ 3 < t + 1 :=
    hH.eventually (Iio_mem_nhds (by linarith))
  have hmem : ∀ n, MemLp
      (fun field => @countableRootEndpointMinimum (m n) (N n) (H n)
          (root_address_linear_order (m n)) field /
          Real.log (N n : ℝ) - c)
      (4 : ℝ≥0∞) μ := by
    intro n
    letI : LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ) :=
      root_address_linear_order (m n)
    have hNpos : 0 < N n := Nat.lt_trans Nat.zero_lt_one (hNlarge n)
    have hlogpos : 0 < Real.log (N n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hNlarge n)
    exact (countableRootEndpointMinimum_div_sub_memLp_four_and_integral_bound
      (m n) (N n) (H n) (hm n) hNpos L hboundary hnonempty hfour
      (Real.log (N n : ℝ)) c (ne_of_gt hlogpos)).1
  let K : ℝ := t + 1
  let C : ℝ := 8 * (K ^ 4 * A + 4096 + c ^ 4)
  have hK_nonneg : 0 ≤ K := by dsimp [K]; linarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound : ∀ᶠ n : ℕ in atTop,
      (∫ field,
        (@countableRootEndpointMinimum (m n) (N n) (H n)
          (root_address_linear_order (m n)) field /
          Real.log (N n : ℝ) - c) ^ 4 ∂μ) ≤
        C * (1 + Real.log (N n : ℝ) ^ 8) := by
    filter_upwards [hlog_ge_one, hratio_lt] with n hnlog hnratio
    letI : LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ) :=
      root_address_linear_order (m n)
    let s : ℝ := Real.log (N n : ℝ)
    have hs_ge_one : 1 ≤ s := hnlog
    have hs_pos : 0 < s := by linarith
    have hs4_pos : 0 < s ^ 4 := pow_pos hs_pos 4
    have hs4_ge_one : 1 ≤ s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 1)]
    have hs8_ge_one : 1 ≤ s ^ 8 := by nlinarith [sq_nonneg (s ^ 4 - 1)]
    have hmpos : 0 < (m n : ℝ) := by exact_mod_cast hm n
    have hlogm_le : Real.log (m n : ℝ) ≤ s := by
      dsimp [s]
      exact Real.log_le_log hmpos (by exact_mod_cast hm_le n)
    have hH_le : (H n : ℝ) ≤ K * s ^ 3 := by
      have hmul := (div_lt_iff₀ (pow_pos hs_pos 3)).mp hnratio
      dsimp [K, s]
      linarith
    have hH_nonneg : 0 ≤ (H n : ℝ) := Nat.cast_nonneg _
    have hlogm_nonneg : 0 ≤ Real.log (m n : ℝ) :=
      Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hm n))))
    have hlogm4_le : (Real.log (m n : ℝ)) ^ 4 ≤ s ^ 4 :=
      pow_le_pow_left₀ hlogm_nonneg hlogm_le 4
    have hfirst : (H n : ℝ) ^ 4 * A / s ^ 4 ≤ K ^ 4 * A * s ^ 8 := by
      apply (div_le_iff₀ hs4_pos).2
      calc
        (H n : ℝ) ^ 4 * A ≤ (K * s ^ 3) ^ 4 * A :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hH_nonneg hH_le 4) hA_nonneg
        _ = (K ^ 4 * A * s ^ 8) * s ^ 4 := by ring
    have hsecond :
        2048 * (1 + (Real.log (m n : ℝ)) ^ 4) / s ^ 4 ≤ 4096 := by
      apply (div_le_iff₀ hs4_pos).2
      have hinside : 1 + (Real.log (m n : ℝ)) ^ 4 ≤ 1 + s ^ 4 :=
        add_le_add le_rfl hlogm4_le
      nlinarith [hinside, hs4_ge_one]
    have hNpos : 0 < N n := Nat.lt_trans Nat.zero_lt_one (hNlarge n)
    have hmoment :=
      countableRootEndpointMinimum_div_sub_memLp_four_and_integral_bound
        (m n) (N n) (H n) (hm n) hNpos L hboundary hnonempty hfour
        s c (ne_of_gt hs_pos)
    have hmomentBound := hmoment.2
    have hdecomp :
        ((H n : ℝ) ^ 4 * A +
          2048 * (1 + Real.log (m n : ℝ) ^ 4) + (c * s) ^ 4) / s ^ 4 =
        (H n : ℝ) ^ 4 * A / s ^ 4 +
          2048 * (1 + Real.log (m n : ℝ) ^ 4) / s ^ 4 + c ^ 4 := by
      field_simp [ne_of_gt hs_pos]
    have hmomentBound :
        (∫ field,
          (countableRootEndpointMinimum (m n) (N n) (H n) field / s - c) ^ 4
            ∂μ) ≤
        8 * ((H n : ℝ) ^ 4 * A +
          2048 * (1 + Real.log (m n : ℝ) ^ 4) + (c * s) ^ 4) / s ^ 4 := by
      simpa [A, μ] using hmoment.2
    have hmoment' :
        (∫ field,
          (countableRootEndpointMinimum (m n) (N n) (H n) field / s - c) ^ 4
            ∂μ) ≤
        8 * ((H n : ℝ) ^ 4 * A / s ^ 4 +
          2048 * (1 + Real.log (m n : ℝ) ^ 4) / s ^ 4 + c ^ 4) := by
      have hnormalized :
          (∫ field,
            (countableRootEndpointMinimum (m n) (N n) (H n) field / s - c) ^ 4
              ∂μ) ≤
          8 * (((H n : ℝ) ^ 4 * A +
            2048 * (1 + Real.log (m n : ℝ) ^ 4) + (c * s) ^ 4) / s ^ 4) := by
        calc
          _ ≤ 8 * ((H n : ℝ) ^ 4 * A +
              2048 * (1 + Real.log (m n : ℝ) ^ 4) + (c * s) ^ 4) / s ^ 4 :=
            hmomentBound
          _ = 8 * (((H n : ℝ) ^ 4 * A +
              2048 * (1 + Real.log (m n : ℝ) ^ 4) + (c * s) ^ 4) / s ^ 4) := by ring
      rw [hdecomp] at hnormalized
      exact hnormalized
    have hsmall :
        (H n : ℝ) ^ 4 * A / s ^ 4 +
          2048 * (1 + Real.log (m n : ℝ) ^ 4) / s ^ 4 + c ^ 4 ≤
        K ^ 4 * A * s ^ 8 + 4096 + c ^ 4 := by
      linarith [hfirst, hsecond]
    have hlarge :
        8 * (K ^ 4 * A * s ^ 8 + 4096 + c ^ 4) ≤ C * (1 + s ^ 8) := by
      have hB : 0 ≤ K ^ 4 * A := by positivity
      have hD : 0 ≤ (4096 : ℝ) + c ^ 4 := by positivity
      have hBmul : K ^ 4 * A * s ^ 8 ≤
          K ^ 4 * A * (1 + s ^ 8) :=
        mul_le_mul_of_nonneg_left (by linarith) hB
      have hDmul : 4096 + c ^ 4 ≤
          (4096 + c ^ 4) * (1 + s ^ 8) := by
        calc
          4096 + c ^ 4 = (4096 + c ^ 4) * 1 := by ring
          _ ≤ (4096 + c ^ 4) * (1 + s ^ 8) :=
            mul_le_mul_of_nonneg_left (by linarith) hD
      have hsum : K ^ 4 * A * s ^ 8 + (4096 + c ^ 4) ≤
          K ^ 4 * A * (1 + s ^ 8) +
            (4096 + c ^ 4) * (1 + s ^ 8) :=
        add_le_add hBmul hDmul
      calc
        8 * (K ^ 4 * A * s ^ 8 + 4096 + c ^ 4) ≤
            8 * (K ^ 4 * A * (1 + s ^ 8) +
              (4096 + c ^ 4) * (1 + s ^ 8)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hsum]) (by norm_num)
        _ = C * (1 + s ^ 8) := by dsimp [C]; ring
    calc
      (∫ field,
          (countableRootEndpointMinimum (m n) (N n) (H n) field / s - c) ^ 4
            ∂μ) ≤
          8 * (K ^ 4 * A * s ^ 8 + 4096 + c ^ 4) := by
            exact hmoment'.trans
              (mul_le_mul_of_nonneg_left hsmall (by norm_num))
      _ ≤ C * (1 + s ^ 8) := hlarge
  refine ⟨?_, ?_⟩
  · simpa [μ] using hmem
  · refine ⟨C, hC_nonneg, ?_⟩
    simpa [μ] using hbound

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
