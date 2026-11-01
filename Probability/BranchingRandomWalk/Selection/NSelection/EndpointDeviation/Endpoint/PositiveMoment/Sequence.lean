/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.L2Closure

/-!
# Logarithmic-scale endpoint fourth moments

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_div_sub_integral_fourth_le_log_eighth`:
  if $H_n/(\log N_n)^3$ has a finite limit and $\log m_n\le a\log N_n$ eventually,
  and the leftmost child has a finite fourth moment, then for each fixed
  $c\in\mathbb R$ there is $C<\infty$ such that
  \[
    \mathbb E\!\left[
      \left(\frac{M_n}{\log N_n}-c\right)^4
    \right]\le C\bigl(1+(\log N_n)^8\bigr)
  \]
  eventually, where $M_n$ is the first-$N_n$ endpoint minimum from $m_n$
  initial roots at generation $H_n$.

The proof applies the fixed-horizon two-sided fourth-moment bound from
`PositiveMoment/L2Closure.lean` and controls its terms using the two
logarithmic scale hypotheses. This is the moment-growth input for the
arbitrary-scale polynomial-tail criterion in
`Probability/MeasureTheory/Convergence/SecondMoment/FromPolynomialTails.lean`.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk

/-- The centered, logarithmically normalized first-`N` endpoint has at most
eighth-power logarithmic growth of its fourth moment when the horizon is of
order `log N ^ 3` and the initial population has logarithmic size. -/
theorem eventually_countableRootEndpointMinimum_div_sub_integral_fourth_le_log_eighth
    {m N H : ℕ → ℕ}
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ))
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : HasLeftmostFourthMoment L)
    {a t c : ℝ}
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto
      (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hmPositive : ∀ᶠ n : ℕ in atTop, 0 < m n)
    (hlogm : ∀ᶠ n : ℕ in atTop,
      Real.log (m n : ℝ) ≤ a * Real.log (N n : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ field,
        (countableRootEndpointMinimum (m n) (N n) (H n) field /
          Real.log (N n : ℝ) - c) ^ 4
        ∂RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage) ≤
        C * (1 + Real.log (N n : ℝ) ^ 8) := by
  let fourthStep : ℝ :=
    ∫ ξ, (L.leftmostPositivePart ξ) ^ 4 ∂L.raw
  let coefficientH : ℝ := fourthStep * (t + 1) ^ 4
  let coefficientRest : ℝ := 2048 * (1 + a ^ 4) + c ^ 4
  let C : ℝ := 8 * (coefficientH + coefficientRest)
  have hfourthStep_nonneg : 0 ≤ fourthStep := by
    dsimp [fourthStep]
    exact integral_nonneg (fun ξ => by positivity)
  have hcoefficientH_nonneg : 0 ≤ coefficientH := by
    dsimp [coefficientH]
    positivity
  have hcoefficientRest_nonneg : 0 ≤ coefficientRest := by
    dsimp [coefficientRest]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hlogN : Tendsto (fun n => Real.log (N n : ℝ)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hN.eventually_gt_atTop 0
  have hparams : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (N n : ℝ) ∧
      (H n : ℝ) / Real.log (N n : ℝ) ^ 3 ≤ t + 1 ∧
      Real.log (m n : ℝ) ≤ a * Real.log (N n : ℝ) := by
    have hR := hlogN.eventually_ge_atTop (1 : ℝ)
    have hHr := hH.eventually (Iio_mem_nhds (by linarith : t < t + 1))
    filter_upwards [hR, hHr, hlogm] with n hR hHr hlogm_n
    exact ⟨hR, hHr.le, hlogm_n⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hparams, hmPositive, hNpos] with n ⟨hRge1, hHratio, hlogm_n⟩ hm hNn
  let _ := horder n
  have hRpos : 0 < Real.log (N n : ℝ) := lt_of_lt_of_le (by norm_num) hRge1
  have hlogm_nonneg : 0 ≤ Real.log (m n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))
  have hHratio_nonneg : 0 ≤ (H n : ℝ) / Real.log (N n : ℝ) ^ 3 := by
    positivity
  have hHdiv_eq :
      (H n : ℝ) / Real.log (N n : ℝ) =
        ((H n : ℝ) / Real.log (N n : ℝ) ^ 3) *
          Real.log (N n : ℝ) ^ 2 := by
    field_simp [ne_of_gt hRpos]
  have hHdiv :
      (H n : ℝ) / Real.log (N n : ℝ) ≤
        (t + 1) * Real.log (N n : ℝ) ^ 2 := by
    rw [hHdiv_eq]
    exact mul_le_mul_of_nonneg_right hHratio (sq_nonneg _)
  have hHpow :
      ((H n : ℝ) / Real.log (N n : ℝ)) ^ 4 ≤
        (t + 1) ^ 4 * Real.log (N n : ℝ) ^ 8 := by
    calc
      ((H n : ℝ) / Real.log (N n : ℝ)) ^ 4 ≤
          ((t + 1) * Real.log (N n : ℝ) ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hHdiv 4
      _ = (t + 1) ^ 4 * Real.log (N n : ℝ) ^ 8 := by ring
  have hlogm_div :
      Real.log (m n : ℝ) / Real.log (N n : ℝ) ≤ a :=
    (div_le_iff₀ hRpos).2 (by simpa [mul_comm] using hlogm_n)
  have hlogm_div_nonneg :
      0 ≤ Real.log (m n : ℝ) / Real.log (N n : ℝ) :=
    div_nonneg hlogm_nonneg (le_of_lt hRpos)
  have hlogm_pow :
      (Real.log (m n : ℝ) / Real.log (N n : ℝ)) ^ 4 ≤ a ^ 4 :=
    pow_le_pow_left₀ hlogm_div_nonneg hlogm_div 4
  have hinv : (1 : ℝ) / Real.log (N n : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hRpos).2
    linarith
  have hinv_pow : ((1 : ℝ) / Real.log (N n : ℝ)) ^ 4 ≤ 1 := by
    calc
      ((1 : ℝ) / Real.log (N n : ℝ)) ^ 4 ≤ 1 ^ 4 :=
        pow_le_pow_left₀ (by positivity) hinv 4
      _ = 1 := by norm_num
  have hfixed :=
    countableRootEndpointMinimum_div_sub_memLp_four_and_integral_bound
      (m n) (N n) (H n) hm hNn L hboundary hnonempty hfour
      (Real.log (N n : ℝ)) c hRpos.ne'
  have hidentity :
      8 * ((H n : ℝ) ^ 4 * fourthStep +
        2048 * (1 + Real.log (m n : ℝ) ^ 4) +
        (c * Real.log (N n : ℝ)) ^ 4) /
          Real.log (N n : ℝ) ^ 4 =
      8 * (((H n : ℝ) / Real.log (N n : ℝ)) ^ 4 * fourthStep +
        2048 * (((1 : ℝ) / Real.log (N n : ℝ)) ^ 4 +
          (Real.log (m n : ℝ) / Real.log (N n : ℝ)) ^ 4) + c ^ 4) := by
    field_simp [ne_of_gt hRpos]
  have hbase :
      ((H n : ℝ) / Real.log (N n : ℝ)) ^ 4 * fourthStep +
        2048 * (((1 : ℝ) / Real.log (N n : ℝ)) ^ 4 +
          (Real.log (m n : ℝ) / Real.log (N n : ℝ)) ^ 4) + c ^ 4 ≤
      coefficientH * Real.log (N n : ℝ) ^ 8 + coefficientRest := by
    have hfirst := mul_le_mul_of_nonneg_right hHpow hfourthStep_nonneg
    have hsecond :
        2048 * (((1 : ℝ) / Real.log (N n : ℝ)) ^ 4 +
          (Real.log (m n : ℝ) / Real.log (N n : ℝ)) ^ 4) + c ^ 4 ≤
        2048 * (1 + a ^ 4) + c ^ 4 := by
      gcongr
    dsimp [coefficientH, coefficientRest]
    linarith
  have hbase_to_C :
      coefficientH * Real.log (N n : ℝ) ^ 8 + coefficientRest ≤
        (coefficientH + coefficientRest) *
          (1 + Real.log (N n : ℝ) ^ 8) := by
    have hlogpow_nonneg : 0 ≤ Real.log (N n : ℝ) ^ 8 := by positivity
    have hfirst : coefficientH * Real.log (N n : ℝ) ^ 8 ≤
        (coefficientH + coefficientRest) * Real.log (N n : ℝ) ^ 8 :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right hcoefficientRest_nonneg) hlogpow_nonneg
    have hsecond : coefficientRest ≤ coefficientH + coefficientRest :=
      le_add_of_nonneg_left hcoefficientH_nonneg
    calc
      coefficientH * Real.log (N n : ℝ) ^ 8 + coefficientRest ≤
          (coefficientH + coefficientRest) * Real.log (N n : ℝ) ^ 8 +
            (coefficientH + coefficientRest) := add_le_add hfirst hsecond
      _ = (coefficientH + coefficientRest) *
          (1 + Real.log (N n : ℝ) ^ 8) := by ring
  calc
    (∫ field,
        (countableRootEndpointMinimum (m n) (N n) (H n) field /
          Real.log (N n : ℝ) - c) ^ 4
        ∂RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage) ≤
      8 * ((H n : ℝ) ^ 4 * fourthStep +
        2048 * (1 + Real.log (m n : ℝ) ^ 4) +
        (c * Real.log (N n : ℝ)) ^ 4) /
          Real.log (N n : ℝ) ^ 4 := hfixed.2
    _ = 8 * (((H n : ℝ) / Real.log (N n : ℝ)) ^ 4 * fourthStep +
        2048 * (((1 : ℝ) / Real.log (N n : ℝ)) ^ 4 +
          (Real.log (m n : ℝ) / Real.log (N n : ℝ)) ^ 4) + c ^ 4) :=
      hidentity
    _ ≤ 8 * (coefficientH * Real.log (N n : ℝ) ^ 8 + coefficientRest) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ ≤ C * (1 + Real.log (N n : ℝ) ^ 8) := by
      calc
        8 * (coefficientH * Real.log (N n : ℝ) ^ 8 + coefficientRest) ≤
            8 * ((coefficientH + coefficientRest) *
              (1 + Real.log (N n : ℝ) ^ 8)) :=
          mul_le_mul_of_nonneg_left hbase_to_C (by norm_num)
        _ = C * (1 + Real.log (N n : ℝ) ^ 8) := by ring

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
