/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.Normed.Group.Completeness
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Topology.Cadlag.Skorokhod.TimeChange.Sequence

/-!
# Uniform limits of cumulative time changes

Summably small logarithmic distortions make the cumulative time changes
uniformly Cauchy. This file constructs their continuous uniform limit; strict
monotonicity of the limit is treated separately.
-/

@[expose] public section

open Filter
open scoped NNReal

namespace Skorokhod

namespace TimeChange

private theorem cumulative_dist_le_exp_tail
    (clocks : ℕ → TimeChange) (error : ℕ → ℝ≥0)
    (hstep : ∀ n, (clocks n).logDistortion ≤ error n)
    (herror : Summable error)
    (n m : ℕ) (hnm : n ≤ m) :
    dist (cumulative clocks m).toContinuousMap (cumulative clocks n).toContinuousMap ≤
      Real.exp ((∑' k, error (n + k) : ℝ≥0) : ℝ) -
        Real.exp (-((∑' k, error (n + k) : ℝ≥0) : ℝ)) := by
  let suffix := segment clocks n (m - n)
  let tail := ∑' k, error (n + k : ℕ)
  have hdecomp : cumulative clocks m = (cumulative clocks n).trans suffix := by
    have hmn' : n + (m - n) = m := Nat.add_sub_of_le hnm
    rw [← hmn']
    exact cumulative_add_eq_trans_segment clocks n (m - n)
  have hsummable : Summable fun k => error (n + k) := by
    simpa only [Nat.add_comm] using NNReal.summable_nat_add error herror n
  have hlog : suffix.logDistortion ≤ ENNReal.ofReal (tail : ℝ) := by
    have hsum := logDistortion_segment_le_tsum clocks error hstep n (m - n)
    rw [← ENNReal.coe_tsum hsummable] at hsum
    exact hsum.trans_eq (by simp [tail, ENNReal.ofReal_coe_nnreal])
  have htail_nonneg : 0 ≤ (tail : ℝ) := NNReal.coe_nonneg _
  have hdist : dist (cumulative clocks m).toContinuousMap
      (cumulative clocks n).toContinuousMap ≤ suffix.distortion := by
    rw [ContinuousMap.dist_le_iff_of_nonempty]
    intro t
    rw [hdecomp]
    exact suffix.dist_apply_le_distortion (cumulative clocks n t)
  calc
    dist (cumulative clocks m).toContinuousMap (cumulative clocks n).toContinuousMap ≤
        suffix.distortion := hdist
    _ ≤ Real.exp (tail : ℝ) - Real.exp (-(tail : ℝ)) :=
      distortion_le_exp_sub_exp_neg_of_logDistortion_le suffix htail_nonneg hlog

/-- Summably bounded local logarithmic distortions imply uniform convergence
of the cumulative time changes as continuous maps on the unit interval. -/
theorem exists_uniform_limit_cumulative_of_summable_logDistortion
    (clocks : ℕ → TimeChange) (error : ℕ → ℝ≥0)
    (hstep : ∀ n, (clocks n).logDistortion ≤ error n)
    (herror : Summable error) :
    ∃ limit : C(unitInterval, unitInterval),
      TendstoUniformly (fun n t => cumulative clocks n t) limit atTop := by
  let clockFun : ℕ → C(unitInterval, unitInterval) :=
    fun n => (cumulative clocks n).toContinuousMap
  let tail : ℕ → ℝ≥0 := fun n => ∑' k, error (n + k)
  have htail : Tendsto tail atTop (nhds 0) := by
    simpa only [Nat.add_comm] using NNReal.tendsto_sum_nat_add error
  have htailReal : Tendsto (fun n => (tail n : ℝ)) atTop (nhds 0) :=
    NNReal.tendsto_coe.mpr htail
  have hmodContinuous : Continuous fun x : ℝ => Real.exp x - Real.exp (-x) := by
    fun_prop [Real.continuous_exp]
  let modulus : ℕ → ℝ := fun n => Real.exp (tail n : ℝ) - Real.exp (-(tail n : ℝ))
  have hmod : Tendsto modulus atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => Real.exp x - Real.exp (-x)) ∘ fun n => (tail n : ℝ))
      atTop (nhds 0)
    simpa using hmodContinuous.continuousAt.tendsto.comp htailReal
  have hcauchy : CauchySeq clockFun := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hev : ∀ᶠ n in atTop, modulus n < ε := by
      have h := Metric.tendsto_nhds.mp hmod ε hε
      filter_upwards [h] with n hn
      have htail_nonneg : 0 ≤ (tail n : ℝ) := NNReal.coe_nonneg _
      have hmod_nonneg : 0 ≤ modulus n := by
        dsimp [modulus]
        exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
      simpa [Real.dist_eq, abs_of_nonneg hmod_nonneg] using hn
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, ?_⟩
    intro m hm n hn
    by_cases hmn : m ≤ n
    · calc
        dist (clockFun m) (clockFun n) = dist (clockFun n) (clockFun m) := dist_comm _ _
        _ ≤ modulus m := by
          simpa [modulus, tail] using
            cumulative_dist_le_exp_tail clocks error hstep herror m n hmn
        _ < ε := hN m hm
    · have hnm : n ≤ m := le_of_not_ge hmn
      exact (cumulative_dist_le_exp_tail clocks error hstep herror n m hnm).trans_lt (by
        simpa [modulus, tail] using hN n hn)
  obtain ⟨limit, hlimit⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨limit, ?_⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hnear : ∀ᶠ n in atTop, dist (clockFun n) limit < ε :=
    Metric.tendsto_nhds.mp hlimit ε hε
  filter_upwards [hnear] with n hn t
  calc
    dist (limit t) (cumulative clocks n t) =
        dist (cumulative clocks n t) (limit t) := dist_comm _ _
    _ = dist (clockFun n t) (limit t) := by simp [clockFun]
    _ ≤ dist (clockFun n) limit := ContinuousMap.dist_apply_le_dist t
    _ < ε := hn

end TimeChange

end Skorokhod
