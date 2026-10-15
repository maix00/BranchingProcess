/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Portmanteau

/-!
# Weak convergence of mixtures whose indices escape

The public theorem in this file is:

- `MeasureTheory.ProbabilityMeasure.tendsto_finiteMixture_of_escape`:
  if $Q_k\Rightarrow Q$, each fixed weight $p_{n,k}\to0$, and
  $M_n=\sum_{k=0}^{n}p_{n,k}Q_k$ with weights summing to one,
  then $M_n\Rightarrow Q$.

This is the finite-mixture limit used in the last paragraph of page 484
of Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace MeasureTheory.ProbabilityMeasure

open Filter MeasureTheory
open scoped ENNReal Topology

/-- A finite convex mixture converges to a common limit when its
weights escape every fixed finite set of indices. This is the
random-index step in the last paragraph of page 484 of Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. -/
theorem tendsto_finiteMixture_of_escape
    {E : Type*} [PseudoEMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [OpensMeasurableSpace E]
    (Q : ℕ → ProbabilityMeasure E) (limit : ProbabilityMeasure E)
    (mix : ℕ → ProbabilityMeasure E) (weight : ℕ → ℕ → ℝ≥0∞)
    (hQ : Tendsto Q atTop (𝓝 limit))
    (hweight : ∀ n, ∑ k ∈ Finset.range (n + 1), weight n k = 1)
    (hvanish : ∀ k, Tendsto (fun n => weight n k) atTop (𝓝 0))
    (hmix : ∀ n (A : Set E), MeasurableSet A →
      (mix n : Measure E) A =
        ∑ k ∈ Finset.range (n + 1),
          weight n k * (Q k : Measure E) A) :
    Tendsto mix atTop (𝓝 limit) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  apply le_of_forall_lt
  intro c hc
  obtain ⟨d, hcd, hdq⟩ := exists_between hc
  have hQopen := le_liminf_measure_open_of_tendsto hQ hG
  have hcInf : d < liminf (fun k => (Q k : Measure E) G) atTop :=
    lt_of_lt_of_le hdq hQopen
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (eventually_lt_of_lt_liminf hcInf)
  let head (n : ℕ) : ℝ≥0∞ :=
    ∑ k ∈ Finset.range K, weight n k
  let tail (n : ℕ) : ℝ≥0∞ :=
    ∑ j ∈ Finset.range (n + 1 - K), weight n (K + j)
  have hhead : Tendsto head atTop (𝓝 0) := by
    simpa only [head, Finset.sum_const_zero] using
      (tendsto_finsetSum (Finset.range K)
        (fun k _ => hvanish k))
  have htail : Tendsto tail atTop (𝓝 1) := by
    have hsub : Tendsto (fun n => 1 - head n) atTop (𝓝 (1 : ℝ≥0∞)) := by
      simpa only [tsub_zero] using
        (ENNReal.Tendsto.sub tendsto_const_nhds hhead
          (Or.inl ENNReal.one_ne_top))
    apply hsub.congr'
    filter_upwards [eventually_ge_atTop K] with n hn
    have hsplit := hweight n
    rw [show n + 1 = K + (n + 1 - K) by omega,
      Finset.sum_range_add] at hsplit
    change head n + tail n = 1 at hsplit
    exact (ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
      (by simpa only [add_comm] using hsplit)).symm
  have hcTop : d ≠ ∞ := by
    have hle : d ≤ (limit : Measure E) G := hdq.le
    exact ne_of_lt (lt_of_le_of_lt hle
      (lt_of_le_of_lt (measure_mono (Set.subset_univ G))
        (by simpa only [measure_univ] using ENNReal.one_lt_top)))
  have hlow : Tendsto (fun n => d * tail n) atTop (𝓝 d) := by
    simpa only [mul_one] using
      (ENNReal.Tendsto.mul
        (tendsto_const_nhds (x := d)) (Or.inr ENNReal.one_ne_top)
        htail (Or.inr hcTop))
  have hbound : ∀ᶠ n : ℕ in atTop,
      d * tail n ≤ (mix n : Measure E) G := by
    filter_upwards [eventually_ge_atTop K] with n hn
    rw [hmix n G hG.measurableSet,
      show n + 1 = K + (n + 1 - K) by omega,
      Finset.sum_range_add]
    have hsum : d * tail n ≤
        ∑ j ∈ Finset.range (n + 1 - K),
          weight n (K + j) * (Q (K + j) : Measure E) G := by
      change d * (∑ j ∈ Finset.range (n + 1 - K),
        weight n (K + j)) ≤ _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hq : d ≤ (Q (K + j) : Measure E) G :=
        (hK (K + j) (by omega)).le
      simpa only [mul_comm] using mul_le_mul_left hq (weight n (K + j))
    exact hsum.trans (le_add_of_nonneg_left bot_le)
  exact lt_of_lt_of_le hcd <| calc
    d = liminf (fun n => d * tail n) atTop := hlow.liminf_eq.symm
    _ ≤ liminf (fun n => (mix n : Measure E) G) atTop :=
      liminf_le_liminf hbound

end MeasureTheory.ProbabilityMeasure

end
