/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Analysis.Asymptotics.Scale.Block.Length

/-!
# Reindexing support for stable norming

## Internal proof declarations

* `stableNormingIndex` rounds the reciprocal stable time scale to a positive
  integer sequence.
* `stableNormingIndex_ratio` and `stableNormingIndex_tendsto_atTop` provide
  the asymptotic ratio and divergence used by the source stable-norming
  lemma.
-/

open Filter
open scoped Topology

namespace ProbabilityTheory

noncomputable def stableNormingIndex (d : ℝ) (n : ℕ) : ℕ :=
  Asymptotics.floorBlockLength (fun n => (n : ℝ) / d) n + 1

lemma stableNormingIndex_ratio {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n => (stableNormingIndex d n : ℝ) / (n : ℝ)) atTop
      (nhds d⁻¹) := by
  let argument : ℕ → ℝ := fun n => (n : ℝ) / d
  let denominator : ℕ → ℝ := fun n => (n : ℝ)
  have hargument : Tendsto argument atTop atTop := by
    simpa [argument, div_eq_mul_inv, mul_comm] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (inv_pos.mpr hd)
  have hdenominator : Tendsto denominator atTop atTop := by
    simpa [denominator] using (tendsto_natCast_atTop_atTop : Tendsto
      (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hratio : Tendsto (fun n => argument n / denominator n) atTop
      (nhds d⁻¹) := by
    have heq : (fun n => argument n / denominator n) =ᶠ[atTop]
        fun _ => d⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      dsimp [argument, denominator]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR]
    exact tendsto_const_nhds.congr' heq.symm
  simpa [stableNormingIndex, argument, denominator] using
    Asymptotics.tendsto_floorBlockLength_add_nat_div_of_argument_ratio
      1 hargument hdenominator hratio

lemma stableNormingIndex_tendsto_atTop {d : ℝ} (hd : 0 < d) :
    Tendsto (stableNormingIndex d) atTop atTop := by
  have hratio := stableNormingIndex_ratio hd
  have hbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (2 * d) ≤ (stableNormingIndex d n : ℝ) := by
    have hhalf : d⁻¹ / 2 < d⁻¹ := by
      have hinv : 0 < d⁻¹ := inv_pos.mpr hd
      linarith
    filter_upwards [hratio.eventually
        (Ioi_mem_nhds hhalf),
      eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    have hnratio : d⁻¹ / 2 <
        (stableNormingIndex d n : ℝ) / (n : ℝ) := hn
    have hmul : d⁻¹ / 2 * (n : ℝ) < (stableNormingIndex d n : ℝ) :=
      (lt_div_iff₀ hnR).mp hnratio
    have hcoef : d⁻¹ / 2 * (n : ℝ) = (n : ℝ) / (2 * d) := by
      field_simp [hd.ne']
    rw [← hcoef]
    exact hmul.le
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ) / (2 * d)) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity :
        0 < (2 * d)⁻¹))
  have hreal : Tendsto (fun n => (stableNormingIndex d n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hbound hlinear
  refine tendsto_atTop.2 ?_
  intro k
  filter_upwards [hreal.eventually (eventually_gt_atTop (k : ℝ))] with n hn
  exact_mod_cast hn.le


end ProbabilityTheory
