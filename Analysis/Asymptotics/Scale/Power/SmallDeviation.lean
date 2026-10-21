/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Analysis.Asymptotics.Scale.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Power-law small-deviation scales

The public theorem `Asymptotics.isSmallDeviationScale_natCast_rpow_of_lt`
states that for $0<p<q$, the power scale $n\mapsto n^p$ satisfies
$(n^p)\to\infty$ and $n^p/n^q\to0$. It supplies a reusable instance of
`Asymptotics.IsSmallDeviationScale` for power-law widths.
-/

@[expose] public section

open Filter

namespace Asymptotics

/-- For `0 < p < q`, the power `n ^ p` is a small-deviation scale relative to
the larger power `n ^ q`. -/
theorem isSmallDeviationScale_natCast_rpow_of_lt {p q : ℝ}
    (hp : 0 < p) (hpq : p < q) :
    IsSmallDeviationScale (fun n : ℕ => (n : ℝ) ^ p)
      (fun n => (n : ℝ) ^ q) := by
  have hscale : Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(q - p))) atTop
        (nhds 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hpq)).comp
        tendsto_natCast_atTop_atTop
  have heq : (fun n : ℕ => (n : ℝ) ^ p / (n : ℝ) ^ q) =ᶠ[atTop]
      fun n => (n : ℝ) ^ (-(q - p)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [← Real.rpow_sub hnpos]
    congr 1
    ring
  exact IsSmallDeviationScale.of_tendsto hscale (hpow.congr' heq.symm)

end Asymptotics
