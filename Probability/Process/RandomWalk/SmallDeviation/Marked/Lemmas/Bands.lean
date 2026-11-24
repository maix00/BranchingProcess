/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.SmallDeviation.Marked.Basic
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic

/-!
# Return-band geometry for the marked affine-corridor bound

## Internal proof declarations

* `ProbabilityTheory.RandomWalk.SmallDeviation.Marked.band_subset_driftedReturn`:
  a centered increment tube of width `D` and an endpoint band of half-width
  `s/4`, translated from a core point with `x + is ∈ [0,s]`, stays in
  `[-R,R]` and returns to `[-3s,3s]` after subtracting drift, provided
  `D/2+4s ≤ R` and `0 ≤ drift · length ≤ s`.
-/

open scoped BigOperators
namespace ProbabilityTheory.RandomWalk.SmallDeviation.Marked

lemma band_subset_driftedReturn
    {D spacing radius drift x : ℝ} {length : ℕ} {i : ℤ}
    (hs : 0 < spacing) (hd : 0 ≤ drift)
    (hmax : drift * (length : ℝ) ≤ spacing)
    (hfit : D / 2 + 4 * spacing ≤ radius)
    (hx : x ∈ Set.Icc (-3 * spacing) (3 * spacing))
    (hnear : x + (i : ℝ) * spacing ∈ Set.Icc 0 spacing)
    (ω : ℕ → ℝ)
    (hpath : InHorizontalTube (1 / 2) D length ω)
    (hend : AdditivePath.displacement length ω ∈
      Set.Icc ((i : ℝ) * spacing - spacing / 4) ((i : ℝ) * spacing + spacing / 4)) :
    StaysIn (Set.Icc (-radius) radius) length x (fun j => ω j - drift) ∧
      x + AdditivePath.displacement length (fun j => ω j - drift) ∈
        Set.Icc (-3 * spacing) (3 * spacing) := by
  have hsum (k : ℕ) : AdditivePath.displacement k (fun j => ω j - drift) =
      AdditivePath.displacement k ω - (k : ℝ) * drift := by
    simp [AdditivePath.displacement, Finset.sum_sub_distrib]
  constructor
  · intro k
    have hk := hpath k
    rw [hsum]
    push_cast
    have hkl : (k.val + 1 : ℝ) ≤ length := by exact_mod_cast k.isLt
    have hkn : 0 ≤ (k.val + 1 : ℝ) := by positivity
    have hdk := mul_le_mul_of_nonneg_left hkl hd
    constructor <;> nlinarith [hx.1, hx.2, hk.1, hk.2, mul_nonneg hd hkn]
  · rw [hsum]
    constructor <;> nlinarith [hend.1, hend.2, hnear.1, hnear.2,
      mul_nonneg hd (Nat.cast_nonneg length)]

end ProbabilityTheory.RandomWalk.SmallDeviation.Marked
