/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.Brownian.Bessel.ThreeDimensional
import Probability.Process.Brownian.Support.LinearTube
import Topology.Cadlag.Skorokhod.Path.Linear

/-!
# Proof support for the Bessel path support theorem

## Internal proof declarations

The coordinate error estimate and its path-space transfer form the
single-client proof chain for `BrownianBessel3.linearPath_mem_support`.
-/

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.BrownianBessel3

lemma radius_error_le_coordinate_errors (x y z a : ℝ) :
    |Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) - (|a|)| ≤
      |x - a| + |y| + |z| := by
  let r := Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)
  have hs : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := Real.sq_sqrt hs
  have hx : |x| ≤ r := by
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg y, sq_nonneg z]
  have hu : r ≤ |x| + |y| + |z| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [← sq_abs x, ← sq_abs y, ← sq_abs z]
      nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg y),
        mul_nonneg (abs_nonneg x) (abs_nonneg z),
        mul_nonneg (abs_nonneg y) (abs_nonneg z)]
  have hxa : |x| ≤ |a| + |x - a| := by
    calc |x| = |(x - a) + a| := by congr 1; ring
      _ ≤ |x - a| + |a| := abs_add_le _ _
      _ = |a| + |x - a| := add_comm _ _
  have hax : |a| ≤ |x| + |x - a| := by
    calc |a| = |x - (x - a)| := by congr 1; ring
      _ ≤ |x| + |a - x| := by
        simpa [sub_eq_add_neg] using abs_add_le x (-(x - a))
      _ = |x| + |x - a| := by rw [abs_sub_comm]
  apply abs_le.mpr
  constructor <;> linarith

lemma radial_path_close
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    (hB : ∀ ω, Continuous (B · ω))
    {a δ r : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (hsmall : 5 * δ * (1 + |a|) < r)
    {ω : Triple Ω}
    (h₁ : dist (cadlagunitIntervalPath B hB ω.1)
      (Skorokhod.linearPath a) < δ)
    (h₂ : dist (cadlagunitIntervalPath B hB ω.2.1)
      (Skorokhod.linearPath 0) < δ)
    (h₃ : dist (cadlagunitIntervalPath B hB ω.2.2)
      (Skorokhod.linearPath 0) < δ) :
    dist (path B hB ω) (Skorokhod.linearPath a) < r := by
  have he₁ := Skorokhod.abs_sub_linear_lt_radius_mul_of_dist_lt hδ h₁
  have he₂ := Skorokhod.abs_sub_linear_lt_radius_mul_of_dist_lt hδ h₂
  have he₃ := Skorokhod.abs_sub_linear_lt_radius_mul_of_dist_lt hδ h₃
  have hpoint (t : unitInterval) :
      |path B hB ω t - a * (t : ℝ)| ≤ 5 * δ * (1 + |a|) := by
    have h₁t := he₁ t
    have h₂t := he₂ t
    have h₃t := he₃ t
    simp only [cadlagunitIntervalPath_apply, zero_mul, sub_zero,
      add_zero, abs_zero] at h₁t h₂t h₃t
    have hat : 0 ≤ a * (t : ℝ) :=
      mul_nonneg ha t.property.1
    have hrad := radius_error_le_coordinate_errors
      (B (unitInterval.toNNReal t) ω.1)
      (B (unitInterval.toNNReal t) ω.2.1)
      (B (unitInterval.toNNReal t) ω.2.2) (a * (t : ℝ))
    simp only [path, cadlagunitIntervalPath_apply, radius,
      abs_of_nonneg hat] at hrad ⊢
    have hδle : δ ≤ δ * (1 + |a|) := by
      nlinarith [abs_nonneg a]
    linarith
  have huniform : Skorokhod.uniformEDist (path B hB ω)
      (Skorokhod.linearPath a) ≤ ENNReal.ofReal (5 * δ * (1 + |a|)) := by
    rw [Skorokhod.uniformEDist_eq_edist, UniformFun.edist_def]
    refine iSup_le fun t => ?_
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal (hpoint t)
  have hj1 := (Skorokhod.j1EDist_le_uniformEDist
    (path B hB ω) (Skorokhod.linearPath a)).trans huniform
  rw [← Skorokhod.edist_cadlagPath_eq_j1EDist, edist_dist] at hj1
  have hdist : dist (path B hB ω) (Skorokhod.linearPath a) ≤
      5 * δ * (1 + |a|) := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hj1
  exact hdist.trans_lt hsmall

end ProbabilityTheory.BrownianBessel3

end
