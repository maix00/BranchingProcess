/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.ContinuousMap

/-!
# Linear paths in Skorokhod space

This file records the elementary relation between a `J₁` ball centered at a
linear path and the corresponding uniform tube. The time-change part of the
`J₁` metric moves a line by at most its slope times the clock distortion.
-/

@[expose] public section

open scoped ENNReal

namespace Skorokhod

/-- The continuous linear path with the given slope. -/
def linearPath (slope : ℝ) : CadlagPath unitInterval ℝ :=
  ofContinuousMap
    ⟨fun t => slope * (t : ℝ), continuous_const.mul continuous_subtype_val⟩

/-- The `J₁` distance between two linear paths is at most the difference of
their slopes. The identity time change bounds it by the uniform distance. -/
theorem dist_linearPath_le (slope₁ slope₂ : ℝ) :
    dist (linearPath slope₁) (linearPath slope₂) ≤ |slope₁ - slope₂| := by
  let f : C(unitInterval, ℝ) :=
    ⟨fun t => slope₁ * (t : ℝ),
      continuous_const.mul continuous_subtype_val⟩
  let g : C(unitInterval, ℝ) :=
    ⟨fun t => slope₂ * (t : ℝ),
      continuous_const.mul continuous_subtype_val⟩
  have hfun : edist f g ≤ ENNReal.ofReal |slope₁ - slope₂| := by
    rw [ContinuousMap.edist_eq_iSup]
    apply iSup_le
    intro t
    have htval : |(t : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg t.property.1]
      exact t.property.2
    have hreal :
        |slope₁ * (t : ℝ) - slope₂ * (t : ℝ)| ≤ |slope₁ - slope₂| := by
      calc
        |slope₁ * (t : ℝ) - slope₂ * (t : ℝ)| =
            |slope₁ - slope₂| * |(t : ℝ)| := by
              rw [show slope₁ * (t : ℝ) - slope₂ * (t : ℝ) =
                (slope₁ - slope₂) * (t : ℝ) by ring, abs_mul]
        _ ≤ |slope₁ - slope₂| * 1 :=
          mul_le_mul_of_nonneg_left htval (abs_nonneg _)
        _ = |slope₁ - slope₂| := by ring
    simpa [f, g, edist_dist, Real.dist_eq] using
      (ENNReal.ofReal_le_ofReal hreal)
  have hpath : edist (linearPath slope₁) (linearPath slope₂) ≤
      ENNReal.ofReal |slope₁ - slope₂| := by
    change edist (ofContinuousMap f) (ofContinuousMap g) ≤ _
    exact (edist_ofContinuousMap_le f g).trans hfun
  have hpath' : ENNReal.ofReal
      (dist (linearPath slope₁) (linearPath slope₂)) ≤
      ENNReal.ofReal |slope₁ - slope₂| := by
    simpa only [edist_dist] using hpath
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp hpath'

/-- A `J₁` ball around a linear path controls the uniform error, since a time
change of size `r` moves the linear center by at most `|slope| r`. -/
theorem abs_sub_linear_lt_two_mul_of_dist_lt
    {path : CadlagPath unitInterval ℝ} {slope radius : ℝ}
    (hradius : 0 < radius) (hslope : |slope| ≤ 1)
    (hpath : dist path (linearPath slope) < radius) :
    ∀ t, |path t - slope * (t : ℝ)| < 2 * radius := by
  have hj1 : j1EDist (linearPath slope) path < ENNReal.ofReal radius := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hradius]
    simpa [dist_comm] using hpath
  obtain ⟨change, hcost⟩ := exists_timeChange_j1Cost_lt hj1
  have hclockENN : ENNReal.ofReal change.distortion < ENNReal.ofReal radius :=
    (le_max_left _ _).trans_lt hcost
  have hclock : change.distortion < radius :=
    (ENNReal.ofReal_lt_ofReal_iff hradius).1 hclockENN
  have huniform : uniformEDist (change.act (linearPath slope)) path <
      ENNReal.ofReal radius :=
    (le_max_right _ _).trans_lt hcost
  intro t
  have hpointENN :=
    (edist_apply_le_uniformEDist
      (change.act (linearPath slope)) path t).trans_lt huniform
  rw [TimeChange.act_apply, edist_dist,
    ENNReal.ofReal_lt_ofReal_iff hradius] at hpointENN
  have hpoint : dist (path t) (linearPath slope (change t)) < radius := by
    simpa [dist_comm] using hpointENN
  have htime : dist (change t) t < radius :=
    (change.dist_apply_le_distortion t).trans_lt hclock
  have hline : dist (linearPath slope (change t))
      (linearPath slope t) ≤ |slope| * radius := by
    rw [linearPath, ofContinuousMap_apply, Real.dist_eq]
    calc
      |slope * (change t : ℝ) - slope * (t : ℝ)| =
          |slope| * |(change t : ℝ) - (t : ℝ)| := by
            rw [← abs_mul]
            congr 1 <;> ring
      _ = |slope| * dist (change t) t := by
        rw [Subtype.dist_eq, Real.dist_eq]
      _ ≤ |slope| * radius :=
        mul_le_mul_of_nonneg_left htime.le (abs_nonneg slope)
  have htotal : dist (path t) (linearPath slope t) < 2 * radius := by
    calc
      dist (path t) (linearPath slope t) ≤
          dist (path t) (linearPath slope (change t)) +
            dist (linearPath slope (change t)) (linearPath slope t) :=
        dist_triangle _ _ _
      _ < radius + |slope| * radius := add_lt_add_of_lt_of_le hpoint hline
      _ ≤ 2 * radius := by
        have hmul := mul_le_mul_of_nonneg_right hslope hradius.le
        nlinarith
  simpa [linearPath, ofContinuousMap_apply, Real.dist_eq] using htotal

end Skorokhod

end
