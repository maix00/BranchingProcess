/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.Corridor
public import Topology.Cadlag.Skorokhod.Endpoint

/-!
# Open Skorokhod corridors with an endpoint constraint

The event combines a uniformly interior path corridor with an open condition
on the terminal value.  Both conditions are open in the `J₁` topology.
-/

@[expose] public section

open Set

namespace Skorokhod

/-- Paths that remain uniformly inside an open interval and whose terminal
value belongs to a prescribed open interval. -/
def rangeInOpenIntervalEndsIn (lower upper endpointLower endpointUpper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  rangeInOpenInterval lower upper ∩
    (fun path : CadlagPath unitInterval ℝ => path ⊤) ⁻¹'
      Set.Ioo endpointLower endpointUpper

theorem mem_rangeInOpenIntervalEndsIn_iff
    {lower upper endpointLower endpointUpper : ℝ}
    {path : CadlagPath unitInterval ℝ} :
    path ∈ rangeInOpenIntervalEndsIn lower upper endpointLower endpointUpper ↔
      path ∈ rangeInOpenInterval lower upper ∧
        path ⊤ ∈ Set.Ioo endpointLower endpointUpper :=
  Iff.rfl

/-- A uniform ball around a path with a positive corridor margin remains
inside the corridor and its open endpoint window. -/
theorem uniformBall_subset_rangeInOpenIntervalEndsIn
    {lower upper endpointLower endpointUpper : ℝ}
    {center : CadlagPath unitInterval ℝ}
    {δ : ℝ}
    (hmargin : ∃ margin > δ, ∀ t,
      lower + margin ≤ center t ∧ center t ≤ upper - margin)
    (hendpointLower : δ < center ⊤ - endpointLower)
    (hendpointUpper : δ < endpointUpper - center ⊤) :
    {path : CadlagPath unitInterval ℝ |
      ∀ t, |path t - center t| ≤ δ} ⊆
      rangeInOpenIntervalEndsIn
        lower upper endpointLower endpointUpper := by
  intro path hclose
  obtain ⟨margin, hδmargin, hpath⟩ := hmargin
  constructor
  · refine ⟨margin - δ, by linarith, fun t => ?_⟩
    have hc := hpath t
    have hd := abs_le.mp (hclose t)
    constructor <;> linarith
  · have hd := abs_le.mp (hclose ⊤)
    exact ⟨by linarith, by linarith⟩

theorem isOpen_rangeInOpenIntervalEndsIn
    (lower upper endpointLower endpointUpper : ℝ) :
    IsOpen (rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper) := by
  exact (isOpen_rangeInOpenInterval lower upper).inter
    (isOpen_Ioo.preimage continuous_apply_top)

theorem measurableSet_rangeInOpenIntervalEndsIn
    (lower upper endpointLower endpointUpper : ℝ) :
    MeasurableSet (rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper) :=
  (isOpen_rangeInOpenIntervalEndsIn
    lower upper endpointLower endpointUpper).measurableSet

/-- The straight path from zero to `y`, viewed as a càdlàg path. -/
def straightPath (y : ℝ) : CadlagPath unitInterval ℝ :=
  ⟨fun t => y * (t : ℝ),
    (continuous_const.mul continuous_subtype_val).isCadlag⟩

/-- A corridor and endpoint window containing a straight path form a
nonempty open set in the Skorokhod path space. -/
theorem straightPath_mem_rangeInOpenIntervalEndsIn
    {lower upper endpointLower endpointUpper y : ℝ}
    (hzero : lower < 0 ∧ 0 < upper)
    (hy : lower < y ∧ y < upper)
    (hend : endpointLower < y ∧ y < endpointUpper) :
    straightPath y ∈ rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper := by
  let margin := min (min (-lower) upper) (min (y - lower) (upper - y)) / 2
  have hmargin : 0 < margin := by
    dsimp [margin]
    apply half_pos
    exact lt_min (lt_min (by linarith) hzero.2)
      (lt_min (by linarith) (by linarith))
  have hmargin_le : margin ≤
      min (min (-lower) upper) (min (y - lower) (upper - y)) := by
    dsimp [margin]
    have hm := hmargin
    dsimp [margin] at hm
    linarith
  have hmLowerZero : margin ≤ -lower := by
    exact hmargin_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hmUpperZero : margin ≤ upper := by
    exact hmargin_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hmLowerY : margin ≤ y - lower := by
    exact hmargin_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmUpperY : margin ≤ upper - y := by
    exact hmargin_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  constructor
  · refine ⟨margin, hmargin, ?_⟩
    intro t
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    by_cases hy0 : 0 ≤ y
    · have hprod0 : 0 ≤ y * (t : ℝ) := mul_nonneg hy0 ht0
      have hprodY : y * (t : ℝ) ≤ y := by
        nlinarith [mul_nonneg hy0 (sub_nonneg.mpr ht1)]
      change lower + margin ≤ y * (t : ℝ) ∧
        y * (t : ℝ) ≤ upper - margin
      constructor <;> linarith
    · have hy0' : y ≤ 0 := le_of_lt (lt_of_not_ge hy0)
      have hprod0 : y * (t : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy0' ht0
      have hprodY : y ≤ y * (t : ℝ) := by
        nlinarith [mul_nonneg (neg_nonneg.mpr hy0') (sub_nonneg.mpr ht1)]
      change lower + margin ≤ y * (t : ℝ) ∧
        y * (t : ℝ) ≤ upper - margin
      constructor <;> linarith
  · simpa [straightPath] using hend

/-- Paths that remain in a closed interval and whose terminal value lies in
a prescribed closed interval. -/
def rangeInClosedIntervalEndsIn (lower upper endpointLower endpointUpper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  rangeInClosedInterval lower upper ∩
    (fun path : CadlagPath unitInterval ℝ => path ⊤) ⁻¹'
      Set.Icc endpointLower endpointUpper

theorem mem_rangeInClosedIntervalEndsIn_iff
    {lower upper endpointLower endpointUpper : ℝ}
    {path : CadlagPath unitInterval ℝ} :
    path ∈ rangeInClosedIntervalEndsIn lower upper endpointLower endpointUpper ↔
      path ∈ rangeInClosedInterval lower upper ∧
        path ⊤ ∈ Set.Icc endpointLower endpointUpper :=
  Iff.rfl

theorem isClosed_rangeInClosedIntervalEndsIn
    (lower upper endpointLower endpointUpper : ℝ) :
    IsClosed (rangeInClosedIntervalEndsIn
      lower upper endpointLower endpointUpper) := by
  exact (isClosed_rangeInClosedInterval lower upper).inter
    (isClosed_Icc.preimage continuous_apply_top)

theorem measurableSet_rangeInClosedIntervalEndsIn
    (lower upper endpointLower endpointUpper : ℝ) :
    MeasurableSet (rangeInClosedIntervalEndsIn
      lower upper endpointLower endpointUpper) :=
  (isClosed_rangeInClosedIntervalEndsIn
    lower upper endpointLower endpointUpper).measurableSet

end Skorokhod
