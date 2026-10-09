/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Order.Interval.RationalCoordinate.UnitInterval

/-!
# Rational coordinates in the real unit interval

This file supplies the topological embedding and density result for rational
unit-interval coordinates. Their finite-grid representation is an instance of
the bounded interval construction in `Order.Interval.RationalGrid.Interval`.
-/

@[expose] public section

open Set

namespace RationalCoordinate

/-- The canonical inclusion of rational coordinates in `[0, 1]` into the real
unit interval. -/
def toUnitInterval (q : RationalCoordinate.UnitInterval) : unitInterval :=
  ⟨q.1, by
    constructor
    · exact_mod_cast q.2.1
    · exact_mod_cast q.2.2⟩

theorem denseRange_toUnitInterval :
    DenseRange toUnitInterval := by
  rw [Metric.denseRange_iff]
  intro x radius hradius
  by_cases hx0 : (x : ℝ) = 0
  · refine ⟨⟨0, by simp⟩, ?_⟩
    rw [Subtype.dist_eq]
    simp [toUnitInterval, hx0, hradius]
  by_cases hx1 : (x : ℝ) = 1
  · refine ⟨⟨1, by simp⟩, ?_⟩
    rw [Subtype.dist_eq]
    simp [toUnitInterval, hx1, hradius]
  have hx0lt : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx0)
  have hx1lt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 hx1
  let lower : ℝ := max 0 ((x : ℝ) - radius)
  let upper : ℝ := min 1 ((x : ℝ) + radius)
  have hlower : lower < (x : ℝ) := by
    dsimp only [lower]
    exact max_lt hx0lt (sub_lt_self _ hradius)
  have hupper : (x : ℝ) < upper := by
    dsimp only [upper]
    exact lt_min hx1lt (lt_add_of_pos_right _ hradius)
  obtain ⟨q, hlq, hqu⟩ := exists_rat_btwn (hlower.trans hupper)
  have hqmem : q ∈ Set.Icc (0 : ℚ) 1 := by
    constructor
    · exact_mod_cast (le_max_left 0 ((x : ℝ) - radius) |>.trans_lt hlq).le
    · exact_mod_cast (hqu.trans_le (min_le_left 1 ((x : ℝ) + radius))).le
  refine ⟨⟨q, hqmem⟩, ?_⟩
  rw [Subtype.dist_eq, Real.dist_eq]
  apply abs_lt.2
  constructor
  · have := hqu.trans_le (min_le_right 1 ((x : ℝ) + radius))
    dsimp only [toUnitInterval]
    linarith
  · have := (le_max_right 0 ((x : ℝ) - radius)).trans_lt hlq
    dsimp only [toUnitInterval]
    linarith


/-- The canonical embedding of rational unit-interval coordinates into
nonnegative real time. -/
def toNNReal (q : RationalCoordinate.UnitInterval) : NNReal :=
  ⟨(toUnitInterval q : ℝ), (toUnitInterval q).property.1⟩

@[simp]
theorem toNNReal_coe (q : RationalCoordinate.UnitInterval) :
    (toNNReal q : ℝ) = (toUnitInterval q : ℝ) := rfl

theorem monotone_toNNReal : Monotone (toNNReal : RationalCoordinate.UnitInterval → NNReal) := by
  intro s t hst
  apply NNReal.coe_le_coe.mpr
  change ((s : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ)
  exact_mod_cast hst

theorem toNNReal_bot : toNNReal ⊥ = ⊥ := by
  apply Subtype.ext
  norm_num [toNNReal, toUnitInterval]

theorem toNNReal_le_one (q : RationalCoordinate.UnitInterval) : toNNReal q ≤ 1 := by
  apply NNReal.coe_le_coe.mpr
  exact (toUnitInterval q).property.2

@[simp]
theorem toNNReal_top : toNNReal ⊤ = 1 := by
  apply NNReal.coe_injective
  change ((1 : ℚ) : ℝ) = 1
  norm_num

end RationalCoordinate
