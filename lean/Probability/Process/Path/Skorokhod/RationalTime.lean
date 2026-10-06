/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalGrid.UnitInterval
public import Topology.Cadlag.Skorokhod.Oscillation.Dense
import Topology.Order.UnitInterval.Rational

/-!
# Rational-time process restrictions

This file contains the canonical embedding of rational points of the unit
interval into nonnegative time and the corresponding horizon restriction for
an arbitrary real-valued process.  It has no stable-law assumptions; stable
scaling and tube-rate statements are built on this interface in
`Probability.Process.Stable.SmallDeviation.RationalTube`.
-/

open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- The canonical embedding of a rational point of `[0,1]` into nonnegative
real time. -/
def rationalUnitTime (q : RationalGrid.UnitCoordinate) : ℝ≥0 :=
  ⟨(RationalGrid.unitCoe q : ℝ),
    (RationalGrid.unitCoe q).property.1⟩

@[simp]
theorem rationalUnitTime_coe (q : RationalGrid.UnitCoordinate) :
    (rationalUnitTime q : ℝ) = (RationalGrid.unitCoe q : ℝ) := rfl

theorem monotone_rationalUnitTime :
    Monotone (rationalUnitTime : RationalGrid.UnitCoordinate → ℝ≥0) := by
  intro s t hst
  apply NNReal.coe_le_coe.mp
  change ((s : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ)
  exact_mod_cast hst

theorem rationalUnitTime_bot : rationalUnitTime ⊥ = ⊥ := by
  apply Subtype.ext
  norm_num [rationalUnitTime, RationalGrid.unitCoe]

theorem rationalUnitTime_le_one (q : RationalGrid.UnitCoordinate) :
    rationalUnitTime q ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  change ((q : ℚ) : ℝ) ≤ 1
  exact_mod_cast q.property.2

@[simp]
theorem rationalUnitTime_top : rationalUnitTime ⊤ = 1 := by
  apply NNReal.coe_injective
  change ((1 : ℚ) : ℝ) = 1
  norm_num

/-- Restriction of a real-time process to rational points in `[0,1]`, after
running it up to the requested horizon. -/
def rationalHorizonProcess {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (horizon : ℝ≥0) : Ω → RationalGrid.UnitCoordinate → ℝ :=
  fun ω q => X (horizon * rationalUnitTime q) ω

/-- Subtract the initial coordinate of a rational path. -/
def centerRationalPath (x : RationalGrid.UnitCoordinate → ℝ) :
    RationalGrid.UnitCoordinate → ℝ :=
  fun q => x q - x ⊥

theorem measurable_centerRationalPath : Measurable centerRationalPath := by
  rw [measurable_pi_iff]
  intro q
  exact (measurable_pi_apply q).sub (measurable_pi_apply ⊥)

/-- The rational-coordinate form of a strict range tube. The target set is
measurable in the countable coordinate space; measurability of a pullback to
an arbitrary sample space requires the corresponding process map. -/
def rationalHorizonTubeEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (horizon : ℝ≥0) (width : ℝ) : Set Ω :=
  (rationalHorizonProcess X horizon) ⁻¹'
    Skorokhod.rationalCoordinateOscillationTube width

end ProbabilityTheory

end
