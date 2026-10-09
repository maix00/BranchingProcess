/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Topology.Cadlag.Skorokhod.Oscillation.Dense
public import Topology.Order.UnitInterval.Rational

/-!
# Rational-time restrictions of processes

The rational embedding into nonnegative time is deterministic and lives in
`Topology.Order.UnitInterval.Rational`. This file defines its use to restrict
real-time processes and form tube events.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- Restrict a process to rational points in `[0,1]`, after running it up to
the requested horizon. -/
def rationalHorizonProcess {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (horizon : ℝ≥0) : Ω → RationalCoordinate.UnitInterval → ℝ :=
  fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω

/-- Subtract the initial coordinate of a rational path. -/
def centerRationalPath (x : RationalCoordinate.UnitInterval → ℝ) :
    RationalCoordinate.UnitInterval → ℝ :=
  fun q => x q - x ⊥

theorem measurable_centerRationalPath : Measurable centerRationalPath := by
  rw [measurable_pi_iff]
  intro q
  exact (measurable_pi_apply q).sub (measurable_pi_apply ⊥)

/-- The rational-coordinate form of a strict range tube. Measurability of its
pullback to a sample space requires the corresponding process map. -/
def rationalHorizonTubeEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (horizon : ℝ≥0) (width : ℝ) : Set Ω :=
  (rationalHorizonProcess X horizon) ⁻¹'
    Skorokhod.rationalCoordinateOscillationTube width

end ProbabilityTheory

end
