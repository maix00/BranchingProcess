module

public import Topology.Cadlag.Skorokhod.Oscillation.Dense

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
def rationalUnitTime (q : Skorokhod.RationalunitInterval) : ℝ≥0 :=
  ⟨(Skorokhod.rationalunitIntervalCoe q : ℝ),
    (Skorokhod.rationalunitIntervalCoe q).property.1⟩

@[simp]
theorem rationalUnitTime_coe (q : Skorokhod.RationalunitInterval) :
    (rationalUnitTime q : ℝ) = (Skorokhod.rationalunitIntervalCoe q : ℝ) := rfl

theorem monotone_rationalUnitTime :
    Monotone (rationalUnitTime : Skorokhod.RationalunitInterval → ℝ≥0) := by
  intro s t hst
  apply NNReal.coe_le_coe.mp
  change ((s : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ)
  exact_mod_cast hst

theorem rationalUnitTime_bot : rationalUnitTime ⊥ = ⊥ := by
  apply Subtype.ext
  norm_num [rationalUnitTime, Skorokhod.rationalunitIntervalCoe]

theorem rationalUnitTime_le_one (q : Skorokhod.RationalunitInterval) :
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
    (horizon : ℝ≥0) : Ω → Skorokhod.RationalunitInterval → ℝ :=
  fun ω q => X (horizon * rationalUnitTime q) ω

/-- The rational-coordinate form of a strict range tube. The target set is
measurable in the countable coordinate space; measurability of a pullback to
an arbitrary sample space requires the corresponding process map. -/
def rationalHorizonTubeEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (horizon : ℝ≥0) (width : ℝ) : Set Ω :=
  (rationalHorizonProcess X horizon) ⁻¹'
    Skorokhod.rationalCoordinateOscillationTube width

end ProbabilityTheory

end
