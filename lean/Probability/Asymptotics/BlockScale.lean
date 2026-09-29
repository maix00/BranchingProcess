module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Nat

public section

/-!
# Integer block scales

This file contains the rounding and quotient facts shared by the diffusive
and stable small-deviation constructions.  The probabilistic scale
parameters remain in their respective modules; only the common floor
operation and its asymptotic interface live here.
-/

open Filter Topology

namespace ProbabilityTheory.Asymptotics

/-- The integer length obtained by rounding a real-valued block argument
down at each time. -/
noncomputable def floorBlockLength (argument : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊argument n⌋₊

/-- A divergent nonnegative block argument has a divergent rounded length. -/
theorem tendsto_floorBlockLength_atTop {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    Tendsto (floorBlockLength argument) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp hargument

/-- A divergent rounded block length is eventually positive. -/
theorem eventually_floorBlockLength_pos {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    ∀ᶠ n in atTop, 0 < floorBlockLength argument n :=
  (tendsto_floorBlockLength_atTop hargument).eventually
    (eventually_gt_atTop 0)

/-- Rounding a positive divergent argument does not change its normalized
length. -/
theorem tendsto_floorBlockLength_div_argument {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    Tendsto (fun n => (floorBlockLength argument n : ℝ) / argument n)
      atTop (nhds 1) :=
  (tendsto_nat_floor_div_atTop (R := ℝ)).comp hargument

/-- The rounded length is bounded above by its argument whenever the latter
is nonnegative. -/
theorem floorBlockLength_le {argument : ℕ → ℝ} {n : ℕ}
    (hargument : 0 ≤ argument n) :
    (floorBlockLength argument n : ℝ) ≤ argument n :=
  Nat.floor_le hargument

end ProbabilityTheory.Asymptotics
