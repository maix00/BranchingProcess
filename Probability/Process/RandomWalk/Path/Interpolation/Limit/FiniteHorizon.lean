/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Scaling.FiniteHorizon
public import Probability.Process.RandomWalk.Path.Interpolation.Limit.Unbounded

/-!
# Finite-horizon restriction of polygonal random-walk paths

## Public declarations

- `ProbabilityTheory.RandomWalk.restrict_normalizedLinearContinuousPathUnbounded_eq_rescaleUnitPath`:
  for $m>0$ and nonzero $a_n,a_{mn}$, restricting the whole-time path to
  $[0,m]$ equals the rescaled unit-time path of the first $mn$ increments,
  with amplitude factor $a_{mn}/a_n$.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open MeasureTheory
open scoped NNReal

/-- Restricting the whole-time polygonal path to `[0,m]` gives the unit-time
path built from the first `m * n` increments, with the corresponding time and
amplitude rescaling. -/
theorem restrict_normalizedLinearContinuousPathUnbounded_eq_rescaleUnitPath
    (scale : ℕ → ℝ) (m n : ℕ) (hm : 0 < m)
    (hscale : scale n ≠ 0) (hscaleMN : scale (m * n) ≠ 0)
    (increment : ℕ → ℝ) :
    restrictPathTo (m : ℝ≥0)
        (normalizedLinearContinuousPathUnbounded scale n increment) =
      rescaleUnitPath (m : ℝ≥0) (by exact_mod_cast hm)
        (scale (m * n) / scale n)
        (normalizedLinearContinuousPathIcc scale (m * n) increment) := by
  ext t
  let u : unitInterval := unitTimeOfFiniteTime (m : ℝ≥0)
    (by exact_mod_cast hm) t
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have harg : ((m * n : ℕ) : ℝ) * (u : ℝ) = (n : ℝ) * (t.1 : ℝ) := by
    change ((m * n : ℕ) : ℝ) * ((t.1 : ℝ) / (m : ℝ)) =
      (n : ℝ) * (t.1 : ℝ)
    push_cast
    field_simp
  have hcap : (n : ℝ) * (t.1 : ℝ) ≤ (m * n : ℕ) := by
    have ht : (t.1 : ℝ) ≤ m := NNReal.coe_le_coe.mpr t.property.2
    calc
      (n : ℝ) * (t.1 : ℝ) ≤ (n : ℝ) * m :=
        mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
      _ = (m * n : ℕ) := by push_cast; ring
  have hweights (i : ℕ) :
      linearIncrementWeight (m * n) i (u : ℝ) =
        linearIncrementWeight n i (t.1 : ℝ) := by
    unfold linearIncrementWeight
    rw [harg]
  have hsum :
      (∑ i ∈ Finset.range (m * n),
        linearIncrementWeight (m * n) i (u : ℝ) * increment i) =
      ∑ i ∈ Finset.range (m * n),
        linearIncrementWeight n i (t.1 : ℝ) * increment i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hweights]
  change normalizedLinearPathUnbounded scale n increment t.1 =
    (scale (m * n) / scale n) *
      normalizedLinearPath scale (m * n) increment u
  rw [normalizedLinearPathUnbounded_eq_sum_range
    scale n increment t.1 (m * n) hcap]
  unfold normalizedLinearPath
  rw [hsum]
  field_simp

end ProbabilityTheory.RandomWalk

end
