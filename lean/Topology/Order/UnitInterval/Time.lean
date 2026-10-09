/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval

/-!
# Standard time coordinates on the unit interval

The interval's inclusion into nonnegative real time and its identity clock
are deterministic time-domain constructions. Process-valued restrictions
are defined in the probability layer.
-/

@[expose] public section

namespace UnitInterval

/-- The canonical inclusion of `[0,1]` into nonnegative real time. -/
def toNNReal (t : unitInterval) : NNReal :=
  ⟨t, t.property.1⟩

theorem continuous_toNNReal : Continuous toNNReal := by
  exact continuous_subtype_val.subtype_mk _

@[simp] theorem toNNReal_top : toNNReal ⊤ = 1 := by
  apply NNReal.coe_injective
  rfl

theorem toNNReal_le_one (t : unitInterval) : toNNReal t ≤ 1 := by
  apply NNReal.coe_le_coe.mpr
  exact t.property.2

/-- Every point of a nonnegative interval is reached by the normalized
unit-interval clock when the interval has positive length. -/
theorem exists_mul_eq (length t : NNReal)
    (hlength : 0 < length) (ht : t ≤ length) :
    ∃ u : unitInterval, length * toNNReal u = t := by
  have hreal : 0 < (length : ℝ) := NNReal.coe_pos.mpr hlength
  have htle : (t : ℝ) ≤ (length : ℝ) := NNReal.coe_le_coe.mpr ht
  let u : unitInterval := ⟨(t : ℝ) / length, by
    constructor
    · positivity
    · exact (div_le_one hreal).mpr htle⟩
  refine ⟨u, ?_⟩
  apply NNReal.coe_injective
  change (length : ℝ) * ((t : ℝ) / length) = t
  field_simp

/-- Every point of a translated nonnegative interval is reached by its
normalized affine clock. -/
theorem exists_add_mul_eq (start length t : NNReal)
    (hlength : 0 < length) (hstart : start ≤ t)
    (hend : t ≤ start + length) :
    ∃ u : unitInterval, start + length * toNNReal u = t := by
  have hdelta : t - start ≤ length := by
    exact tsub_le_iff_left.mpr hend
  obtain ⟨u, hu⟩ := exists_mul_eq length (t - start)
    hlength hdelta
  refine ⟨u, ?_⟩
  rw [hu]
  simpa [add_comm] using tsub_add_cancel_of_le hstart

/-- The canonical real-valued time coordinate on `[0,1]`. -/
def clock (t : unitInterval) : ℝ := t

theorem monotone_clock : Monotone clock := by
  intro s t hst
  exact hst

@[simp] theorem clock_bot : clock ⊥ = 0 := by
  simp [clock]

end UnitInterval

end
