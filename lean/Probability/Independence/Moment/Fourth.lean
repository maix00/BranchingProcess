/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Fourth moments of independent centered sums

The identities here are independent of any random-walk representation.  They
supply the elementary fourth-moment recurrence used by truncation arguments.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a real random variable, fourth-power integrability is exactly the
`L⁴` condition. -/
theorem memLp_four_iff_integrable_pow_four {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) :
    MemLp X 4 μ ↔ Integrable (fun ω => X ω ^ 4) μ := by
  rw [← integrable_norm_rpow_iff hX (by norm_num) (by norm_num)]
  norm_num
  constructor <;> intro h
  · apply h.congr
    filter_upwards [] with ω
    rw [show |X ω| ^ 4 = (|X ω| ^ 2) ^ 2 by ring,
      show X ω ^ 4 = (X ω ^ 2) ^ 2 by ring, sq_abs]
  · apply h.congr
    filter_upwards [] with ω
    rw [show X ω ^ 4 = (X ω ^ 2) ^ 2 by ring,
      show |X ω| ^ 4 = (|X ω| ^ 2) ^ 2 by ring, sq_abs]

private theorem integrable_pow_two_of_memLp_four
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 4 μ) :
    Integrable (fun ω => X ω ^ 2) μ := by
  have hX2 : MemLp X 2 μ := hX.mono_exponent (by norm_num)
  simpa [Real.norm_eq_abs, sq_abs] using hX2.integrable_norm_pow (by norm_num)

private theorem integrable_pow_three_of_memLp_four
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 4 μ) :
    Integrable (fun ω => X ω ^ 3) μ := by
  have hX3 : MemLp X 3 μ := hX.mono_exponent (by norm_num)
  exact (hX3.integrable_norm_pow (by norm_num)).mono
    (hX.aestronglyMeasurable.pow 3)
    (ae_of_all μ fun ω => by simp [Real.norm_eq_abs])

private theorem integrable_pow_four_of_memLp_four
    {X : Ω → ℝ} (hX : MemLp X 4 μ) :
    Integrable (fun ω => X ω ^ 4) μ := by
  have h := hX.integrable_norm_pow (by norm_num)
  apply h.congr
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]

/-- Fourth-moment expansion for two independent real random variables. -/
theorem IndepFun.integral_add_pow_four
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXY : X ⟂ᵢ[μ] Y) (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hX4 : MemLp X 4 μ) (hY4 : MemLp Y 4 μ) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) =
      (∫ ω, X ω ^ 4 ∂μ) +
        4 * (∫ ω, X ω ^ 3 ∂μ) * (∫ ω, Y ω ∂μ) +
        6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) +
        4 * (∫ ω, X ω ∂μ) * (∫ ω, Y ω ^ 3 ∂μ) +
        ∫ ω, Y ω ^ 4 ∂μ := by
  have hX1 : Integrable X μ := hX4.integrable (by norm_num)
  have hY1 : Integrable Y μ := hY4.integrable (by norm_num)
  have hX2 := integrable_pow_two_of_memLp_four hX4
  have hY2 := integrable_pow_two_of_memLp_four hY4
  have hX3 := integrable_pow_three_of_memLp_four hX4
  have hY3 := integrable_pow_three_of_memLp_four hY4
  have hX4i := integrable_pow_four_of_memLp_four hX4
  have hY4i := integrable_pow_four_of_memLp_four hY4
  have hfactor (a b : ℕ) :
      (∫ ω, X ω ^ a * Y ω ^ b ∂μ) =
        (∫ ω, X ω ^ a ∂μ) * ∫ ω, Y ω ^ b ∂μ := by
    simpa [Function.comp_def] using hXY.integral_fun_comp_mul_comp
      hXmeas.aemeasurable hYmeas.aemeasurable
      (measurable_id.pow_const a).aestronglyMeasurable
      (measurable_id.pow_const b).aestronglyMeasurable
  have hX3Y : Integrable (fun ω => X ω ^ 3 * Y ω) μ := by
    change Integrable ((fun ω => X ω ^ 3) * Y) μ
    simpa [Function.comp_def] using
      (hXY.comp (measurable_id.pow_const 3) measurable_id).integrable_mul hX3 hY1
  have hX2Y2 : Integrable (fun ω => X ω ^ 2 * Y ω ^ 2) μ := by
    change Integrable ((fun ω => X ω ^ 2) * fun ω => Y ω ^ 2) μ
    simpa [Function.comp_def] using
      (hXY.comp (measurable_id.pow_const 2)
        (measurable_id.pow_const 2)).integrable_mul hX2 hY2
  have hXY3 : Integrable (fun ω => X ω * Y ω ^ 3) μ := by
    change Integrable (X * fun ω => Y ω ^ 3) μ
    simpa [Function.comp_def] using
      (hXY.comp measurable_id (measurable_id.pow_const 3)).integrable_mul hX1 hY3
  have hfactor31 :
      (∫ ω, X ω ^ 3 * Y ω ∂μ) =
        (∫ ω, X ω ^ 3 ∂μ) * ∫ ω, Y ω ∂μ := by
    simpa using hfactor 3 1
  have hfactor22 := hfactor 2 2
  have hfactor13 :
      (∫ ω, X ω * Y ω ^ 3 ∂μ) =
        (∫ ω, X ω ∂μ) * ∫ ω, Y ω ^ 3 ∂μ := by
    simpa using hfactor 1 3
  rw [show (fun ω => (X ω + Y ω) ^ 4) = fun ω =>
      X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) +
        6 * (X ω ^ 2 * Y ω ^ 2) + 4 * (X ω * Y ω ^ 3) + Y ω ^ 4 by
    funext ω
    ring]
  rw [integral_add, integral_add, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul,
    hfactor31, hfactor22, hfactor13]
  · ring
  all_goals first
    | exact hX4i
    | exact hX3Y.const_mul 4
    | exact hX2Y2.const_mul 6
    | exact hXY3.const_mul 4
    | exact hY4i
    | exact hX4i.add (hX3Y.const_mul 4)
    | exact (hX4i.add (hX3Y.const_mul 4)).add (hX2Y2.const_mul 6)
    | exact ((hX4i.add (hX3Y.const_mul 4)).add
        (hX2Y2.const_mul 6)).add (hXY3.const_mul 4)

/-- For independent centered variables, only the pure fourth moments and the
product of second moments remain. -/
theorem IndepFun.integral_add_pow_four_of_centered
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXY : X ⟂ᵢ[μ] Y) (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hX4 : MemLp X 4 μ) (hY4 : MemLp Y 4 μ)
    (hXcentered : ∫ ω, X ω ∂μ = 0)
    (hYcentered : ∫ ω, Y ω ∂μ = 0) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) =
      (∫ ω, X ω ^ 4 ∂μ) +
        6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) +
        ∫ ω, Y ω ^ 4 ∂μ := by
  rw [hXY.integral_add_pow_four hXmeas hYmeas hX4 hY4,
    hXcentered, hYcentered]
  ring

end ProbabilityTheory
