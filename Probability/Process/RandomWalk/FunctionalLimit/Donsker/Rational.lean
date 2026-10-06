/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalGrid.Interval
public import Order.Interval.RationalCoordinate.UnitInterval
public import Mathlib.Topology.UnitInterval
public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Grid
public import Probability.Process.Path.FiniteDimensional
public import Probability.Process.Path.UnitInterval
public import Topology.Order.UnitInterval.Rational

/-!
# Rational finite-dimensional Donsker limits

Every finite family of rational unit-interval times is projected from one
common uniform grid.  This converts the uniform-grid limit into the finite
marginals on a fixed countable dense time family.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Polygonal interpolation converges jointly at every finite family of
rational unit-interval times. -/
theorem tendstoInDistribution_normalizedLinearPath_rationalFinite_brownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (I : Finset RationalCoordinate.UnitInterval) :
    TendstoInDistribution
      (fun n increment (q : I) =>
        normalizedLinearPath (fun n => Real.sqrt n) n increment
          (RationalCoordinate.toUnitInterval q : ℝ))
      atTop
      (fun ω => fun q : I =>
        B (unitIntervalToNNReal
          (RationalCoordinate.toUnitInterval q)) ω)
      (fun _ => iidSequenceLaw nu) P := by
  obtain ⟨blocks, hleft, hright, index, hindex⟩ :=
    RationalGrid.exists_uniformGrid_of_intervalFinset
      (left := 0) (right := 1) (by norm_num) I
  let restrict : (blocks.Index → ℝ) → (I → ℝ) :=
    fun value q => value (index q)
  let step : NNReal := ⟨1 / (blocks.blocks : ℝ), by positivity⟩
  have hrestrict : Continuous restrict := by
    rw [continuous_pi_iff]
    intro q
    exact continuous_apply (index q)
  have hgrid :=
    tendstoInDistribution_normalizedLinearPath_uniformGrid_brownian
      nu hcentered hsecondMoment hB blocks.blocks_pos
  have hprojected := hgrid.continuous_comp hrestrict
  apply hprojected.congr
  · intro n
    filter_upwards [] with increment
    funext q
    have hindex' : (RationalCoordinate.toUnitInterval q : ℝ) =
        (index q : ℝ) / (blocks.blocks : ℝ) := by
      calc
        (RationalCoordinate.toUnitInterval q : ℝ) =
            blocks.point (index q) := hindex q
        _ = (index q : ℝ) / (blocks.blocks : ℝ) := by
          simp [UniformGrid.point, hleft, hright]
    exact congrArg
      (normalizedLinearPath (fun n => Real.sqrt n) n increment)
      hindex'.symm
  · filter_upwards [] with ω
    funext q
    change B (uniformGridTime step (index q)) ω =
      B (unitIntervalToNNReal
        (RationalCoordinate.toUnitInterval q)) ω
    have htime : uniformGridTime step (index q) =
        unitIntervalToNNReal (RationalCoordinate.toUnitInterval q) := by
      apply NNReal.eq
      rw [coe_uniformGridTime]
      change (index q : ℝ) * (1 / (blocks.blocks : ℝ)) =
        (RationalCoordinate.toUnitInterval q : ℝ)
      have hindex' : (RationalCoordinate.toUnitInterval q : ℝ) =
          (index q : ℝ) / (blocks.blocks : ℝ) := by
        calc
          (RationalCoordinate.toUnitInterval q : ℝ) =
              blocks.point (index q) := hindex q
          _ = (index q : ℝ) / (blocks.blocks : ℝ) := by
            simp [UniformGrid.point, hleft, hright]
      simpa only [div_eq_mul_inv, one_mul] using hindex'.symm
    rw [htime]

/-- The rational finite-dimensional limit with the Brownian limit bundled
as a continuous unit-interval path. -/
theorem tendstoInDistribution_normalizedLinearPath_rationalFinite_continuousPath
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hcontinuous : ∀ ω, Continuous (B · ω))
    (I : Finset RationalCoordinate.UnitInterval) :
    TendstoInDistribution
      (fun n increment (q : I) =>
        normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n
          increment (RationalCoordinate.toUnitInterval q))
      atTop
      (Process.Path.finiteEvaluation
        (fun q : I => RationalCoordinate.toUnitInterval q) ∘
          continuousunitIntervalPath B hcontinuous)
      (fun _ => iidSequenceLaw nu) P := by
  convert
    tendstoInDistribution_normalizedLinearPath_rationalFinite_brownian
      nu hcentered hsecondMoment hB I using 1 <;> rfl

end ProbabilityTheory.RandomWalk
