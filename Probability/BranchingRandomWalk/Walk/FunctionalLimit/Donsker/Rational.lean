module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Grid
public import Probability.Process.Path.FiniteDimensional
public import Probability.Process.Path.UnitInterval
public import Topology.Order.RationalUnitInterval

/-!
# Rational finite-dimensional Donsker limits

Every finite family of rational unit-interval times is projected from one
common uniform grid.  This converts the uniform-grid limit into the finite
marginals on a fixed countable dense time family.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Polygonal interpolation converges jointly at every finite family of
rational unit-interval times. -/
theorem tendstoInDistribution_normalizedLinearPath_rationalFinite_brownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (I : Finset RationalGrid.RationalUnitInterval) :
    TendstoInDistribution
      (fun n increment (q : I) =>
        normalizedLinearPath (fun n => Real.sqrt n) n increment
          (RationalGrid.unitCoe q : ℝ))
      atTop
      (fun ω => fun q : I =>
        B (unitIntervalToNNReal
          (RationalGrid.unitCoe q)) ω)
      (fun _ => independentIncrementLaw nu) P := by
  obtain ⟨blocks, hleft, hright, index, hindex⟩ :=
    RationalGrid.exists_unit_uniformGrid_of_finset I
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
    have hindex' : (RationalGrid.unitCoe q : ℝ) =
        (index q : ℝ) / (blocks.blocks : ℝ) := by
      calc
        (RationalGrid.unitCoe q : ℝ) =
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
        (RationalGrid.unitCoe q)) ω
    have htime : uniformGridTime step (index q) =
        unitIntervalToNNReal (RationalGrid.unitCoe q) := by
      apply NNReal.eq
      rw [coe_uniformGridTime]
      change (index q : ℝ) * (1 / (blocks.blocks : ℝ)) =
        (RationalGrid.unitCoe q : ℝ)
      have hindex' : (RationalGrid.unitCoe q : ℝ) =
          (index q : ℝ) / (blocks.blocks : ℝ) := by
        calc
          (RationalGrid.unitCoe q : ℝ) =
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
    (I : Finset RationalGrid.RationalUnitInterval) :
    TendstoInDistribution
      (fun n increment (q : I) =>
        normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n
          increment (RationalGrid.unitCoe q))
      atTop
      (Process.Path.finiteEvaluation
        (fun q : I => RationalGrid.unitCoe q) ∘
          continuousunitIntervalPath B hcontinuous)
      (fun _ => independentIncrementLaw nu) P := by
  convert
    tendstoInDistribution_normalizedLinearPath_rationalFinite_brownian
      nu hcentered hsecondMoment hB I using 1 <;> rfl

end ProbabilityTheory.RandomWalk
