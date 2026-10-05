/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.FiniteDimensional
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Brownian laws on uniform grids

This file identifies cumulative independent Gaussian increments with the
finite-dimensional laws supplied by mathlib's Brownian-motion interface.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- The uniform nonnegative-time grid with spacing `step`. -/
def uniformGridTime (step : NNReal) {blocks : ℕ} (j : Fin (blocks + 1)) :
    NNReal := (j : ℕ) • step

@[simp]
theorem coe_uniformGridTime (step : NNReal) {blocks : ℕ}
    (j : Fin (blocks + 1)) :
    (uniformGridTime step j : ℝ) = (j : ℕ) * (step : ℝ) := by
  simp [uniformGridTime]

theorem monotone_uniformGridTime (step : NNReal) (blocks : ℕ) :
    Monotone (uniformGridTime step : Fin (blocks + 1) → NNReal) := by
  intro i j hij
  exact nsmul_le_nsmul_left step.2 (Fin.mk_le_mk.mp hij)

/-- Brownian increments over a uniform grid are independent. -/
theorem IsPreBrownianReal.iIndepFun_uniformGridIncrements
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (step : NNReal) (blocks : ℕ) :
    iIndepFun (fun j : Fin blocks => fun ω =>
      B (uniformGridTime step j.succ) ω -
        B (uniformGridTime step j.castSucc) ω) P :=
  hB.hasIndepIncrements blocks (uniformGridTime step)
    (monotone_uniformGridTime step blocks)

/-- Every Brownian increment on a uniform grid has the centered Gaussian law
whose variance is the grid spacing. -/
theorem IsPreBrownianReal.hasLaw_uniformGridIncrement
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (step : NNReal) {blocks : ℕ} (j : Fin blocks) :
    HasLaw
      (fun ω => B (uniformGridTime step j.succ) ω -
        B (uniformGridTime step j.castSucc) ω)
      (gaussianReal 0 step) P := by
  have h := hB.hasLaw_sub (uniformGridTime step j.succ)
    (uniformGridTime step j.castSucc)
  have hdist : nndist
      ((uniformGridTime step j.succ : NNReal) : ℝ)
      ((uniformGridTime step j.castSucc : NNReal) : ℝ) = step := by
    rw [← NNReal.coe_inj]
    simp only [coe_nndist, uniformGridTime, Fin.val_succ, Fin.val_castSucc]
    rw [Real.dist_eq]
    have hmono : ((j : ℕ) • step : NNReal) ≤
        ((j : ℕ) + 1) • step :=
      nsmul_le_nsmul_left step.2 (Nat.le_succ _)
    rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hmono))]
    norm_cast
    rw [add_nsmul, one_nsmul, add_tsub_cancel_left]
  convert h using 1
  congr 1
  exact hdist.symm

/-- The complete vector of Brownian increments on a uniform grid has the
corresponding product Gaussian law. -/
theorem IsPreBrownianReal.hasLaw_uniformGridIncrements
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (step : NNReal) (blocks : ℕ) :
    HasLaw
      (fun ω => fun j : Fin blocks =>
        B (uniformGridTime step j.succ) ω -
          B (uniformGridTime step j.castSucc) ω)
      (Measure.pi fun _ : Fin blocks => gaussianReal 0 step) P :=
  (ProbabilityTheory.RandomWalk.IsPreBrownianReal.iIndepFun_uniformGridIncrements
    hB step blocks).hasLaw_pi
    (fun j => ProbabilityTheory.RandomWalk.IsPreBrownianReal.hasLaw_uniformGridIncrement
      hB step j)

/-- Brownian values on a uniform grid are cumulative independent Gaussian
increments. -/
theorem IsPreBrownianReal.hasLaw_uniformGrid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (step : NNReal) (blocks : ℕ) :
    HasLaw
      (fun ω => fun j : Fin (blocks + 1) => B (uniformGridTime step j) ω)
      ((Measure.pi fun _ : Fin blocks => gaussianReal 0 step).map
        (Fin.partialSum : (Fin blocks → ℝ) →
          Fin (blocks + 1) → ℝ)) P := by
  have hincrements :=
    ProbabilityTheory.RandomWalk.IsPreBrownianReal.hasLaw_uniformGridIncrements
      hB step blocks
  have hcumulative : HasLaw
      (Fin.partialSum ∘ fun ω => fun j : Fin blocks =>
        B (uniformGridTime step j.succ) ω -
          B (uniformGridTime step j.castSucc) ω)
      ((Measure.pi fun _ : Fin blocks => gaussianReal 0 step).map
        (Fin.partialSum : (Fin blocks → ℝ) →
          Fin (blocks + 1) → ℝ)) P :=
    (hasLaw_map (continuous_partialSum blocks).measurable.aemeasurable).comp
      hincrements
  apply hcumulative.congr
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hzero
  funext j
  change B (uniformGridTime step j) ω =
    Fin.partialSum
      (fun k : Fin blocks =>
        (fun q : Fin (blocks + 1) => B (uniformGridTime step q) ω) k.succ -
          (fun q : Fin (blocks + 1) => B (uniformGridTime step q) ω) k.castSucc) j
  have htel := Fin.partialSum_differences
    (n := blocks)
    (fun q : Fin (blocks + 1) => B (uniformGridTime step q) ω) j
  rw [htel]
  simp [uniformGridTime, hzero]

/-- Scaling independent standard Gaussians by the square root of a
nonnegative spacing produces the product law of Brownian increments over
that spacing. -/
theorem map_pi_gaussianReal_mul_sqrt
    (step : NNReal) (blocks : ℕ) :
    (Measure.pi fun _ : Fin blocks => gaussianReal 0 1).map
        (fun z j => z j * Real.sqrt (step : ℝ)) =
      Measure.pi fun _ : Fin blocks => gaussianReal 0 step := by
  rw [Measure.pi_map_pi (fun _ => (by fun_prop :
    AEMeasurable (fun x : ℝ => x * Real.sqrt (step : ℝ))
      (gaussianReal 0 1)))]
  congr 1 with j
  rw [gaussianReal_map_mul_const]
  congr 2
  · simp
  · rw [← NNReal.coe_inj]
    simp

/-- Uniform-grid Brownian values realized from a product of standard
Gaussians by scaling each increment and taking cumulative sums. -/
theorem IsPreBrownianReal.hasLaw_uniformGrid_of_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (step : NNReal) (blocks : ℕ) :
    HasLaw
      (fun ω => fun j : Fin (blocks + 1) => B (uniformGridTime step j) ω)
      ((Measure.pi fun _ : Fin blocks => gaussianReal 0 1).map
        (fun z => Fin.partialSum
          (fun j : Fin blocks => z j * Real.sqrt (step : ℝ)))) P := by
  have hgrid :=
    ProbabilityTheory.RandomWalk.IsPreBrownianReal.hasLaw_uniformGrid
      hB step blocks
  refine ⟨hgrid.aemeasurable, ?_⟩
  rw [hgrid.map_eq, ← map_pi_gaussianReal_mul_sqrt step blocks,
    Measure.map_map]
  · rfl
  · exact (continuous_partialSum blocks).measurable
  · exact Measurable.of_eval fun _ => by fun_prop

/-- Equal-partition random-walk endpoints converge jointly to Brownian values
at the matching uniform grid. -/
theorem tendstoInDistribution_proportionalBlockEndpoints_brownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    {fraction : ℝ} (hfraction : 0 < fraction) (blocks : ℕ) :
    TendstoInDistribution
      (fun n increment (j : Fin (blocks + 1)) =>
        AdditivePath.displacement (j * proportionalBlockLength fraction n) increment /
          Real.sqrt n)
      atTop
      (fun ω => fun j : Fin (blocks + 1) =>
        B (uniformGridTime ⟨fraction, hfraction.le⟩ j) ω)
      (fun _ => independentIncrementLaw nu) P := by
  have h := tendstoInDistribution_proportionalBlockEndpoints nu hcentered
    hsecondMoment hfraction blocks
  exact h.congr_limit_hasLaw (by
    convert
      (ProbabilityTheory.RandomWalk.IsPreBrownianReal.hasLaw_uniformGrid_of_standardGaussian
        hB ⟨fraction, hfraction.le⟩ blocks) using 1
    congr 1)

end ProbabilityTheory.RandomWalk
