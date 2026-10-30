/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Mathlib.Probability.BrownianMotion.Basic
import Topology.Algebra.BigOperators.PartialSum

/-!
# Brownian finite-dimensional laws on uniform grids

For a step size $h\ge0$ and $m$ blocks, let $t_j=jh$ for
$0\le j\le m$. This module expresses the Brownian grid values as cumulative
independent Gaussian increments.

## Public declarations

- `ProbabilityTheory.uniformGridTime`, `ProbabilityTheory.coe_uniformGridTime`:
  the nonnegative-time grid $t_j=jh$ and its real-valued formula.
- `ProbabilityTheory.IsPreBrownianReal.hasLaw_uniformGridIncrements`:
  $(B(t_{j+1})-B(t_j))_{j<m}$ has product law $\prod_{j<m}N(0,h)$.
- `ProbabilityTheory.IsPreBrownianReal.hasLaw_uniformGrid`:
  $(B(t_j))_{j\le m}$ has the law of cumulative independent $N(0,h)$
  increments.
- `ProbabilityTheory.IsPreBrownianReal.hasLaw_uniformGrid_of_standardGaussian`:
  the same grid values are realized by cumulative sums of independent
  standard Gaussians multiplied by $\sqrt h$.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The `j`-th point of the nonnegative-time grid with spacing `step`. -/
def uniformGridTime (step : NNReal) {blocks : ℕ} (j : Fin (blocks + 1)) :
    NNReal := (j : ℕ) • step

/-- The real-valued formula for a nonnegative-time uniform grid point. -/
@[simp]
theorem coe_uniformGridTime (step : NNReal) {blocks : ℕ}
    (j : Fin (blocks + 1)) :
    (uniformGridTime step j : ℝ) = (j : ℕ) * (step : ℝ) := by
  simp [uniformGridTime]

private lemma monotone_uniformGridTime (step : NNReal) (blocks : ℕ) :
    Monotone (uniformGridTime step : Fin (blocks + 1) → NNReal) := by
  intro i j hij
  exact nsmul_le_nsmul_left step.2 (Fin.mk_le_mk.mp hij)

namespace IsPreBrownianReal

/-- Every Brownian increment on a uniform grid has the centered Gaussian law
whose variance is the grid spacing. -/
private lemma hasLaw_uniformGridIncrement
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
theorem hasLaw_uniformGridIncrements
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (step : NNReal) (blocks : ℕ) :
    HasLaw
      (fun ω => fun j : Fin blocks =>
        B (uniformGridTime step j.succ) ω -
          B (uniformGridTime step j.castSucc) ω)
      (Measure.pi fun _ : Fin blocks => gaussianReal 0 step) P :=
  (hB.hasIndepIncrements blocks (uniformGridTime step)
    (monotone_uniformGridTime step blocks)).hasLaw_pi
    (fun j => hasLaw_uniformGridIncrement hB step j)

/-- Brownian values on a uniform grid are cumulative independent Gaussian
increments. -/
theorem hasLaw_uniformGrid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (step : NNReal) (blocks : ℕ) :
    HasLaw
      (fun ω => fun j : Fin (blocks + 1) => B (uniformGridTime step j) ω)
      ((Measure.pi fun _ : Fin blocks => gaussianReal 0 step).map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ)) P := by
  have hincrements := hB.hasLaw_uniformGridIncrements step blocks
  have hcumulative : HasLaw
      (Fin.partialSum ∘ fun ω => fun j : Fin blocks =>
        B (uniformGridTime step j.succ) ω -
          B (uniformGridTime step j.castSucc) ω)
      ((Measure.pi fun _ : Fin blocks => gaussianReal 0 step).map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ)) P :=
    (hasLaw_map (Fin.continuous_partialSum blocks).measurable.aemeasurable).comp
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

end IsPreBrownianReal

/-- Scaling a finite product of standard Gaussians by `sqrt step` gives the
product law of Brownian increments at that spacing. -/
private lemma map_pi_gaussianReal_mul_sqrt
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

namespace IsPreBrownianReal

/-- Uniform-grid Brownian values realized from product standard Gaussians
by scaling the increments and taking cumulative sums. -/
theorem hasLaw_uniformGrid_of_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (step : NNReal) (blocks : ℕ) :
    HasLaw
      (fun ω => fun j : Fin (blocks + 1) => B (uniformGridTime step j) ω)
      ((Measure.pi fun _ : Fin blocks => gaussianReal 0 1).map
        (fun z => Fin.partialSum
          (fun j : Fin blocks => z j * Real.sqrt (step : ℝ)))) P := by
  have hgrid := hB.hasLaw_uniformGrid step blocks
  refine ⟨hgrid.aemeasurable, ?_⟩
  rw [hgrid.map_eq, ← map_pi_gaussianReal_mul_sqrt step blocks,
    Measure.map_map]
  · rfl
  · exact (Fin.continuous_partialSum blocks).measurable
  · exact Measurable.of_eval fun _ => by fun_prop

end IsPreBrownianReal

end ProbabilityTheory

end
