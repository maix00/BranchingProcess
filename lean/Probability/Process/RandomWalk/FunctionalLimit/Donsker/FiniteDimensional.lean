/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Block.Scale
public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.CLT
public import Probability.ConvergenceInDistribution.Independence
public import Topology.Algebra.BigOperators.PartialSum

/-!
# Finite-dimensional limits for Donsker's theorem

This file develops the finite-dimensional input for the functional central
limit theorem.  The block lengths are proportional to the full time horizon;
they are therefore distinct from the subdiffusive blocks used in Mogulskii
estimates.
-/

open Filter MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- The endpoint of the first `floor (fraction * n)` increments, normalized
by `sqrt n`, converges to a standard Gaussian scaled by `sqrt fraction`.

This is the one-coordinate building block for finite-dimensional Donsker
convergence. -/
theorem tendstoInDistribution_proportionalPartialSum
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {fraction : ℝ} (hfraction : 0 < fraction) :
    TendstoInDistribution
      (fun n increment =>
        AdditivePath.displacement (proportionalBlockLength fraction n) increment /
          Real.sqrt n)
      atTop (fun x => x * Real.sqrt fraction)
      (fun _ => iidSequenceLaw nu) (gaussianReal 0 1) := by
  let length : ℕ → ℕ := proportionalBlockLength fraction
  have hlength : Tendsto length atTop atTop := by
    exact tendsto_nat_floor_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hfraction)
  have hnormalized :=
    TendstoInDistribution.comp_tendsto
      (tendstoInDistribution_normalizedPartialSum nu hcentered hsecondMoment)
      hlength
  have hcoefficient : TendstoInMeasure (iidSequenceLaw nu)
      (fun n (_ : ℕ → ℝ) =>
        Real.sqrt (length n) / Real.sqrt n)
      atTop (fun _ => Real.sqrt fraction) := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => by fun_prop)
    filter_upwards [] with increment
    have hratio := Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_proportionalBlockLength_div hfraction)
    apply hratio.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    change Real.sqrt ((length n : ℝ) / (n : ℝ)) =
      Real.sqrt (length n) / Real.sqrt n
    rw [Real.sqrt_div (Nat.cast_nonneg _)]
  have hproduct := hnormalized.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun pair : ℝ × ℝ => pair.1 * pair.2) (by fun_prop)
    hcoefficient (fun _ => by fun_prop)
  apply hproduct.congr_eventually
  · filter_upwards [eventually_proportionalBlockLength_pos hfraction,
      eventually_gt_atTop 0] with n hnLength hn
    filter_upwards [] with increment
    have hsqrtLength : Real.sqrt (length n) ≠ 0 :=
      Real.sqrt_ne_zero'.2 (by exact_mod_cast hnLength)
    have hsqrtN : Real.sqrt n ≠ 0 :=
      Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)
    dsimp only [length]
    field_simp [hsqrtLength, hsqrtN]
  · intro n
    exact (displacement_measurable _).div_const _ |>.aemeasurable

/-- A deterministic shift of the proportional block does not alter its
limit.  The starting index may depend arbitrarily on the time horizon; this
is the form used for consecutive increments between observation times. -/
theorem tendstoInDistribution_proportionalBlockSum
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    (start : ℕ → ℕ) {fraction : ℝ} (hfraction : 0 < fraction) :
    TendstoInDistribution
      (fun n increment =>
        AdditivePath.blockSum (start n) (proportionalBlockLength fraction n) increment /
          Real.sqrt n)
      atTop (fun x => x * Real.sqrt fraction)
      (fun _ => iidSequenceLaw nu) (gaussianReal 0 1) := by
  apply (tendstoInDistribution_proportionalPartialSum nu hcentered
    hsecondMoment hfraction).congr_map_eventually
  · filter_upwards [] with n
    let length := proportionalBlockLength fraction n
    have hblock := iidSequenceLaw_map_blockSum nu (start n) length
    have hdiv : Measurable (fun x : ℝ => x / Real.sqrt n) :=
      measurable_id.div_const _
    calc
      (iidSequenceLaw nu).map
          (fun increment => AdditivePath.displacement length increment / Real.sqrt n) =
        ((iidSequenceLaw nu).map (AdditivePath.displacement length)).map
          (fun x => x / Real.sqrt n) := by
            simpa only [Function.comp_def] using
              (Measure.map_map hdiv (displacement_measurable length)).symm
      _ = ((iidSequenceLaw nu).map
            (AdditivePath.blockSum (start n) length)).map
            (fun x => x / Real.sqrt n) := by
              rw [show (iidSequenceLaw nu).map
                  (AdditivePath.blockSum (start n) length) =
                  (iidSequenceLaw nu).map (AdditivePath.displacement length) by
                simpa [iidSequenceLaw] using hblock]
      _ = (iidSequenceLaw nu).map
          (fun increment =>
            AdditivePath.blockSum (start n) length increment / Real.sqrt n) := by
        simpa only [Function.comp_def] using
          Measure.map_map hdiv (blockSum_measurable (start n) length)
  · intro n
    exact (blockSum_measurable (start n)
      (proportionalBlockLength fraction n)).div_const _ |>.aemeasurable

/-- A fixed finite vector of consecutive proportional blocks converges to
independent Gaussian increments. -/
theorem tendstoInDistribution_proportionalBlockSums
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {fraction : ℝ} (hfraction : 0 < fraction) (blocks : ℕ) :
    TendstoInDistribution
      (fun n increment (j : Fin blocks) =>
        let length := proportionalBlockLength fraction n
        AdditivePath.blockSum (j * length) length increment / Real.sqrt n)
      atTop
      (fun z (j : Fin blocks) => z j * Real.sqrt fraction)
      (fun _ => iidSequenceLaw nu)
      (Measure.pi fun _ : Fin blocks => gaussianReal 0 1) := by
  let length : ℕ → ℕ := proportionalBlockLength fraction
  let X : ℕ → Fin blocks → (ℕ → ℝ) → ℝ := fun n j increment =>
    AdditivePath.blockSum (j * length n) (length n) increment / Real.sqrt n
  let Z : Fin blocks → ℝ → ℝ := fun _ z => z * Real.sqrt fraction
  have hcoordinate (j : Fin blocks) :
      TendstoInDistribution (fun n => X n j) atTop (Z j)
        (fun _ => iidSequenceLaw nu) (gaussianReal 0 1) := by
    simpa only [X, Z, length] using
      tendstoInDistribution_proportionalBlockSum nu hcentered
        hsecondMoment (fun n => j * proportionalBlockLength fraction n)
        hfraction
  have hindep (n : ℕ) : iIndepFun (X n) (iidSequenceLaw nu) := by
    have h := iIndepFun_consecutiveBlockSums nu blocks (length n)
    exact h.comp (fun _ x => x / Real.sqrt n)
      (fun _ => measurable_id.div_const _)
  simpa only [X, Z, length] using TendstoInDistribution.pi_of_iIndepFun
    hcoordinate (fun _ => by fun_prop) hindep

/-- The normalized positions at the endpoints of a fixed equal partition
converge to the cumulative sums of independent Gaussian increments. -/
theorem tendstoInDistribution_proportionalBlockEndpoints
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {fraction : ℝ} (hfraction : 0 < fraction) (blocks : ℕ) :
    TendstoInDistribution
      (fun n increment (j : Fin (blocks + 1)) =>
        AdditivePath.displacement (j * proportionalBlockLength fraction n) increment /
          Real.sqrt n)
      atTop
      (fun z => Fin.partialSum
        (fun j : Fin blocks => z j * Real.sqrt fraction))
      (fun _ => iidSequenceLaw nu)
      (Measure.pi fun _ : Fin blocks => gaussianReal 0 1) := by
  have hblocks := tendstoInDistribution_proportionalBlockSums nu hcentered
    hsecondMoment hfraction blocks
  have hcumulative := hblocks.continuous_comp
    (Fin.continuous_partialSum blocks)
  apply hcumulative.congr_eventually
  · filter_upwards [] with n
    filter_upwards [] with increment
    funext j
    rw [← partialSum_blockSum increment j]
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using
      (Fin.partialSum_smul (R := ℝ) (M := ℝ) ((Real.sqrt n)⁻¹)
        (fun k : Fin blocks =>
          AdditivePath.blockSum (k * proportionalBlockLength fraction n)
            (proportionalBlockLength fraction n) increment) j)
  · intro n
    exact (Measurable.of_eval fun j =>
      (displacement_measurable _).div_const _).aemeasurable

end ProbabilityTheory.RandomWalk
