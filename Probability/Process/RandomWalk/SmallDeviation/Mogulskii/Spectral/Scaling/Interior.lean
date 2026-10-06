/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Scaling.Upper
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Scaling.Lower

/-!
# Interior-start spectral limits

The principal sine weight is uniformly positive for starts that stay in the
interior of the interval.  This gives the matching lower rate and the complete
limit under the diffusive scale.
-/

open Filter Topology


@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Complete sharp limit for starting sites that stay uniformly inside the
Dirichlet ground state.  It needs only the diffusive scale condition and no
logarithmic width hypothesis. -/
theorem tendsto_scaledLog_remainingMass_of_sineWeight
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (c : ℝ) (hc : 0 < c)
    (hstart : ∀ n, c ≤ intervalSineWeight (interiorCount n) (start n)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (Kernel.remainingMass
          (intervalRademacherKernel (interiorCount n))
          (time n) (start n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  let width : ℕ → ℝ := fun n => ((interiorCount n + 1 : ℕ) : ℝ)
  let ratio : ℕ → ℝ := fun n => width n ^ 2 / (time n : ℝ)
  let eigenvalue : ℕ → ℝ := fun n => Real.cos (Real.pi / width n)
  let weight : ℕ → ℝ := fun n =>
    intervalSineWeight (interiorCount n) (start n)
  let lower : ℕ → ℝ := fun n =>
    width n ^ 2 * Real.log (eigenvalue n) +
      ratio n * Real.log (weight n)
  let upper : ℕ → ℝ := fun n =>
    width n ^ 2 * Real.log (eigenvalue n) +
      ratio n * Real.log (4 / (1 - eigenvalue n ^ time n))
  have hmain : Tendsto (fun n =>
      width n ^ 2 * Real.log (eigenvalue n)) atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [width, eigenvalue, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hratio' : Tendsto ratio atTop (nhds 0) := by
    simpa [ratio, width] using hratio
  have hratioNonneg : ∀ n, 0 ≤ ratio n := by
    intro n
    dsimp [ratio, width]
    positivity
  have hlogWeightLower : ∀ n, Real.log c ≤ Real.log (weight n) := by
    intro n
    exact Real.log_le_log hc (by simpa [weight] using hstart n)
  have hlogWeightUpper : ∀ n, Real.log (weight n) ≤ 0 := by
    intro n
    apply Real.log_nonpos
    · exact (intervalSineWeight_pos
        (Nat.zero_lt_of_lt (hcount n)) (start n)).le
    · exact intervalSineWeight_le_one _ _
  have hweightCorrection : Tendsto (fun n =>
      ratio n * Real.log (weight n)) atTop (nhds 0) := by
    have hlower : Tendsto (fun n => ratio n * Real.log c)
        atTop (nhds 0) := by
      simpa using hratio'.mul_const (Real.log c)
    have hupper : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    apply hlower.squeeze' hupper
    · exact Eventually.of_forall fun n => mul_le_mul_of_nonneg_left
        (hlogWeightLower n) (hratioNonneg n)
    · exact Eventually.of_forall fun n => mul_nonpos_of_nonneg_of_nonpos
        (hratioNonneg n) (hlogWeightUpper n)
  have hlowerTendsto : Tendsto lower atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa [lower] using hmain.add hweightCorrection
  have hupperCorrection : Tendsto (fun n =>
      ratio n * Real.log (4 / (1 - eigenvalue n ^ time n)))
      atTop (nhds 0) := by
    simpa [ratio, width, eigenvalue] using
      tendsto_scaledLog_geometricCorrection interiorCount time
        hcount htime hwidth hratio
  have hupperTendsto : Tendsto upper atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa [upper] using hmain.add hupperCorrection
  have hlower : ∀ n, lower n ≤
      ratio n * Real.log (Kernel.remainingMass
        (intervalRademacherKernel (interiorCount n))
        (time n) (start n)).toReal := by
    intro n
    simpa [lower, ratio, width, eigenvalue, weight] using
      main_add_logSineWeight_le_scaledLog_remainingMass
        (hcount n) (htime n) (start n)
  have hupper : ∀ n,
      ratio n * Real.log (Kernel.remainingMass
          (intervalRademacherKernel (interiorCount n))
          (time n) (start n)).toReal ≤ upper n := by
    intro n
    simpa [upper, ratio, width, eigenvalue] using
      scaledLog_remainingMass_le_main_add_geometricCorrection
        (hcount n) (htime n) (start n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerTendsto hupperTendsto hlower hupper

/-- Process-law form of the complete sharp interior-start limit. -/
theorem tendsto_scaledLog_rademacherIncrement_of_sineWeight
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (c : ℝ) (hc : 0 < c)
    (hstart : ∀ n, c ≤ intervalSineWeight (interiorCount n) (start n)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (ENNReal.toReal
          (iidSequenceLaw rademacherMeasure
        {increment | InClosedInterval 1 (interiorCount n)
              (time n) (intervalSite (start n)) increment})))
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  have h := tendsto_scaledLog_remainingMass_of_sineWeight
    interiorCount time start hcount htime hwidth hratio c hc hstart
  convert h using 1
  funext n
  congr 2
  exact congrArg ENNReal.toReal
    (intervalRademacherKernel_pow_apply_univ_eq_randomWalkInterval
      (interiorCount n) (time n) (start n)).symm


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
