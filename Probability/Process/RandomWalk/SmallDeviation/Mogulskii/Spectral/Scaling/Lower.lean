/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Asymptotics
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.SurvivalBounds
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Variable-scale spectral lower bound

The finite-interval sine eigenfunction gives the exact `-π² / 2` lower
rate when both the interval width and elapsed time vary.  The starting sites
are abstract; only a uniform positive lower bound on their ground-state
weight is required.
-/

open Filter Topology

open Combinatorics.Branching.Walk

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Pointwise lower bound obtained from the positive principal
eigenfunction. -/
theorem main_add_logSineWeight_le_scaledLog_remainingMass
    {interiorCount time : ℕ} (hcount : 1 < interiorCount)
    (htime : 0 < time) (start : Fin interiorCount) :
    ((interiorCount + 1 : ℕ) : ℝ) ^ 2 *
          Real.log (Real.cos
            (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))) +
        ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
          Real.log (intervalSineWeight interiorCount start) ≤
      ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
        Real.log (Kernel.remainingMass
          (intervalRademacherKernel interiorCount) time start).toReal := by
  let width : ℝ := ((interiorCount + 1 : ℕ) : ℝ)
  let ratio : ℝ := width ^ 2 / (time : ℝ)
  let eigenvalue : ℝ := Real.cos (Real.pi / width)
  let weight : ℝ := intervalSineWeight interiorCount start
  let mass : ENNReal := Kernel.remainingMass
    (intervalRademacherKernel interiorCount) time start
  have heigenvalue : 0 < eigenvalue := by
    simpa [eigenvalue, width] using intervalEigenvalue_pos hcount
  have hweight : 0 < weight := by
    simpa [weight] using intervalSineWeight_pos
      (Nat.zero_lt_of_lt hcount) start
  have hmass : ENNReal.ofReal (weight * eigenvalue ^ time) ≤ mass := by
    obtain ⟨lower, _hlowerPos, hlower, _hupper⟩ :=
      intervalKernel_pow_rowSum_bounds (Nat.zero_lt_of_lt hcount) time start
    have hmassEq : mass = ENNReal.ofReal
        (∑ finish, (intervalKernel interiorCount ^ time) start finish) := by
      dsimp [mass, Kernel.remainingMass]
      rw [intervalRademacherKernel_eq_ofRealMatrix,
        intervalKernel_pow_apply_univ]
    rw [hmassEq]
    apply ENNReal.ofReal_le_ofReal
    simpa [weight, eigenvalue, width, Nat.cast_add, Nat.cast_one,
      mul_comm] using hlower
  have hmassTop : mass ≠ ⊤ := by
    exact ne_of_lt ((Kernel.remainingMass_le_one
      (intervalRademacherKernel interiorCount) time start).trans_lt
        ENNReal.one_lt_top)
  have hproductPos : 0 < weight * eigenvalue ^ time :=
    mul_pos hweight (pow_pos heigenvalue _)
  have hreal : weight * eigenvalue ^ time ≤ mass.toReal := by
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hmassTop).2 hmass
    simpa [ENNReal.toReal_ofReal hproductPos.le] using this
  have hlog := Real.log_le_log hproductPos hreal
  rw [Real.log_mul hweight.ne' (pow_pos heigenvalue _).ne',
    Real.log_pow] at hlog
  have hratioNonneg : 0 ≤ ratio := by
    dsimp [ratio, width]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog hratioNonneg
  calc
    width ^ 2 * Real.log eigenvalue + ratio * Real.log weight =
        ratio * (Real.log weight +
          (time : ℝ) * Real.log eigenvalue) := by
      dsimp [ratio]
      field_simp [(Nat.cast_ne_zero.mpr htime.ne')]
      ring
    _ ≤ ratio * Real.log mass.toReal := hscaled
    _ = _ := by rfl

/-- Variable finite intervals whose widths diverge and whose elapsed times
are large compared with the squared widths have the sharp Rademacher
small-deviation lower rate. -/
theorem neg_pi_sq_div_two_le_liminf_scaledLog_remainingMass
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
    -(Real.pi ^ 2) / 2 ≤ atTop.liminf (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (Kernel.remainingMass
          (intervalRademacherKernel (interiorCount n))
          (time n) (start n)).toReal) := by
  let width : ℕ → ℝ := fun n => ((interiorCount n + 1 : ℕ) : ℝ)
  let ratio : ℕ → ℝ := fun n => width n ^ 2 / (time n : ℝ)
  let eigenvalue : ℕ → ℝ := fun n =>
    Real.cos (Real.pi / width n)
  let weight : ℕ → ℝ := fun n =>
    intervalSineWeight (interiorCount n) (start n)
  let mass : ℕ → ENNReal := fun n => Kernel.remainingMass
    (intervalRademacherKernel (interiorCount n)) (time n) (start n)
  have hweight : ∀ n, 0 < weight n := fun n =>
    hc.trans_le (by simpa [weight] using hstart n)
  have hmassTop : ∀ n, mass n ≠ ⊤ := by
    intro n
    exact ne_of_lt ((Kernel.remainingMass_le_one
      (intervalRademacherKernel (interiorCount n)) (time n) (start n)).trans_lt
        ENNReal.one_lt_top)
  have hlog : ∀ n,
      width n ^ 2 * Real.log (eigenvalue n) +
          ratio n * Real.log (weight n) ≤
        ratio n * Real.log (mass n).toReal := by
    intro n
    simpa [width, ratio, eigenvalue, weight, mass] using
      main_add_logSineWeight_le_scaledLog_remainingMass
        (hcount n) (htime n) (start n)
  have hmain : Tendsto (fun n =>
      width n ^ 2 * Real.log (eigenvalue n)) atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [width, eigenvalue, Function.comp_apply, Nat.cast_add,
      Nat.cast_one]
  have hlogWeightLower : ∀ n, Real.log c ≤ Real.log (weight n) := by
    intro n
    exact Real.log_le_log hc (by simpa [weight] using hstart n)
  have hlogWeightUpper : ∀ n, Real.log (weight n) ≤ 0 := by
    intro n
    apply Real.log_nonpos (hweight n).le
    exact intervalSineWeight_le_one _ _
  have herror : Tendsto (fun n => ratio n * Real.log (weight n))
      atTop (nhds 0) := by
    have hratioNonneg : ∀ n, 0 ≤ ratio n := by
      intro n
      dsimp [ratio, width]
      positivity
    have hratio' : Tendsto ratio atTop (nhds 0) := by
      simpa [ratio, width] using hratio
    have hlower : Tendsto (fun n => ratio n * Real.log c)
        atTop (nhds 0) := by
      simpa using hratio'.mul_const (Real.log c)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower (tendsto_const_nhds)
      (fun n => mul_le_mul_of_nonneg_left
        (hlogWeightLower n) (hratioNonneg n))
      (fun n => mul_nonpos_of_nonneg_of_nonpos
        (hratioNonneg n) (hlogWeightUpper n))
  have hleft : Tendsto (fun n =>
      width n ^ 2 * Real.log (eigenvalue n) +
        ratio n * Real.log (weight n)) atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa using hmain.add herror
  have hrightUpper : ∀ᶠ n in atTop,
      ratio n * Real.log (mass n).toReal ≤ 0 :=
    Eventually.of_forall fun n => by
      have hmassOne := Kernel.remainingMass_le_one
        (intervalRademacherKernel (interiorCount n)) (time n) (start n)
      have hrealOne : (mass n).toReal ≤ 1 :=
        (ENNReal.toReal_le_toReal (hmassTop n) ENNReal.one_ne_top).2
          (by simpa [mass] using hmassOne)
      exact mul_nonpos_of_nonneg_of_nonpos (by
        dsimp [ratio, width]
        positivity) (Real.log_nonpos ENNReal.toReal_nonneg hrealOne)
  calc
    -(Real.pi ^ 2) / 2 = atTop.liminf (fun n =>
        width n ^ 2 * Real.log (eigenvalue n) +
          ratio n * Real.log (weight n)) := hleft.liminf_eq.symm
    _ ≤ atTop.liminf (fun n =>
        ratio n * Real.log (mass n).toReal) := by
      exact Filter.liminf_le_liminf (Eventually.of_forall hlog)
        hleft.isBoundedUnder_ge
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop hrightUpper)
    _ = _ := rfl

/-- The variable-scale spectral lower bound stated for the actual
`RandomWalk` process law.  This is the process-level form used by later
small-deviation arguments. -/
theorem neg_pi_sq_div_two_le_liminf_scaledLog_rademacherIncrement
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
    -(Real.pi ^ 2) / 2 ≤ atTop.liminf (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (ENNReal.toReal
          (independentIncrementLaw rademacherMeasure
        {increment | InClosedInterval 1 (interiorCount n)
              (time n) (intervalSite (start n)) increment}))) := by
  have h := neg_pi_sq_div_two_le_liminf_scaledLog_remainingMass
    interiorCount time start hcount htime hwidth hratio c hc hstart
  convert h using 1
  apply congrArg (fun f => atTop.liminf f)
  funext n
  congr 2
  exact congrArg ENNReal.toReal
    (intervalRademacherKernel_pow_apply_univ_eq_randomWalkInterval
      (interiorCount n) (time n) (start n)).symm

/-- Centered odd-cardinality intervals have ground-state weight exactly one,
so the abstract starting-weight hypothesis disappears. -/
theorem neg_pi_sq_div_two_le_liminf_scaledLog_centeredRademacherProcess
    (radius time : ℕ → ℕ)
    (hradius : ∀ n, 0 < radius n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0)) :
    -(Real.pi ^ 2) / 2 ≤ atTop.liminf (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (ENNReal.toReal
          (independentIncrementLaw rademacherMeasure
            {increment | InClosedInterval 1 (2 * radius n + 1) (time n)
              (intervalSite (⟨radius n, by omega⟩ : Fin (2 * radius n + 1)))
              increment}))) := by
  let interiorCount : ℕ → ℕ := fun n => 2 * radius n + 1
  let start : ∀ n, Fin (interiorCount n) := fun n =>
    ⟨radius n, by dsimp [interiorCount]; omega⟩
  have hcount : ∀ n, 1 < interiorCount n := by
    intro n
    have := hradius n
    dsimp [interiorCount]
    omega
  have hcountWidth : ∀ n, interiorCount n + 1 = 2 * (radius n + 1) := by
    intro n
    dsimp [interiorCount]
    omega
  have hweight : ∀ n,
      (1 : ℝ) ≤ intervalSineWeight (interiorCount n) (start n) := by
    intro n
    simp [interiorCount, start]
  have hwidth' : Tendsto
      (fun n => ((interiorCount n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [hcountWidth] using hwidth
  have hratio' : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0) := by
    simpa only [hcountWidth] using hratio
  simpa only [hcountWidth, interiorCount, start, Nat.cast_add,
    Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
    (neg_pi_sq_div_two_le_liminf_scaledLog_rademacherIncrement
      interiorCount time start hcount htime hwidth' hratio'
      1 zero_lt_one hweight)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
