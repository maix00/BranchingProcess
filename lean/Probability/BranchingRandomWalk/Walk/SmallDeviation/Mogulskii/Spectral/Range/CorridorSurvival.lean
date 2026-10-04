/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Corridor.Interpolation
public import Probability.BranchingRandomWalk.Walk.Path.Corridor.Interpolation
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Range.Basic
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.PathSurvival
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.UpperBound
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.SurvivalBounds
public import Probability.Kernel.Survival

/-!
# Fixed open corridors and killed interval survival

An open corridor containing the origin is embedded into an integer interval
by rounding its two scaled endpoints outwards.  The integer-valued
Rademacher path then survives in the corresponding finite killed interval.
-/

open MeasureTheory Set
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

open Combinatorics.Branching.Walk
open ProbabilityTheory.RandomWalk

noncomputable section

/-- Integer distance from the origin to the rounded lower boundary of a
scaled corridor. -/
def corridorLeftCeil (lower : ℝ) (n : ℕ) : ℕ :=
  ⌈-lower * Real.sqrt n⌉₊

/-- Integer distance from the origin to the rounded upper boundary of a
scaled corridor. -/
def corridorRightCeil (upper : ℝ) (n : ℕ) : ℕ :=
  ⌈upper * Real.sqrt n⌉₊

/-- Number of interior sites in the rounded killed interval. -/
def corridorInteriorCount (lower upper : ℝ) (n : ℕ) : ℕ :=
  corridorLeftCeil lower n + corridorRightCeil upper n - 1

/-- The translated origin in the rounded killed interval. -/
def corridorStart (lower upper : ℝ) (n : ℕ)
    (hleft : 0 < corridorLeftCeil lower n)
    (hright : 0 < corridorRightCeil upper n) :
    Fin (corridorInteriorCount lower upper n) :=
  ⟨corridorLeftCeil lower n - 1, by
    dsimp [corridorInteriorCount]
    omega⟩

theorem corridorLeftCeil_pos {lower : ℝ} (hlower : lower < 0) {n : ℕ}
    (hn : 0 < n) : 0 < corridorLeftCeil lower n := by
  apply Nat.one_le_ceil_iff.mpr
  apply mul_pos
  · exact neg_pos.mpr hlower
  · exact Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)

theorem corridorRightCeil_pos {upper : ℝ} (hupper : 0 < upper) {n : ℕ}
    (hn : 0 < n) : 0 < corridorRightCeil upper n := by
  apply Nat.one_le_ceil_iff.mpr
  exact mul_pos hupper (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn))

/-- A normalized Rademacher polygonal path in an open corridor is a path
surviving in the finite interval obtained by rounding the scaled boundaries
outwards. -/
theorem normalizedRademacherPath_openCorridor_implies_survival
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    {n : ℕ} (hn : 0 < n) (branch : ℕ → Bool)
    (hpath : normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n
      (rademacherIncrementPath branch) ∈
        ContinuousMap.rangeInOpenInterval lower upper) :
    rademacherStaysInInterval (corridorInteriorCount lower upper n) n
      (intervalSite (corridorStart lower upper n
        (corridorLeftCeil_pos hlower hn)
        (corridorRightCeil_pos hupper hn))) branch := by
  let L := corridorLeftCeil lower n
  let U := corridorRightCeil upper n
  let D := corridorInteriorCount lower upper n
  let start := corridorStart lower upper n
    (corridorLeftCeil_pos hlower hn) (corridorRightCeil_pos hupper hn)
  have hLpos : 0 < L := corridorLeftCeil_pos hlower hn
  have hUpos : 0 < U := corridorRightCeil_pos hupper hn
  have hLceil : -lower * Real.sqrt n ≤ (L : ℝ) := by
    exact_mod_cast (Nat.le_ceil (-lower * Real.sqrt n))
  have hUceil : upper * Real.sqrt n ≤ (U : ℝ) := by
    exact_mod_cast (Nat.le_ceil (upper * Real.sqrt n))
  have hLsite : intervalSite start = (L : ℝ) := by
    change ((L - 1 : ℕ) : ℝ) + 1 = (L : ℝ)
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    push_cast
    ring
  have hD : D = L + U - 1 := by
    simp [D, corridorInteriorCount, L, U]
  have hinitial : (L : ℝ) ∈ Set.Icc (1 : ℝ) D := by
    constructor
    · have : 1 ≤ L := hLpos
      exact_mod_cast this
    · rw [hD]
      have hU : 1 ≤ U := hUpos
      have hnat : L ≤ L + U - 1 := by omega
      exact_mod_cast hnat
  have hgrid :=
    (normalizedLinearContinuousPathIcc_mem_rangeInOpenInterval_iff
      (fun m => Real.sqrt m) hn hlower hupper
      (rademacherIncrementPath branch)).mp hpath
  have hstay : StaysIn (Set.Icc (1 : ℝ) D) n (L : ℝ)
      (rademacherIncrementPath branch) := by
    intro k
    let m := k.val + 1
    have hk := hgrid k
    change lower < normalizedStepPath (fun q => Real.sqrt q) n
        (rademacherIncrementPath branch) ((m : ℝ) / (n : ℝ)) ∧
      normalizedStepPath (fun q => Real.sqrt q) n
        (rademacherIncrementPath branch) ((m : ℝ) / (n : ℝ)) < upper at hk
    rw [normalizedStepPath_grid (fun q => Real.sqrt q) hn
      (rademacherIncrementPath branch)] at hk
    change lower < (Real.sqrt n)⁻¹ * rademacherPartialSum m branch ∧
      (Real.sqrt n)⁻¹ * rademacherPartialSum m branch < upper at hk
    let z : ℤ := ∑ i ∈ Finset.range m, rademacherIntIncrement (branch i)
    have hz : rademacherPartialSum m branch = (z : ℝ) := by
      simp [z, rademacherPartialSum_eq_intCast]
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
    have hscaledLower : lower * Real.sqrt n < (z : ℝ) := by
      rw [← hz]
      calc
        lower * Real.sqrt n <
            ((Real.sqrt n)⁻¹ * rademacherPartialSum m branch) * Real.sqrt n :=
          mul_lt_mul_of_pos_right hk.1 hsqrt
        _ = rademacherPartialSum m branch := by
          field_simp
    have hscaledUpper : (z : ℝ) < upper * Real.sqrt n := by
      rw [← hz]
      calc
        rademacherPartialSum m branch =
            ((Real.sqrt n)⁻¹ * rademacherPartialSum m branch) * Real.sqrt n := by
          field_simp
        _ < upper * Real.sqrt n := mul_lt_mul_of_pos_right hk.2 hsqrt
    have htranslatedLowerReal : 0 < (L : ℝ) + (z : ℝ) := by
      nlinarith
    have htranslatedUpperReal : (L : ℝ) + (z : ℝ) <
        (L : ℝ) + (U : ℝ) := by
      nlinarith
    have htranslatedLower : 0 < (L : ℤ) + z := by
      exact_mod_cast htranslatedLowerReal
    have htranslatedUpper : (L : ℤ) + z < (L + U : ℤ) := by
      exact_mod_cast htranslatedUpperReal
    have htranslatedNat :
        1 ≤ (L : ℤ) + z ∧ (L : ℤ) + z ≤ (D : ℤ) := by
      rw [hD]
      omega
    have hsum : (L : ℝ) + rademacherPartialSum m branch =
        ((L : ℤ) + z : ℤ) := by
      rw [hz]
      norm_cast
    change (L : ℝ) + rademacherPartialSum m branch ∈ Set.Icc (1 : ℝ) D
    rw [hsum]
    constructor
    · exact_mod_cast htranslatedNat.1
    · exact_mod_cast htranslatedNat.2
  have hclosed :=
    (staysIn_Icc_iff_inClosedInterval 1 D n (L : ℝ) hinitial
      (rademacherIncrementPath branch)).mp hstay
  rw [← hLsite] at hclosed
  exact (rademacherStaysInInterval_iff_inClosedInterval n start branch).mpr hclosed

/-- Probability that the normalized Rademacher polygonal path remains in a
fixed open corridor is bounded by survival of the corresponding killed
finite-state walk. -/
theorem normalizedRademacherPath_openCorridor_probability_le_survival
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    {n : ℕ} (hn : 0 < n) :
    normalizedLinearPathLaw rademacherMeasure (fun n => Real.sqrt n) n
      (ContinuousMap.rangeInOpenInterval lower upper) ≤
    Kernel.remainingMass (intervalRademacherKernel
      (corridorInteriorCount lower upper n)) n
      (corridorStart lower upper n
        (corridorLeftCeil_pos hlower hn)
        (corridorRightCeil_pos hupper hn)) := by
  let L := corridorLeftCeil lower n
  let U := corridorRightCeil upper n
  let D := corridorInteriorCount lower upper n
  let start := corridorStart lower upper n
    (corridorLeftCeil_pos hlower hn) (corridorRightCeil_pos hupper hn)
  have hmap : normalizedLinearPathLaw rademacherMeasure
      (fun n => Real.sqrt n) n =
      (iidSequenceLaw fairBoolMeasure).map
        (fun branch => normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n
          (rademacherIncrementPath branch)) := by
    rw [normalizedLinearPathLaw, ← map_iidSequenceLaw_rademacherIncrementPath,
      Measure.map_map]
    · rfl
    · exact measurable_normalizedLinearContinuousPathIcc _ _
    · exact measurable_rademacherIncrementPath
  rw [hmap, Measure.map_apply]
  · calc
      iidSequenceLaw fairBoolMeasure
          ((fun branch => normalizedLinearContinuousPathIcc
            (fun n => Real.sqrt n) n (rademacherIncrementPath branch)) ⁻¹'
            ContinuousMap.rangeInOpenInterval lower upper) ≤
        iidSequenceLaw fairBoolMeasure
          {branch | rademacherStaysInInterval D n (intervalSite start) branch} := by
            apply measure_mono
            intro branch hbranch
            exact normalizedRademacherPath_openCorridor_implies_survival
              hlower hupper hn branch hbranch
      _ = Kernel.remainingMass (intervalRademacherKernel D) n start := by
        symm
        rw [← intervalRademacherKernel_pow_apply_univ_eq_pathSurvival,
          ProbabilityTheory.Kernel.remainingMass]
  · exact (measurable_normalizedLinearContinuousPathIcc _ _).comp
      measurable_rademacherIncrementPath
  · exact ContinuousMap.measurableSet_rangeInOpenInterval (by linarith)

/-- The complete interval spectrum bounds killed survival by a geometric
series with a prefactor independent of the interval width. -/
theorem intervalRademacherKernel_remainingMass_le_geometric
    {interiorCount n : ℕ} (hcount : 0 < interiorCount) (hn : 0 < n)
    (start : Fin interiorCount) :
    Kernel.remainingMass (intervalRademacherKernel interiorCount) n start ≤
      ENNReal.ofReal (4 *
        (Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n /
          (1 - Real.cos
            (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n))) := by
  have hmass : Kernel.remainingMass (intervalRademacherKernel interiorCount)
      n start = ENNReal.ofReal
        (∑ finish, (intervalKernel interiorCount ^ n) start finish) := by
    unfold ProbabilityTheory.Kernel.remainingMass
    rw [intervalRademacherKernel_eq_ofRealMatrix,
      intervalKernel_pow_apply_univ]
  rw [hmass]
  apply ENNReal.ofReal_le_ofReal
  exact intervalKernel_pow_rowSum_le_four_mul_div_one_sub hcount hn start

/-- A fixed open corridor has the width-uniform complete-spectrum upper
bound after outward integer rounding of its endpoints. -/
theorem normalizedRademacherPath_openCorridor_probability_le_geometric
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    {n : ℕ} (hn : 0 < n) :
    normalizedLinearPathLaw rademacherMeasure (fun n => Real.sqrt n) n
      (ContinuousMap.rangeInOpenInterval lower upper) ≤
    ENNReal.ofReal (4 *
      (Real.cos (Real.pi /
          ((corridorInteriorCount lower upper n + 1 : ℕ) : ℝ)) ^ n /
        (1 - Real.cos (Real.pi /
          ((corridorInteriorCount lower upper n + 1 : ℕ) : ℝ)) ^ n))) := by
  calc
    normalizedLinearPathLaw rademacherMeasure (fun n => Real.sqrt n) n
        (ContinuousMap.rangeInOpenInterval lower upper) ≤
      Kernel.remainingMass (intervalRademacherKernel
        (corridorInteriorCount lower upper n)) n
        (corridorStart lower upper n
          (corridorLeftCeil_pos hlower hn)
          (corridorRightCeil_pos hupper hn)) :=
      normalizedRademacherPath_openCorridor_probability_le_survival
        hlower hupper hn
    _ ≤ _ := intervalRademacherKernel_remainingMass_le_geometric
      (by
        dsimp [corridorInteriorCount]
        have hL := corridorLeftCeil_pos hlower hn
        have hU := corridorRightCeil_pos hupper hn
        omega)
      hn _

/-- Replace the rounded lattice width by a deterministic upper width
`(upper - lower) * sqrt n + 3`.  The fixed additive slack absorbs both
outward roundings and has no effect on the diffusive limit. -/
theorem normalizedRademacherPath_openCorridor_probability_le_widthGeometric
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    {n : ℕ} (hn : 0 < n) :
    normalizedLinearPathLaw rademacherMeasure (fun n => Real.sqrt n) n
      (ContinuousMap.rangeInOpenInterval lower upper) ≤
    ENNReal.ofReal (4 *
      (Real.cos (Real.pi /
          ((upper - lower) * Real.sqrt n + 3)) ^ n /
        (1 - Real.cos (Real.pi /
          ((upper - lower) * Real.sqrt n + 3)) ^ n))) := by
  let L := corridorLeftCeil lower n
  let U := corridorRightCeil upper n
  let D := corridorInteriorCount lower upper n
  let W := upper - lower
  let A := W * Real.sqrt n + 3
  let q := Real.cos (Real.pi / ((D + 1 : ℕ) : ℝ))
  let q' := Real.cos (Real.pi / A)
  have hW : 0 < W := by dsimp [W]; linarith
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hLpos : 0 < L := corridorLeftCeil_pos hlower hn
  have hUpos : 0 < U := corridorRightCeil_pos hupper hn
  have hLupper : (L : ℝ) < -lower * Real.sqrt n + 1 := by
    exact Nat.ceil_lt_add_one
      (mul_nonneg (neg_nonneg.mpr hlower.le) hsqrt.le)
  have hUupper : (U : ℝ) < upper * Real.sqrt n + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg hupper.le hsqrt.le)
  have hdenNat : D + 1 = L + U := by
    dsimp [D, corridorInteriorCount, L, U]
    omega
  have hden : ((D + 1 : ℕ) : ℝ) = (L : ℝ) + (U : ℝ) := by
    rw [hdenNat]
    norm_cast
  have hMpos : 0 < (L : ℝ) + (U : ℝ) := by positivity
  have hMgeTwo : 2 ≤ (L : ℝ) + (U : ℝ) := by
    have hL : (1 : ℝ) ≤ L := by exact_mod_cast (Nat.succ_le_of_lt hLpos)
    have hU : (1 : ℝ) ≤ U := by exact_mod_cast (Nat.succ_le_of_lt hUpos)
    linarith
  have hMleA : (L : ℝ) + (U : ℝ) ≤ A := by
    dsimp [A, W]
    nlinarith
  have hApos : 0 < A := by dsimp [A]; positivity
  have hAgeTwo : 2 ≤ A := by dsimp [A]; linarith
  have hangleMpos : 0 < Real.pi / ((L : ℝ) + (U : ℝ)) :=
    div_pos Real.pi_pos hMpos
  have hangleAle : Real.pi / A ≤ Real.pi / ((L : ℝ) + (U : ℝ)) := by
    rw [div_le_div_iff₀ hApos hMpos]
    nlinarith [Real.pi_pos]
  have hangleMle : Real.pi / ((L : ℝ) + (U : ℝ)) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hMpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos, hMgeTwo]
  have hangleAleHalf : Real.pi / A ≤ Real.pi / 2 :=
    hangleAle.trans hangleMle
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    rw [hden]
    exact Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hangleMle⟩
  have hqLtOne : q < 1 := by
    dsimp [q]
    exact intervalEigenvalue_lt_one (by
      dsimp [D, corridorInteriorCount]
      omega)
  have hq'Nonneg : 0 ≤ q' := by
    dsimp [q']
    exact Real.cos_nonneg_of_mem_Icc
      ⟨by
        have hangleApos : 0 < Real.pi / A := div_pos Real.pi_pos hApos
        linarith [Real.pi_pos], hangleAleHalf⟩
  have hq'LtOne : q' < 1 := by
    dsimp [q']
    have hangleApos : 0 < Real.pi / A := div_pos Real.pi_pos hApos
    have hangleAlePi : Real.pi / A ≤ Real.pi := by
      rw [div_le_iff₀ hApos]
      nlinarith [Real.pi_pos, hAgeTwo]
    have hanti := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith [Real.pi_pos])
      (show Real.pi / A ∈ Set.Icc 0 Real.pi by
        exact ⟨hangleApos.le, hangleAlePi⟩)
      hangleApos
    simpa using hanti
  have hangleOrder : Real.pi / A ≤ Real.pi / ((D + 1 : ℕ) : ℝ) := by
    simpa [hden] using hangleAle
  have hangleDle : Real.pi / ((D + 1 : ℕ) : ℝ) ≤ Real.pi / 2 := by
    simpa [hden] using hangleMle
  have hhalfPiLePi : Real.pi / 2 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hqLe : q ≤ q' := by
    dsimp [q, q']
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (div_nonneg Real.pi_pos.le hApos.le)
      (hangleDle.trans hhalfPiLePi)
      hangleOrder
  have hqPow : q ^ n ≤ q' ^ n :=
    pow_le_pow_left₀ hqNonneg hqLe n
  have hqPowLt : q ^ n < 1 := pow_lt_one₀ hqNonneg hqLtOne hn.ne'
  have hq'PowLt : q' ^ n < 1 := pow_lt_one₀ hq'Nonneg hq'LtOne hn.ne'
  have hfrac : q ^ n / (1 - q ^ n) ≤ q' ^ n / (1 - q' ^ n) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hqPowLt) (sub_pos.mpr hq'PowLt)]
    nlinarith
  have hbase := normalizedRademacherPath_openCorridor_probability_le_geometric
    hlower hupper hn
  calc
    normalizedLinearPathLaw rademacherMeasure (fun n => Real.sqrt n) n
        (ContinuousMap.rangeInOpenInterval lower upper) ≤
      ENNReal.ofReal (4 * (q ^ n / (1 - q ^ n))) := by
        simpa [q, D] using hbase
    _ ≤ ENNReal.ofReal (4 * (q' ^ n / (1 - q' ^ n))) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hfrac (by norm_num)
    _ = _ := by simp [q', A, W]

end

end ProbabilityTheory.RandomWalk.Mogulskii

end
