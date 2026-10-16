/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Spine
/-!
# Second-stage scales for the spine corridor

This file specializes the finite-variance entrance and bridge estimate to the
`D^(1/3)` width and `D^(-2/3)` drift used in the second stage of the positive-a
argument.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The slope of the second-stage affine tube. -/
noncomputable def rightTailPositiveASecondStageSlope
    (κ c : ℝ) (D : ℕ) : ℝ :=
  κ / c ^ 2 * ((D : ℝ) ^ ((-2 : ℝ) / 3))

/-- The width of the second-stage affine tube. -/
noncomputable def rightTailPositiveASecondStageWidth
    (c : ℝ) (D : ℕ) : ℝ :=
  c * ((D : ℝ) ^ ((1 : ℝ) / 3))

/-- The entrance scale used to join a finite-variance entrance block to the
downward bridge in the second-stage tube. -/
noncomputable def rightTailPositiveASecondStageEntranceScale
    (κ c v : ℝ) (D : ℕ) : ℝ :=
  ((5 * (κ / c ^ 2) + v) / 2) * ((D : ℝ) ^ ((1 : ℝ) / 3))

/-- The stable endpoint-bridge scale used by the second-stage corridor
estimate. -/
noncomputable def rightTailPositiveASecondStageBridgeScale
    (κ c v : ℝ) (k : ℕ) : ℝ :=
  ((v - κ / c ^ 2) / 24) * ((k : ℝ) ^ ((1 : ℝ) / 3))

/-- The explicit lower mass furnished by the finite-variance entrance and
bridge estimates at a second-stage horizon of length `D`. -/
noncomputable def rightTailPositiveASecondStageSpineLowerBound
    (ν : Measure ℝ) (κ c v : ℝ) (entryQ : ℝ≥0∞) (C : ℝ)
    (bridgeQ : ℝ≥0∞) (amplitude : ℝ) (D : ℕ) : ℝ≥0∞ := by
  let lambda : ℝ := κ / c ^ 2
  let α : ℝ := (5 * lambda + v) / 2
  let β : ℝ := (v - lambda) / 24
  let scale : ℕ → ℝ := fun k => β * ((k : ℝ) ^ ((1 : ℝ) / 3))
  let entranceScale : ℝ := α * ((D : ℝ) ^ ((1 : ℝ) / 3))
  let bridgeLength : ℕ := D - ⌊entranceScale ^ 2⌋₊
  exact
    entryQ / (⌊entranceScale ^ 2⌋₊ : ℝ≥0∞) *
      (ENNReal.ofReal (Real.exp
        ((C / ((2 / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
          (Asymptotics.balancedBlockCount
            (finiteVarianceBridgeLength scale bridgeLength -
              stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale bridgeLength)
            (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale bridgeLength) + 1)) *
        (bridgeQ / (finiteVarianceEntranceLength scale bridgeLength : ℝ≥0∞))

private theorem rightTailPositiveASecondStageBridgeScale_isMogulskiiScale
    {κ c v : ℝ} (hLambdaV : κ / c ^ 2 < v) :
    IsMogulskiiScale (rightTailPositiveASecondStageBridgeScale κ c v) := by
  let β : ℝ := (v - κ / c ^ 2) / 24
  have hβ : 0 < β := by dsimp [β]; linarith
  have hroot : Tendsto (fun k : ℕ => (k : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)).comp
      tendsto_natCast_atTop_atTop
  have hscale : Tendsto (rightTailPositiveASecondStageBridgeScale κ c v)
      atTop atTop := by
    change Tendsto
      (fun k : ℕ => ((v - κ / c ^ 2) / 24) *
        ((k : ℝ) ^ ((1 : ℝ) / 3))) atTop atTop
    simpa [β] using hroot.const_mul_atTop hβ
  have hneg : Tendsto (fun k : ℕ => (k : ℝ) ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun x : ℝ => x ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
      simpa using (_root_.tendsto_rpow_neg_atTop
        (by norm_num : (0 : ℝ) < (1 : ℝ) / 6))
    have h := hbase.comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hratio : Tendsto
      (fun k : ℕ => rightTailPositiveASecondStageBridgeScale κ c v k /
        Real.sqrt (k : ℝ)) atTop (𝓝 0) := by
    have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℕ => β) atTop (𝓝 β)).mul hneg
    have heq :
        (fun k : ℕ => rightTailPositiveASecondStageBridgeScale κ c v k /
          Real.sqrt (k : ℝ)) =ᶠ[atTop]
        fun k => β * ((k : ℝ) ^ (-(1 / 6 : ℝ))) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
      have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
      dsimp [rightTailPositiveASecondStageBridgeScale, β]
      have hrootInv : ((k : ℝ) ^ ((1 : ℝ) / 2))⁻¹ =
          (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_neg hkReal.le]
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, hrootInv]
      calc
        ((v - κ / c ^ 2) / 24 * (k : ℝ) ^ ((1 : ℝ) / 3)) *
            (k : ℝ) ^ (-(1 / 2 : ℝ)) =
          ((v - κ / c ^ 2) / 24) *
            ((k : ℝ) ^ ((1 : ℝ) / 3) * (k : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
        _ = ((v - κ / c ^ 2) / 24) *
            (k : ℝ) ^ (((1 : ℝ) / 3) + (-(1 / 2 : ℝ))) := by
          rw [← Real.rpow_add hkReal]
        _ = ((v - κ / c ^ 2) / 24) * (k : ℝ) ^ (-(1 / 6 : ℝ)) := by
          congr 1
          congr 1
          ring
    simpa using hmul.congr' heq.symm
  rw [isMogulskiiScale_iff]
  exact ⟨hscale, hratio⟩

private theorem rightTailPositiveA_rpow_third_sq {x : ℝ} (hx : 0 < x) :
    (x ^ ((1 : ℝ) / 3)) ^ 2 = x ^ ((2 : ℝ) / 3) := by
  calc
    (x ^ ((1 : ℝ) / 3)) ^ 2 =
        (x ^ ((1 : ℝ) / 3)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = x ^ (((1 : ℝ) / 3) * 2) := by rw [← Real.rpow_mul hx.le]
    _ = x ^ ((2 : ℝ) / 3) := by congr 1; norm_num

private theorem rightTailPositiveA_rpow_third_cube {x : ℝ} (hx : 0 < x) :
    (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  calc
    (x ^ ((1 : ℝ) / 3)) ^ 3 =
        (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
    _ = x ^ (((1 : ℝ) / 3) * 3) := by rw [← Real.rpow_mul hx.le]
    _ = x := by norm_num [Real.rpow_one]

/-- The scaled entrance block is asymptotically shorter than the full
second-stage horizon, leaving a diverging bridge interval. -/
private theorem tendsto_secondStageRemainingLength_atTop
    {D : ℕ → ℕ} (hD : Tendsto (fun n => (D n : ℝ)) atTop atTop)
    {α : ℝ} :
    Tendsto (fun n =>
      ((D n - ⌊(α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2⌋₊ : ℕ) : ℝ))
      atTop atTop := by
  let root : ℕ → ℝ := fun n => (D n : ℝ) ^ ((1 : ℝ) / 3)
  have hroot : Tendsto root atTop atTop := by
    exact (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)).comp hD
  have hrootBound : ∀ᶠ n : ℕ in atTop, 2 * α ^ 2 ≤ root n :=
    hroot.eventually_ge_atTop (2 * α ^ 2)
  have hDpos : ∀ᶠ n : ℕ in atTop, 0 < (D n : ℝ) :=
    hD.eventually_gt_atTop 0
  have hhalf : Tendsto (fun n => (D n : ℝ) / 2) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      hD.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  apply tendsto_atTop_mono' atTop ?_ hhalf
  filter_upwards [hrootBound, hDpos] with n hnroot hnDpos
  have hrootSquare : root n ^ 2 = (D n : ℝ) ^ ((2 : ℝ) / 3) := by
    dsimp [root]
    have h := rightTailPositiveA_rpow_third_sq hnDpos
    simpa using h
  have hrootCube : root n ^ 3 = (D n : ℝ) := by
    dsimp [root]
    have h := rightTailPositiveA_rpow_third_cube hnDpos
    simpa using h
  have hE2 : (α * root n) ^ 2 ≤ (D n : ℝ) / 2 := by
    rw [mul_pow, ← hrootCube]
    have hmul := mul_le_mul_of_nonneg_right hnroot (sq_nonneg (root n))
    nlinarith [hmul]
  have hfloor :
      (⌊(α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2⌋₊ : ℝ) ≤
        (D n : ℝ) / 2 := by
    calc
      (⌊(α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2⌋₊ : ℝ) ≤
          (α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2 :=
        Nat.floor_le (sq_nonneg _)
      _ = (α * root n) ^ 2 := by rfl
      _ ≤ (D n : ℝ) / 2 := hE2
  have hfloorNat :
      ⌊(α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2⌋₊ ≤ D n := by
    have hreal :
        (⌊(α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2⌋₊ : ℝ) ≤ (D n : ℝ) := by
      linarith
    exact_mod_cast hreal
  have hremain :
      (D n : ℝ) / 2 ≤
        ((D n - ⌊(α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2⌋₊ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hfloorNat]
    linarith [hfloor]
  exact hremain

/-- A finite-second-moment increment law gives an eventual quantitative
lower bound for the tilted random-walk event in the second-stage
affine tube. The only distributional assumption is the centered
finite second moment; the scale inequalities are consequences of the stated
parameter constraints. -/
theorem eventually_iidSequenceLaw_rightTailPositiveASecondStageAffineCorridor_lowerBound_of_centeredSecondMoment
    {D : ℕ → ℕ} (hD : Tendsto (fun n => (D n : ℝ)) atTop atTop)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma κ c v : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hv : 0 < v)
    (hκv : κ / c ^ 2 < v)
    (hterminal : κ / c ^ 2 ≤ 2 * v / 5)
    (hentranceWidth : (5 * (κ / c ^ 2) + v) / 2 ≤ c) :
    ∃ entryQ : ℝ≥0∞, 0 < entryQ ∧
      ∃ C : ℝ, C < 0 ∧ ∃ bridgeQ : ℝ≥0∞, 0 < bridgeQ ∧
        ∃ amplitude : ℝ, 0 < amplitude ∧
          ∀ᶠ n : ℕ in atTop,
            rightTailPositiveASecondStageSpineLowerBound
                ν κ c v entryQ C bridgeQ amplitude (D n) ≤
              iidSequenceLaw ν
                {increment : ℕ → ℝ |
                  RandomWalk.history (D n) 0 increment ∈
                    affineCorridorThrough (D n) 0
                      (rightTailPositiveASecondStageSlope κ c (D n))
                      (rightTailPositiveASecondStageWidth c (D n))
                      (rightTailPositiveASecondStageSlope κ c (D n) * (D n : ℝ) +
                        v * ((D n : ℝ) ^ ((1 : ℝ) / 3)))} := by
  let lambda : ℝ := κ / c ^ 2
  let α : ℝ := (5 * lambda + v) / 2
  let β : ℝ := (v - lambda) / 24
  let entranceScale : ℕ → ℝ := fun n => α * ((D n : ℝ) ^ ((1 : ℝ) / 3))
  let drift : ℕ → ℝ := fun n => (lambda * α ^ 2) / (entranceScale n) ^ 2
  let width : ℕ → ℝ := fun n => c * ((D n : ℝ) ^ ((1 : ℝ) / 3))
  let terminalExtra : ℕ → ℝ := fun n => v * ((D n : ℝ) ^ ((1 : ℝ) / 3))
  let bridgeScale : ℕ → ℝ := rightTailPositiveASecondStageBridgeScale κ c v
  have hLambda_nonneg : 0 ≤ lambda := by dsimp [lambda]; positivity
  have hLambdaV : lambda < v := by dsimp [lambda]; linarith
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β]; linarith
  have hbridgeScale : IsMogulskiiScale bridgeScale :=
    rightTailPositiveASecondStageBridgeScale_isMogulskiiScale hLambdaV
  have hroot : Tendsto (fun n => (D n : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)).comp hD
  have hentranceScale : Tendsto entranceScale atTop atTop := by
    simpa [entranceScale, α] using hroot.const_mul_atTop hα
  have hbridgeLength : Tendsto
      (fun n => ((D n - ⌊entranceScale n ^ 2⌋₊ : ℕ) : ℝ)) atTop atTop := by
    have h := tendsto_secondStageRemainingLength_atTop (α := α) hD
    simpa [entranceScale, α] using h
  have hprefixLe : ∀ᶠ n : ℕ in atTop,
      ⌊entranceScale n ^ 2⌋₊ ≤ D n := by
    have hremaining := hbridgeLength.eventually_gt_atTop 0
    filter_upwards [hremaining] with n hn
    have hremainingNat : 0 < D n - ⌊entranceScale n ^ 2⌋₊ := by
      exact_mod_cast hn
    omega
  have hαc : α ≤ c := by
    dsimp [α, lambda]
    exact hentranceWidth
  have hαthird : 2 * α / 3 ≤ c := by
    have hαnonneg : 0 ≤ α := le_of_lt hα
    nlinarith
  have hαthirdv : 2 * α / 3 ≤ v := by
    dsimp [α]
    nlinarith [hterminal]
  have hlowCoeff : lambda ≤ α / 3 - 2 * β := by
    dsimp [α, β]
    nlinarith [hLambdaV]
  let entryDrift : ℝ := lambda * α ^ 2
  have hentryDrift : 0 ≤ entryDrift := by
    dsimp [entryDrift]
    positivity
  have hdrift : ∀ n, drift n = entryDrift / (entranceScale n) ^ 2 := by
    intro n
    rfl
  have hentranceWidth' : ∀ᶠ n : ℕ in atTop,
      entranceScale n ≤ width n := by
    filter_upwards [] with n
    dsimp [entranceScale, width]
    have hrootNonneg : 0 ≤ (D n : ℝ) ^ ((1 : ℝ) / 3) := by
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  have hbridgeUpper : ∀ᶠ n : ℕ in atTop,
      2 * entranceScale n / 3 ≤ width n := by
    filter_upwards [] with n
    dsimp [entranceScale, width]
    have hrootNonneg : 0 ≤ (D n : ℝ) ^ ((1 : ℝ) / 3) := by
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith
  have hbridgeLower : ∀ᶠ n : ℕ in atTop,
      entranceScale n / 3 - 2 * bridgeScale
          (D n - ⌊entranceScale n ^ 2⌋₊) ≥
        drift n * ((D n - ⌊entranceScale n ^ 2⌋₊ : ℕ) : ℝ) := by
    filter_upwards [hprefixLe, hD.eventually_gt_atTop 0] with n hprefix hnD
    let root : ℝ := (D n : ℝ) ^ ((1 : ℝ) / 3)
    let bridgeLength : ℕ := D n - ⌊entranceScale n ^ 2⌋₊
    have hnDReal : 0 < (D n : ℝ) := hnD
    have hrootPos : 0 < root := by
      dsimp [root]
      exact Real.rpow_pos_of_pos hnDReal _
    have hlengthLe : bridgeLength ≤ D n := by
      dsimp [bridgeLength]
      exact Nat.sub_le _ _
    have hlengthRealLe : (bridgeLength : ℝ) ≤ (D n : ℝ) := by
      exact_mod_cast hlengthLe
    have hbridgeScaleUpper : bridgeScale bridgeLength ≤ β * root := by
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg bridgeLength)
        hlengthRealLe (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      calc
        bridgeScale bridgeLength = β *
            ((bridgeLength : ℝ) ^ ((1 : ℝ) / 3)) := by
          simp [bridgeScale, rightTailPositiveASecondStageBridgeScale, β, lambda]
        _ ≤ β * root := by
          apply mul_le_mul_of_nonneg_left hpow
          exact le_of_lt hβ
    have hpower : ((D n : ℝ) ^ ((-2 : ℝ) / 3)) * (D n : ℝ) = root := by
      calc
        ((D n : ℝ) ^ ((-2 : ℝ) / 3)) * (D n : ℝ) =
            ((D n : ℝ) ^ ((-2 : ℝ) / 3)) *
              ((D n : ℝ) ^ (1 : ℝ)) := by rw [Real.rpow_one]
        _ = (D n : ℝ) ^ (((-2 : ℝ) / 3) + 1) :=
          (Real.rpow_add hnDReal _ _).symm
        _ = root := by
          dsimp [root]
          congr 1
          ring
    have hdriftFormula : drift n = lambda * ((D n : ℝ) ^ ((-2 : ℝ) / 3)) := by
      dsimp [drift, entranceScale]
      have hscaleSq :
          (α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2 =
            α ^ 2 * ((D n : ℝ) ^ ((2 : ℝ) / 3)) := by
        rw [mul_pow, rightTailPositiveA_rpow_third_sq hnDReal]
      rw [hscaleSq]
      have hexponent : (-2 : ℝ) / 3 = -((2 : ℝ) / 3) := by ring
      rw [hexponent, Real.rpow_neg hnDReal.le]
      have hαsq : α ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hα)
      have hDpow : (D n : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hnDReal _)
      field_simp [hαsq, hDpow]
    have hdriftLength : drift n * (bridgeLength : ℝ) ≤ lambda * root := by
      rw [hdriftFormula]
      calc
        (lambda * ((D n : ℝ) ^ ((-2 : ℝ) / 3))) * (bridgeLength : ℝ) ≤
            (lambda * ((D n : ℝ) ^ ((-2 : ℝ) / 3))) * (D n : ℝ) :=
          mul_le_mul_of_nonneg_left hlengthRealLe (by positivity)
        _ = lambda * root := by rw [mul_assoc, hpower]
    have hleft :
        entranceScale n / 3 - 2 * bridgeScale bridgeLength ≥
          (α / 3 - 2 * β) * root := by
      dsimp [entranceScale, root]
      nlinarith [hbridgeScaleUpper]
    have hright : (α / 3 - 2 * β) * root ≥ lambda * root :=
      mul_le_mul_of_nonneg_right hlowCoeff hrootPos.le
    have hcombined : drift n * (bridgeLength : ℝ) ≤
        entranceScale n / 3 - 2 * bridgeScale bridgeLength :=
      hdriftLength.trans (hright.trans hleft)
    simpa [bridgeLength] using hcombined
  have hterminal : ∀ᶠ n : ℕ in atTop,
      2 * entranceScale n / 3 - bridgeScale
          (D n - ⌊entranceScale n ^ 2⌋₊) ≤
        drift n * ((D n - ⌊entranceScale n ^ 2⌋₊ : ℕ) : ℝ) +
          terminalExtra n := by
    filter_upwards [hprefixLe, hD.eventually_gt_atTop 0] with n hprefix hnD
    let root : ℝ := (D n : ℝ) ^ ((1 : ℝ) / 3)
    have hrootNonneg : 0 ≤ root := by
      dsimp [root]
      exact Real.rpow_nonneg (by positivity) _
    have hbridgeNonneg : 0 ≤ bridgeScale
        (D n - ⌊entranceScale n ^ 2⌋₊) := by
      dsimp [bridgeScale, rightTailPositiveASecondStageBridgeScale]
      positivity
    have hdriftFormula : drift n = lambda * ((D n : ℝ) ^ ((-2 : ℝ) / 3)) := by
      dsimp [drift, entranceScale]
      have hnDReal : 0 < (D n : ℝ) := hnD
      have hscaleSq :
          (α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2 =
            α ^ 2 * ((D n : ℝ) ^ ((2 : ℝ) / 3)) := by
        rw [mul_pow, rightTailPositiveA_rpow_third_sq hnDReal]
      rw [hscaleSq]
      have hexponent : (-2 : ℝ) / 3 = -((2 : ℝ) / 3) := by ring
      rw [hexponent, Real.rpow_neg hnDReal.le]
      have hαsq : α ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hα)
      have hDpow : (D n : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hnDReal _)
      field_simp [hαsq, hDpow]
    have hdriftNonneg : 0 ≤ drift n := by
      rw [hdriftFormula]
      positivity
    dsimp [entranceScale, terminalExtra, root]
    have hterminalScaled :
        2 * α / 3 * ((D n : ℝ) ^ ((1 : ℝ) / 3)) ≤
          v * ((D n : ℝ) ^ ((1 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_right hαthirdv hrootNonneg
    nlinarith [hterminalScaled, hbridgeNonneg, hdriftNonneg]
  have hentryDriftNonneg : 0 ≤ entryDrift := hentryDrift
  obtain ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude, hamplitude,
      hcorridor⟩ :=
    eventually_iidSequenceLaw_affineCorridorThrough_lowerBound_of_centeredSecondMoment
      (ν := ν) hν hsigma D entranceScale drift width terminalExtra bridgeScale
      entryDrift hentryDriftNonneg hentranceScale hbridgeScale hbridgeLength
      hdrift hprefixLe hentranceWidth' hbridgeLower hbridgeUpper hterminal
  refine ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude, hamplitude, ?_⟩
  filter_upwards [hcorridor, hD.eventually_gt_atTop 0] with n hbound hDpos
  have hmatchingDrift : drift n =
      rightTailPositiveASecondStageSlope κ c (D n) := by
    have hnD : 0 < (D n : ℝ) := hDpos
    have hlocal : drift n = lambda * ((D n : ℝ) ^ ((-2 : ℝ) / 3)) := by
      dsimp [drift, entranceScale]
      have hscaleSq :
          (α * ((D n : ℝ) ^ ((1 : ℝ) / 3))) ^ 2 =
            α ^ 2 * ((D n : ℝ) ^ ((2 : ℝ) / 3)) := by
        rw [mul_pow, rightTailPositiveA_rpow_third_sq hnD]
      rw [hscaleSq]
      have hexponent : (-2 : ℝ) / 3 = -((2 : ℝ) / 3) := by ring
      rw [hexponent, Real.rpow_neg hnD.le]
      have hαsq : α ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hα)
      have hDpow : (D n : ℝ) ^ ((2 : ℝ) / 3) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hnD _)
      field_simp [hαsq, hDpow]
    simpa [rightTailPositiveASecondStageSlope, lambda] using hlocal
  have hmatchingWidth : width n = rightTailPositiveASecondStageWidth c (D n) := by
    rfl
  have hmass :
      rightTailPositiveASecondStageSpineLowerBound
          ν κ c v entryQ C bridgeQ amplitude (D n) =
        entryQ / (⌊entranceScale n ^ 2⌋₊ : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp
            ((C / ((2 / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
              (Asymptotics.balancedBlockCount
                (finiteVarianceBridgeLength bridgeScale
                    (D n - ⌊entranceScale n ^ 2⌋₊) -
                  stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale
                    (D n - ⌊entranceScale n ^ 2⌋₊))
                (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale
                  (D n - ⌊entranceScale n ^ 2⌋₊)) + 1)) *
          (bridgeQ / ((finiteVarianceEntranceLength bridgeScale
            (D n - ⌊entranceScale n ^ 2⌋₊) : ℕ) : ℝ≥0∞)) := by
    rfl
  rw [hmatchingDrift, hmatchingWidth] at hbound
  rw [hmass]
  simpa [terminalExtra, bridgeScale,
    rightTailPositiveASecondStageBridgeScale] using hbound

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
