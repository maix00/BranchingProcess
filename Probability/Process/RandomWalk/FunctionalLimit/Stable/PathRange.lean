/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.BlockTail
public import Probability.Process.RandomWalk.Path.Skorokhod.Range
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Compact range bounds for stable random walks

This file is the stable-domain adapter from regular variation and truncation
centering to compact-range control of the normalized path laws. The topology
and compactness of state-space ranges are supplied by the general càdlàg and
Skorokhod layers; only the random-walk scale and its stable asymptotics appear
here.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- Over a whole `n`-step horizon, a normalized partial-sum excursion bounds
the probability that the càdlàg path leaves the symmetric compact interval.
The tail and truncated-moment constants may be chosen with any positive
slack above their regular-variation limits. -/
theorem eventually_measure_normalizedStepPathLaw_rangeExit_le_of_stableNorming
    {α radiusMultiplier thresholdMultiplier tailBound momentBound : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (htailBound : ((2 - α) / α) * radiusMultiplier ^ (-α) < tailBound)
    (hmomentBound : radiusMultiplier ^ (2 - α) < momentBound)
    (hbias : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2) :
    ∀ᶠ n : ℕ in atTop,
      (normalizedStepPathLaw ν normalization n)
        (CadlagPath.rangeIn (T := unitInterval)
          (Set.Icc (-thresholdMultiplier) thresholdMultiplier))ᶜ ≤
        ENNReal.ofReal
          (tailBound + 4 * momentBound / thresholdMultiplier ^ 2) := by
  let length : ℕ → ℕ := fun n => n
  have hlength : ∀ᶠ n in atTop, 0 < length n :=
    eventually_gt_atTop 0
  have hratio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [length, hn']
  have hblock := eventually_measure_blockPrefixExceedance_le_of_stableNorming
    (tailBound := tailBound) (momentBound := momentBound)
    hnorm hα₀ hα₂ htail hradius hthreshold (show 0 ≤ (1 : ℝ) by norm_num)
    length htailBound hmomentBound hlength hratio hbias
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [hblock, hscale] with n hblockN hscaleN
  have hblockN' : (iidSequenceLaw ν)
      (blockPrefixExceedance 0 n (thresholdMultiplier * normalization n)) ≤
        ENNReal.ofReal
          (tailBound + 4 * momentBound / thresholdMultiplier ^ 2) := by
    simpa [length] using hblockN
  simpa [one_mul] using
    ProbabilityTheory.RandomWalk.measure_normalizedStepPathLaw_rangeIn_closedInterval_compl_le_of_blockPrefixExceedance
      ν normalization n hthreshold hscaleN
      (ENNReal.ofReal (tailBound + 4 * momentBound / thresholdMultiplier ^ 2)) hblockN'

/-- Parameter choice for a stable whole-horizon range bound. First the
regular-variation tail is made small by increasing the truncation radius;
then the excursion threshold is chosen large enough both for the centering
bias and for the truncated-moment term. -/
theorem exists_stableRangeParameters
    {α ε : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) (hε : 0 < ε)
    (biasBound : ℝ → ℝ) :
    ∃ radiusMultiplier thresholdMultiplier : ℝ,
      0 < radiusMultiplier ∧ biasBound radiusMultiplier < thresholdMultiplier / 2 ∧
      0 < thresholdMultiplier ∧
        (((2 - α) / α) * radiusMultiplier ^ (-α) + ε / 4) +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2 < ε := by
  let tailCoefficient : ℝ := (2 - α) / α
  have htailCoefficient : 0 < tailCoefficient := by
    dsimp [tailCoefficient]
    positivity
  have htailTendsto : Tendsto (fun r : ℝ => tailCoefficient * r ^ (-α))
    atTop (nhds 0) := by
    have hpow := tendsto_rpow_neg_atTop hα₀
    simpa using tendsto_const_nhds.mul hpow
  have htailEventually : ∀ᶠ r : ℝ in atTop,
      tailCoefficient * r ^ (-α) < ε / 4 :=
    htailTendsto.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨lower, hlower⟩ := eventually_atTop.1 htailEventually
  let radiusMultiplier : ℝ := max lower 1 + 1
  have hradius : 0 < radiusMultiplier := by
    dsimp [radiusMultiplier]
    positivity
  have htailSmall : tailCoefficient * radiusMultiplier ^ (-α) < ε / 4 := by
    apply hlower radiusMultiplier
    dsimp [radiusMultiplier]
    calc
      lower ≤ max lower 1 := le_max_left _ _
      _ ≤ max lower 1 + 1 := by norm_num
  let momentBound : ℝ := radiusMultiplier ^ (2 - α) + 1
  have hmomentBound : 0 < momentBound := by
    dsimp [momentBound]
    positivity
  let thresholdLower : ℝ := max
    (2 * biasBound radiusMultiplier)
    (max 1 (8 * momentBound / ε))
  obtain ⟨m, hm⟩ := exists_nat_gt thresholdLower
  let thresholdMultiplier : ℝ := m
  have hthresholdLower : thresholdLower < thresholdMultiplier := by
    exact_mod_cast hm
  have hthresholdPositive : 0 < thresholdMultiplier := by
    have honeLower : 1 ≤ thresholdLower := by
      dsimp [thresholdLower]
      exact le_trans (le_max_left 1 (8 * momentBound / ε)) (le_max_right _ _)
    linarith
  have hbiasSmall : biasBound radiusMultiplier < thresholdMultiplier / 2 := by
    have hle : 2 * biasBound radiusMultiplier ≤ thresholdLower :=
      le_max_left _ _
    linarith
  have hlarge : 8 * momentBound / ε < thresholdMultiplier := by
    have hle : 8 * momentBound / ε ≤ thresholdLower := by
      dsimp [thresholdLower]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hle hthresholdLower
  have hlargeMul : 8 * momentBound < thresholdMultiplier * ε :=
    (div_lt_iff₀ hε).mp hlarge
  have honeLower : 1 ≤ thresholdLower := by
    dsimp [thresholdLower]
    exact le_trans (le_max_left 1 (8 * momentBound / ε)) (le_max_right _ _)
  have hone : 1 ≤ thresholdMultiplier := le_trans honeLower hthresholdLower.le
  have hthresholdSq : thresholdMultiplier ≤ thresholdMultiplier ^ 2 := by
    nlinarith [sq_nonneg (thresholdMultiplier - 1)]
  have hinv : (thresholdMultiplier ^ 2)⁻¹ ≤ thresholdMultiplier⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hthresholdPositive) hthresholdPositive).2
      hthresholdSq
  have hmomentFrac :
      4 * momentBound / thresholdMultiplier ^ 2 ≤
        4 * momentBound / thresholdMultiplier := by
    calc
      4 * momentBound / thresholdMultiplier ^ 2 =
          4 * momentBound * (thresholdMultiplier ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 4 * momentBound * thresholdMultiplier⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4 * momentBound / thresholdMultiplier := by rw [div_eq_mul_inv]
  have hmomentSmall :
      4 * momentBound / thresholdMultiplier < ε / 2 := by
    rw [div_lt_iff₀ hthresholdPositive]
    nlinarith [hlargeMul]
  refine ⟨radiusMultiplier, thresholdMultiplier, hradius, hbiasSmall,
    hthresholdPositive, ?_⟩
  dsimp [tailCoefficient] at htailSmall
  linarith

/-- Any of the stable-domain source centering conditions can be used after
providing its eventual truncation-bias limit bound. The arbitrary error
budget is converted into a compact symmetric state-space range. -/
theorem exists_eventually_compactRange_bound_of_stableNorming
    {α ε : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hε : 0 < ε) (biasBound : ℝ → ℝ)
    (hbias : ∀ radiusMultiplier thresholdMultiplier : ℝ,
      0 < radiusMultiplier →
      biasBound radiusMultiplier < thresholdMultiplier / 2 →
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) *
          |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
            normalization n ≤ thresholdMultiplier / 2) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ ENNReal.ofReal ε := by
  obtain ⟨radiusMultiplier, thresholdMultiplier, hradius, hbiasSmall,
      hthreshold, hbudget⟩ :=
    exists_stableRangeParameters hα₀ hα₂ hε biasBound
  let tailBound : ℝ :=
    ((2 - α) / α) * radiusMultiplier ^ (-α) + ε / 4
  let momentBound : ℝ := radiusMultiplier ^ (2 - α) + 1
  have htailBound :
      ((2 - α) / α) * radiusMultiplier ^ (-α) < tailBound := by
    dsimp [tailBound]
    linarith
  have hmomentBound : radiusMultiplier ^ (2 - α) < momentBound := by
    dsimp [momentBound]
    linarith
  have hrange := eventually_measure_normalizedStepPathLaw_rangeExit_le_of_stableNorming
    (tailBound := tailBound) (momentBound := momentBound)
    hnorm hα₀ hα₂ htail hradius hthreshold htailBound hmomentBound
      (hbias radiusMultiplier thresholdMultiplier hradius hbiasSmall)
  refine ⟨Set.Icc (-thresholdMultiplier) thresholdMultiplier,
    isCompact_Icc, ?_⟩
  have hbudget' :
      tailBound + 4 * momentBound / thresholdMultiplier ^ 2 < ε := by
    dsimp [tailBound, momentBound] at hbudget ⊢
    exact hbudget
  filter_upwards [hrange] with n hn
  exact hn.trans (ENNReal.ofReal_le_ofReal hbudget'.le)

/-- Compact-range control below stable index one, under the uncentered
source convention: only regular variation and the resulting truncation-bias
estimate are used; no first moment is assumed. -/
theorem exists_eventually_compactRange_bound_of_index_lt_one
    {α ε : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hε : 0 < ε) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ ENNReal.ofReal ε := by
  let biasBound : ℝ → ℝ := truncationBiasConstant α
  apply exists_eventually_compactRange_bound_of_stableNorming hnorm hα₀
    (by linarith) htail hε biasBound
  intro radiusMultiplier thresholdMultiplier hradius hbiasSmall
  have hratio : ∀ᶠ n : ℕ in atTop,
      ((n : ℕ) : ℝ) / n ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [hn']
  have hbias := eventually_truncatedIncrementBias_le_of_stableNorming_of_index_lt_one
    hnorm hα₀ hα₁ htail hradius (by norm_num : 0 < (1 : ℝ))
      (by simpa [biasBound] using hbiasSmall) hratio
  simpa [biasBound] using hbias

/-- Compact-range control at stable index one under the sine-centering
condition from Mogulskii's source theorem. -/
theorem exists_eventually_compactRange_bound_of_index_one
    {ε : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    (hε : 0 < ε) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ ENNReal.ofReal ε := by
  let biasBound : ℝ → ℝ := indexOneTruncationBiasConstant
  apply exists_eventually_compactRange_bound_of_stableNorming hnorm
    (by norm_num) (by norm_num) htail hε biasBound
  intro radiusMultiplier thresholdMultiplier hradius hbiasSmall
  have hratio : ∀ᶠ n : ℕ in atTop,
      ((n : ℕ) : ℝ) / n ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [hn']
  have hbias := eventually_truncatedIncrementBias_le_of_stableNorming_of_index_one
    hnorm htail hradius hcenter (by norm_num : 0 < (1 : ℝ))
      (by simpa [biasBound] using hbiasSmall) hratio
  simpa [biasBound] using hbias

/-- Compact-range control above stable index one under the integrable
centered-increment convention. -/
theorem exists_eventually_compactRange_bound_of_index_gt_one
    {α ε : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hint : Integrable (fun x : ℝ => x) ν)
    (hcenter : (∫ x : ℝ, x ∂ν) = 0)
    (hε : 0 < ε) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ ENNReal.ofReal ε := by
  let biasBound : ℝ → ℝ := discardedTailBiasConstant α
  apply exists_eventually_compactRange_bound_of_stableNorming hnorm hα₀ hα₂
    htail hε biasBound
  intro radiusMultiplier thresholdMultiplier hradius hbiasSmall
  have hratio : ∀ᶠ n : ℕ in atTop,
      ((n : ℕ) : ℝ) / n ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [hn']
  have hbias := eventually_truncatedIncrementBias_le_of_stableNorming_of_index_gt_one
    hnorm hα₀ hα₁ hα₂ htail hradius hint hcenter
      (by norm_num : 0 < (1 : ℝ)) (by simpa [biasBound] using hbiasSmall) hratio
  simpa [biasBound] using hbias

private theorem exists_eventually_compactRange_bound_of_ennrealBudget
    (normalization : ℕ → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hreal : ∀ ε : ℝ, 0 < ε →
      ∃ range : Set ℝ, IsCompact range ∧
        ∀ᶠ n : ℕ in atTop,
          (normalizedStepPathLaw ν normalization n)
            (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ ENNReal.ofReal ε)
    {η : ENNReal} (hη : 0 < η) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η := by
  by_cases htop : η = ⊤
  · refine ⟨Set.Icc (-1 : ℝ) 1, isCompact_Icc, ?_⟩
    filter_upwards with n
    calc
      (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) (Set.Icc (-1 : ℝ) 1))ᶜ ≤ 1 := by
        calc
          _ ≤ normalizedStepPathLaw ν normalization n Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := by simp
      _ ≤ η := by rw [htop]; exact le_top
  · have hε : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) htop
    obtain ⟨range, hrange, hbound⟩ := hreal η.toReal hε
    refine ⟨range, hrange, ?_⟩
    filter_upwards [hbound] with n hn
    rwa [ENNReal.ofReal_toReal htop] at hn

/-- Compact-range control below stable index one in the `ENNReal` error
interface used by the general Skorokhod tightness criterion. -/
theorem exists_eventually_compactRange_bound_of_index_lt_one_ennreal
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    {η : ENNReal} (hη : 0 < η) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η := by
  apply exists_eventually_compactRange_bound_of_ennrealBudget normalization ν
  · intro ε hε
    exact exists_eventually_compactRange_bound_of_index_lt_one
      hnorm hα₀ hα₁ htail hε
  · exact hη

/-- Compact-range control at stable index one in the `ENNReal` error
interface, under the source sine-centering condition. -/
theorem exists_eventually_compactRange_bound_of_index_one_ennreal
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    {η : ENNReal} (hη : 0 < η) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η := by
  apply exists_eventually_compactRange_bound_of_ennrealBudget normalization ν
  · intro ε hε
    exact exists_eventually_compactRange_bound_of_index_one
      hnorm htail hcenter hε
  · exact hη

/-- Compact-range control above stable index one in the `ENNReal` error
interface, under integrable centered increments. -/
theorem exists_eventually_compactRange_bound_of_index_gt_one_ennreal
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hint : Integrable (fun x : ℝ => x) ν)
    (hcenter : (∫ x : ℝ, x ∂ν) = 0)
    {η : ENNReal} (hη : 0 < η) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η := by
  apply exists_eventually_compactRange_bound_of_ennrealBudget normalization ν
  · intro ε hε
    exact exists_eventually_compactRange_bound_of_index_gt_one
      hnorm hα₀ hα₁ hα₂ htail hint hcenter hε
  · exact hη

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
