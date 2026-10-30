/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Tightness.BlockTail
public import Probability.Process.RandomWalk.Path.Skorokhod.Range
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import MeasureTheory.Measure.CadlagPath.Tightness
import all Probability.Process.RandomWalk.FunctionalLimit.Stable.Tightness.Lemmas.Parameters

/-!
# Compact range bounds for stable random walks

This file is the stable-domain adapter from regular variation and truncation
centering to compact-range control of the normalized path laws. The topology
and compactness of state-space ranges are supplied by the general càdlàg and
Skorokhod layers; only the random-walk scale and its stable asymptotics appear
here.
## Public declarations

Let $\mu_n=\texttt{normalizedStepPathLaw}(\nu,\texttt{normalization},n)$. For a
compact state-space set $K$, write $R_K=\{f:\operatorname{range}(f)\subseteq K\}$.

- `eventually_measure_normalizedStepPathLaw_rangeExit_le_of_stableNorming`
  proves, for $r,\theta>0$ and explicit regular-variation margins $c_T,c_M$,
  \[
   \mu_n\!\left(R_{[-\theta,\theta]}^c\right)
   \le \operatorname{ENNReal.ofReal}\!\left(c_T+\frac{4c_M}{\theta^2}\right)
  \]
  eventually, where $\frac{2-\alpha}{\alpha}r^{-\alpha}<c_T$ and
  $r^{2-\alpha}<c_M$.
- `exists_eventually_compactRange_bound_of_stableNorming` proves that every
  $\varepsilon>0$ admits compact $K\subseteq\mathbb R$ with
  $\mu_n(R_K^c)\le\operatorname{ENNReal.ofReal}(\varepsilon)$ eventually.
- `exists_eventually_compactRange_bound_of_index_lt_one`,
  `exists_eventually_compactRange_bound_of_index_one`, and
  `exists_eventually_compactRange_bound_of_index_gt_one` establish this same
  conclusion for the uncentered, Mogulskii sine-centered, and integrable
  centered stable regimes, respectively.
- `exists_eventually_compactRange_bound_of_index_lt_one_ennreal`,
  `exists_eventually_compactRange_bound_of_index_one_ennreal`, and
  `exists_eventually_compactRange_bound_of_index_gt_one_ennreal` give the same
  compact $K$ conclusion with arbitrary $0<\eta\le\infty$ and
  $\mu_n(R_K^c)\le\eta$ eventually.

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
condition in Theorem 3, Section 4 of the 1974 Russian original by A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081. -/
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
  apply MeasureTheory.exists_eventually_compactRange_bound_of_real_error
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
  apply MeasureTheory.exists_eventually_compactRange_bound_of_real_error
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
  apply MeasureTheory.exists_eventually_compactRange_bound_of_real_error
  · intro ε hε
    exact exists_eventually_compactRange_bound_of_index_gt_one
      hnorm hα₀ hα₁ hα₂ htail hint hcenter hε
  · exact hη

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
