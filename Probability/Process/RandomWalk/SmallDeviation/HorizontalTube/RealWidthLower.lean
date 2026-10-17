/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.FiniteVarianceLower

/-!
# Real-width horizontal-tube endpoint-window lower bounds

The public declarations in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeEndpointWindowEvent_floor_subset_of_endpointMargins`: an integer-width endpoint-window tube lies in a real-width tube when the endpoint window has a fixed positive margin.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp`: the uniform exponential lower bound for real widths and endpoint windows containing a fixed strict interior interval.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.exists_uniform_finiteRealWidthTubeProbability_ge_exp`: one pair of width and time-ratio thresholds works for every member of a finite parameter family.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.realWidthTubeProbability_ge_exp_globalScale`: compares the rounded-width exponent with a prescribed global width exponent.

The exponential rate specializes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii),
using Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in
the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755--765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(1) (1975),
726--736, DOI 10.1137/1119081.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- An integer-width horizontal tube at width $\lfloor D\rfloor$ is
contained in the real-width tube at width $D$. If the endpoint window
$[u,v]$ has margin $\gamma$ inside $[U,V]$ and $D\ge1/\gamma$, its absolute
endpoint interval is contained as well. This lets the integer-width form of
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii), supply block estimates at the real
widths in the proof of Lemma 3.5. -/
theorem horizontalTubeEndpointWindowEvent_floor_subset_of_endpointMargins
    {horizon : ℕ} {a u v U V margin width : ℝ}
    (hwidth : 0 ≤ width) (haLower : 0 ≤ a) (haUpper : a ≤ 1)
    (huLower : 0 ≤ u) (huv : u ≤ v) (hvUpper : v ≤ 1)
    (hmargin : 0 < margin) (hwidthLarge : 1 / margin ≤ width)
    (hmarginLower : U + margin ≤ u)
    (hmarginUpper : v + margin ≤ V) :
    horizontalTubeEndpointWindowEvent a (⌊width⌋₊ : ℝ) horizon u v ⊆
      horizontalTubeEndpointWindowEvent a width horizon U V := by
  let integerWidth : ℝ := (⌊width⌋₊ : ℝ)
  have hfloorLower : integerWidth ≤ width := by
    exact Nat.floor_le hwidth
  have hgapLower : 0 ≤ width - integerWidth := sub_nonneg.mpr hfloorLower
  have hgapUpper : width - integerWidth ≤ 1 := by
    have hfloorUpper : width < integerWidth + 1 := by
      exact Nat.lt_floor_add_one width
    linarith
  have hmarginScale : 1 ≤ margin * width := by
    simpa [mul_comm] using (div_le_iff₀ hmargin).1 hwidthLarge
  have hendpointLower : (U - a) * width ≤ (u - a) * integerWidth := by
    have hmarginCoeff : margin ≤ u - U := by linarith [hmarginLower]
    have hmarginProduct : margin * width ≤ (u - U) * width :=
      mul_le_mul_of_nonneg_right hmarginCoeff hwidth
    have hrounding : (u - a) * (width - integerWidth) ≤ 1 := by
      calc
        (u - a) * (width - integerWidth) ≤
            1 * (width - integerWidth) :=
          mul_le_mul_of_nonneg_right
            (show u - a ≤ (1 : ℝ) by linarith [huv, hvUpper, haLower])
            hgapLower
        _ = width - integerWidth := by ring
        _ ≤ 1 := hgapUpper
    have hidentity : (u - a) * integerWidth - (U - a) * width =
        (u - U) * width - (u - a) * (width - integerWidth) := by ring
    rw [← sub_nonneg]
    rw [hidentity]
    linarith
  have hendpointUpper : (v - a) * integerWidth ≤ (V - a) * width := by
    have hmarginCoeff : margin ≤ V - v := by linarith [hmarginUpper]
    have hmarginProduct : margin * width ≤ (V - v) * width :=
      mul_le_mul_of_nonneg_right hmarginCoeff hwidth
    have hrounding : -1 ≤ (v - a) * (width - integerWidth) := by
      calc
        -1 ≤ -(width - integerWidth) := by linarith [hgapUpper]
        _ = (-1) * (width - integerWidth) := by ring
        _ ≤ (v - a) * (width - integerWidth) :=
          mul_le_mul_of_nonneg_right
            (show (-1 : ℝ) ≤ v - a by linarith [huLower, haUpper])
            hgapLower
    have hidentity : (V - a) * width - (v - a) * integerWidth =
        (V - v) * width + (v - a) * (width - integerWidth) := by ring
    rw [← sub_nonneg]
    rw [hidentity]
    linarith
  have htubeLower : -a * width ≤ -a * integerWidth := by
    calc
      -a * width = -(a * width) := by ring
      _ ≤ -(a * integerWidth) := neg_le_neg
        (mul_le_mul_of_nonneg_left hfloorLower haLower)
      _ = -a * integerWidth := by ring
  have htubeUpper : (1 - a) * integerWidth ≤ (1 - a) * width :=
    mul_le_mul_of_nonneg_left hfloorLower (by linarith [haUpper])
  intro increment hevent
  change InHorizontalTube a integerWidth horizon increment ∧
      AdditivePath.displacement horizon increment ∈
        Set.Icc ((u - a) * integerWidth) ((v - a) * integerWidth) at hevent
  rcases hevent with ⟨htube, hend⟩
  refine ⟨?_, ?_⟩
  · intro k
    rcases htube k with ⟨hleft, hright⟩
    exact ⟨htubeLower.trans hleft, hright.trans htubeUpper⟩
  · rcases Set.mem_Icc.mp hend with ⟨hleft, hright⟩
    rw [Set.mem_Icc]
    exact ⟨hendpointLower.trans hleft, hright.trans hendpointUpper⟩


/-- Uniform exponential lower bound for a real-width tube, with an
endpoint interval containing a fixed strict interior interval. -/
theorem exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d a u v : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ, ∀ width U V margin : ℝ,
      0 < width → 0 < margin →
      width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
      U + margin ≤ u → v + margin ≤ V →
      ∀ horizon : ℕ,
        ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
        ENNReal.ofReal (Real.exp
          (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
        horizontalTubeEndpointWindowProbability
          (iidSequenceLaw ν) a width horizon U V := by
  obtain ⟨width₀, ratio₀, hinteger⟩ :=
    HorizontalTube.exists_eventually_horizontalTubeEndpointWindowProbability_ge_exp_uniform
      hν hsigma ha haOne hu huv hv hd
  refine ⟨width₀, ratio₀, ?_⟩
  intro width U V margin hwidth hmargin hwidthFloor hwidthMargin
    hmarginLower hmarginUpper horizon hratio
  have hsource := hinteger ⌊width⌋₊ hwidthFloor horizon hratio
  have hsubset :=
    horizontalTubeEndpointWindowEvent_floor_subset_of_endpointMargins
      hwidth.le ha.le haOne.le hu.le huv.le hv.le
      hmargin hwidthMargin hmarginLower hmarginUpper
      (horizon := horizon)
  exact hsource.trans (measure_mono hsubset)

/-- Compare the narrowed tube's rounded-width exponent with the global
staircase width, as in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.5. -/
theorem realWidthTubeProbability_ge_exp_globalScale
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {a width U V globalWidth d target : ℝ} {horizon : ℕ}
    (hfloor : 0 < (⌊width⌋₊ : ℝ))
    (hglobalWidth : 0 < globalWidth)
    (hscale : d * globalWidth ^ 2 ≤
      target * (⌊width⌋₊ : ℝ) ^ 2)
    (hsource : ENNReal.ofReal (Real.exp
      (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
      horizontalTubeEndpointWindowProbability
        (iidSequenceLaw ν) a width horizon U V) :
    ENNReal.ofReal (Real.exp
      (-target * (horizon : ℝ) / globalWidth ^ 2)) ≤
      horizontalTubeEndpointWindowProbability
        (iidSequenceLaw ν) a width horizon U V := by
  have hrate : d / (⌊width⌋₊ : ℝ) ^ 2 ≤
      target / globalWidth ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hfloor)
      (sq_pos_of_pos hglobalWidth)).2
    nlinarith [hscale]
  have hmul := mul_le_mul_of_nonneg_right hrate
    (Nat.cast_nonneg horizon : 0 ≤ (horizon : ℝ))
  have hexponent :
      -target * (horizon : ℝ) / globalWidth ^ 2 ≤
      -d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2 := by
    calc
      -target * (horizon : ℝ) / globalWidth ^ 2 =
          -(target / globalWidth ^ 2 * (horizon : ℝ)) := by ring
      _ ≤ -(d / (⌊width⌋₊ : ℝ) ^ 2 * (horizon : ℝ)) :=
        neg_le_neg hmul
      _ = -d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2 := by ring
  exact (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)).trans
    hsource


/-- A maximum of the finitely many integer-width and time-ratio thresholds
works for all spatial bins. -/
theorem exists_uniform_finiteRealWidthTubeProbability_ge_exp
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {m : ℕ} (a u v : Fin m → ℝ)
    (ha : ∀ l, 0 < a l) (haOne : ∀ l, a l < 1)
    (hu : ∀ l, 0 < u l) (huv : ∀ l, u l < v l)
    (hv : ∀ l, v l < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ,
      ∀ l : Fin m, ∀ width U V margin : ℝ,
        0 < width → 0 < margin →
        width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
        U + margin ≤ u l → v l + margin ≤ V →
        ∀ horizon : ℕ,
          ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
          ENNReal.ofReal (Real.exp
            (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
          horizontalTubeEndpointWindowProbability
            (iidSequenceLaw ν) (a l) width horizon U V := by
  classical
  have hperBin (l : Fin m) : ∃ width₀ ratio₀ : ℕ,
      ∀ width U V margin : ℝ,
        0 < width → 0 < margin →
        width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
        U + margin ≤ u l → v l + margin ≤ V →
        ∀ horizon : ℕ,
          ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
          ENNReal.ofReal (Real.exp
            (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
          horizontalTubeEndpointWindowProbability
            (iidSequenceLaw ν) (a l) width horizon U V :=
    exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp
      hν hsigma (ha l) (haOne l) (hu l) (huv l) (hv l) hd
  choose widthAt ratioAt hAt using hperBin
  let width₀ := Finset.univ.sup widthAt
  let ratio₀ := Finset.univ.sup ratioAt
  refine ⟨width₀, ratio₀, ?_⟩
  intro l width U V margin hwidth hmargin hwidth₀ hwidthMargin
    hmarginLower hmarginUpper horizon hratio
  have hwidthAt : widthAt l ≤ width₀ :=
    Finset.le_sup (Finset.mem_univ l)
  have hratioAt : ratioAt l ≤ ratio₀ :=
    Finset.le_sup (Finset.mem_univ l)
  apply hAt l width U V margin hwidth hmargin
    (hwidthAt.trans hwidth₀) hwidthMargin
    hmarginLower hmarginUpper horizon
  exact (Nat.mul_le_mul_right _ hratioAt).trans hratio


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
