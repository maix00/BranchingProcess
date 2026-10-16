/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.SourcePath
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.NormalContinuousBoundary
/-!
# Finite-variance bounds for block oscillation

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Range.blockOscillationEvent_partialSum_abs_le`:
  a block whose range is at most $\Delta$ has every displacement in
  $[-\Delta,\Delta]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Range.blockOscillationEvent_subset_enlargedSourceCorridor`:
  the block event lies in a centered source corridor after enlarging its
  width by a factor greater than two.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Range.eventually_iidSequenceLaw_blockOscillationProbability_le_exp_of_centeredUnitVariance`:
  the source-path rate gives the finite-variance exponential block bound.

The block-oscillation rate follows A. A. Mogul'skii, *Small Deviations in a
Space of Trajectories*, Theorem 3, Section 4, p. 764 of the 1974 Russian original (English translation,
DOI 10.1137/1119081). It is a reusable bound for random-walk range events.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Range

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor

/-- A block oscillation bound controls every partial sum relative to the
initial value zero. -/
theorem blockOscillationEvent_partialSum_abs_le
    {n : ℕ} (hn : 0 < n) {width : ℝ} (increment : ℕ → ℝ)
    (hosc : blockOscillationEvent width (n - 1)
      (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment))
    (k : Fin n) :
    |AdditivePath.displacement (k : ℕ) increment| ≤ width := by
  have hosc' : OscillationBounded
      (fun i : Fin ((n - 1) + 1) =>
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment) i)
      width := by
    change OscillationBounded _ width at hosc
    exact hosc
  have h := hosc' 0 (Fin.cast (by omega : n = (n - 1) + 1) k)
  change |Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment) 0 -
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)
          (Fin.cast (by omega : n = (n - 1) + 1) k)| ≤ width at h
  rw [partialSum_blockCoordinates (start := 0) (increment := increment) 0,
    partialSum_blockCoordinates (start := 0) (increment := increment)
      (Fin.cast (by omega : n = (n - 1) + 1) k)] at h
  simpa [Fin.cast] using h

/-- A block whose oscillation is at most `width` lies in a strict centered
source corridor after enlarging its spatial scale by a factor greater than
two. The source horizon `n` records exactly the sums through time `n - 1`. -/
theorem blockOscillationEvent_subset_enlargedSourceCorridor
    {n : ℕ} (hn : 0 < n) {width factor : ℝ}
    (hwidth : 0 < width) (hfactor : 2 < factor)
    (increment : ℕ → ℝ) :
    blockOscillationEvent width (n - 1)
      (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment) →
    sourceNormalizedStepCadlagPathIcc (fun _ => factor * width) n increment ∈
      relativeContinuousBoundaryCorridorSet
        (ContinuousMap.const unitInterval (-(1 / 2 : ℝ)))
        (ContinuousMap.const unitInterval (1 / 2 : ℝ)) := by
  intro hosc
  let scale : ℕ → ℝ := fun _ => factor * width
  have hscale : 0 < scale n := mul_pos (by linarith) hwidth
  have htube : InOpenHorizontalTube (1 / 2 : ℝ) (scale n) (n - 1) increment := by
    intro k
    let j : Fin n := ⟨k.val + 1, by omega⟩
    have hpartial := blockOscillationEvent_partialSum_abs_le hn increment hosc j
    have hpartial' : |AdditivePath.displacement (k + 1) increment| ≤ width := by
      simpa [j] using hpartial
    have hfactorWidth : width < scale n / 2 := by
      dsimp [scale]
      nlinarith
    have hbounds := abs_le.mp hpartial'
    change -(1 / 2 : ℝ) * scale n < AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment < (1 - 1 / 2 : ℝ) * scale n
    constructor
    · dsimp [scale]
      nlinarith [hbounds.1, hfactorWidth]
    · dsimp [scale]
      nlinarith [hbounds.2, hfactorWidth]
  have hpath : sourceNormalizedStepCadlagPathIcc scale n increment ∈
      Skorokhod.rangeInOpenInterval (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    have hequiv := sourceNormalizedStepCadlagPathIcc_mem_rangeInOpenInterval_iff
      scale hn hscale (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) increment
    convert hequiv.mpr htube using 1 <;> norm_num
  change sourceNormalizedStepCadlagPathIcc scale n increment ∈
    Skorokhod.terminalLeftPathSpace ∩
      continuousBoundaryCorridorSet
        (ContinuousMap.const unitInterval (-(1 / 2 : ℝ)))
        (ContinuousMap.const unitInterval (1 / 2 : ℝ))
  refine ⟨Skorokhod.terminalLeftPath_mem_space
    (normalizedStepCadlagPathIcc scale n increment), ?_⟩
  rcases (Skorokhod.mem_rangeInOpenInterval_iff.mp hpath) with
    ⟨margin, hmargin, hinside⟩
  refine ⟨?_, ?_⟩
  · simp [sourceNormalizedStepCadlagPathIcc_apply_of_ne_top,
      normalizedStepPath_zero]
  · intro t
    have ht := hinside t
    change -(1 / 2 : ℝ) <
        sourceNormalizedStepCadlagPathIcc scale n increment t ∧
      sourceNormalizedStepCadlagPathIcc scale n increment t < (1 / 2 : ℝ)
    constructor
    · exact lt_of_lt_of_le (by linarith [hmargin]) ht.1
    · exact lt_of_le_of_lt ht.2 (by linarith [hmargin])

/-- Raw finite-variance Mogul'skii rates give an exponential upper bound for
the IID probability of a long block oscillation event. The hypothesis
`scale / sqrt(n) → 0` is essential: this theorem concerns blocks whose length
is asymptotically larger than the squared width. -/
theorem eventually_iidSequenceLaw_blockOscillationProbability_le_exp_of_centeredUnitVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ}
    (hscale : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    {factor rate : ℝ} (hfactor : 2 < factor) (hrate : 0 < rate)
    (hrate_lt : rate < Real.pi ^ 2 / (2 * factor ^ 2)) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        blockOscillationEvent (scale n) (n - 1)
          (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)} ≤
        ENNReal.ofReal (Real.exp (-rate * ((n : ℝ) / scale n ^ 2))) := by
  let enlargedScale : ℕ → ℝ := fun n => factor * scale n
  let lower : C(unitInterval, ℝ) :=
    ContinuousMap.const unitInterval (-(1 / 2 : ℝ))
  let upper : C(unitInterval, ℝ) :=
    ContinuousMap.const unitInterval (1 / 2 : ℝ)
  let corridorEvent (n : ℕ) : Set (ℕ → ℝ) :=
    {increment | sourceNormalizedStepCadlagPathIcc enlargedScale n increment ∈
      relativeContinuousBoundaryCorridorSet lower upper}
  have hfactorPos : 0 < factor := by linarith
  have hscale' : Asymptotics.IsSmallDeviationScale enlargedScale
      (fun n => Real.sqrt n) := by
    apply Asymptotics.IsSmallDeviationScale.of_tendsto
    · simpa [enlargedScale, mul_comm] using
        (Asymptotics.IsSmallDeviationScale.tendsto_atTop hscale).const_mul_atTop hfactorPos
    · have h := (Asymptotics.IsSmallDeviationScale.tendsto_div hscale).const_mul factor
      have heq : (fun n : ℕ => enlargedScale n / Real.sqrt n) =ᶠ[atTop]
          fun n => factor * (scale n / Real.sqrt n) := by
        filter_upwards with n
        simp [enlargedScale, div_eq_mul_inv, mul_assoc]
      simpa using h.congr' heq.symm
  have hlower : ∀ t : unitInterval, lower t < upper t := by
    intro t
    simp [lower, upper]
  have hstartLower : lower ⊥ < 0 := by norm_num [lower]
  have hstartUpper : 0 < upper ⊥ := by norm_num [upper]
  have hratePath := centeredUnitVariance_sourceRelativeContinuousBoundaryProbabilityRate
    hscale' hcentered hsquare hvariance lower upper hlower hstartLower hstartUpper
  have hdensity : continuousBoundaryDensity 2 lower upper = fun _ => (1 : ℝ) := by
    funext t
    change (upper t - lower t) ^ (-(2 : ℝ)) = 1
    rw [show upper t - lower t = 1 by norm_num [lower, upper]]
    norm_num
  have henergy : ∫ t : unitInterval, continuousBoundaryDensity 2 lower upper t ∂volume = 1 := by
    rw [hdensity]
    simp
  have hlimit : Tendsto
      (fun n : ℕ => enlargedScale n ^ 2 / (n : ℝ) *
        Real.log (iidSequenceLaw ν (corridorEvent n)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
    have h := hratePath.2
    rw [henergy] at h
    simpa [corridorEvent] using h
  have hrateGap : factor ^ 2 * rate < Real.pi ^ 2 / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * factor ^ 2)).mp hrate_lt
    nlinarith
  have htarget : -(Real.pi ^ 2) / 2 < -(factor ^ 2 * rate) := by
    nlinarith
  have hlogBound : ∀ᶠ n : ℕ in atTop,
      enlargedScale n ^ 2 / (n : ℝ) *
        Real.log (iidSequenceLaw ν (corridorEvent n)).toReal <
          -(factor ^ 2 * rate) :=
    hlimit.eventually (eventually_lt_nhds htarget)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    (Asymptotics.IsSmallDeviationScale.tendsto_atTop hscale).eventually
      (eventually_gt_atTop 0)
  filter_upwards [hlogBound, hscalePos, eventually_gt_atTop (0 : ℕ), hratePath.1]
    with n hlog hs hn hcorridorPos
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlargeScale : 0 < enlargedScale n := mul_pos hfactorPos hs
  have hden : 0 < enlargedScale n ^ 2 / (n : ℝ) :=
    div_pos (sq_pos_of_pos hlargeScale) hnReal
  have hlog : Real.log (iidSequenceLaw ν (corridorEvent n)).toReal <
      -rate * ((n : ℝ) / scale n ^ 2) := by
    have hdiv : Real.log (iidSequenceLaw ν (corridorEvent n)).toReal <
        (-(factor ^ 2 * rate)) / (enlargedScale n ^ 2 / (n : ℝ)) :=
      (lt_div_iff₀ hden).2 (by nlinarith [hlog])
    have hscaleEq : enlargedScale n ^ 2 / (n : ℝ) =
        factor ^ 2 * (scale n ^ 2 / (n : ℝ)) := by
      simp [enlargedScale]
      ring
    rw [hscaleEq] at hdiv
    have hscaleSq : 0 < scale n ^ 2 := sq_pos_of_pos hs
    have htargetEq : (-(factor ^ 2 * rate)) /
        (factor ^ 2 * (scale n ^ 2 / (n : ℝ))) =
        -rate * ((n : ℝ) / scale n ^ 2) := by
      field_simp [ne_of_gt hfactorPos, ne_of_gt hscaleSq, ne_of_gt hnReal]
    rw [htargetEq] at hdiv
    exact hdiv
  have hcorridorBound : iidSequenceLaw ν (corridorEvent n) ≤
      ENNReal.ofReal (Real.exp (-rate * ((n : ℝ) / scale n ^ 2))) := by
    have hqle : iidSequenceLaw ν (corridorEvent n) ≤ 1 :=
      calc
        iidSequenceLaw ν (corridorEvent n) ≤ iidSequenceLaw ν Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hqtop : iidSequenceLaw ν (corridorEvent n) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt hqle ENNReal.one_lt_top)
    have hqpos : 0 < (iidSequenceLaw ν (corridorEvent n)).toReal := by
      simpa [corridorEvent, lower, upper, enlargedScale] using hcorridorPos
    have hreal : Real.exp
        (Real.log (iidSequenceLaw ν (corridorEvent n)).toReal) <
          Real.exp (-rate * ((n : ℝ) / scale n ^ 2)) :=
      Real.exp_strictMono hlog
    have hprobReal : (iidSequenceLaw ν (corridorEvent n)).toReal <
        Real.exp (-rate * ((n : ℝ) / scale n ^ 2)) := by
      rwa [Real.exp_log hqpos] at hreal
    rw [← ENNReal.ofReal_toReal hqtop]
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).2 hprobReal.le
  have hsubset : {increment : ℕ → ℝ |
      blockOscillationEvent (scale n) (n - 1)
        (Combinatorics.Sequence.blockCoordinates 0 (n - 1) increment)} ⊆
      corridorEvent n := by
    intro increment hosc
    exact blockOscillationEvent_subset_enlargedSourceCorridor hn hs hfactor
      increment hosc
  exact (measure_mono hsubset).trans hcorridorBound

end ProbabilityTheory.RandomWalk.SmallDeviation.Range

end
