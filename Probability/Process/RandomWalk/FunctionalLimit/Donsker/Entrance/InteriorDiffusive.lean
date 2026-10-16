/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Entrance.InteriorFinite
public import Analysis.Asymptotics.Scale.ShiftedFloor
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.ProcessExistence

/-!
# Diffusive middle-start entrance bound

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.eventually_diffusiveInteriorProbability_pos_uniform`:
  for $n_\Delta=\lfloor\Delta^2\rfloor$ and every
  $x\in[\Delta/12,11\Delta/12]$, the probability of
  $c\le x+S_j\le\Delta$ for $1\le j\le n_\Delta$, with
  $x+S_{n_\Delta}\in[5\Delta/12,7\Delta/12]$, has one positive
  lower bound for all sufficiently large real widths.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.eventually_diffusiveInteriorProbability_pos_uniform_of_centeredSecondMoment`:
  the same statement from the increment law alone, with its Gaussian path
  law constructed internally.

This is the middle starting interval in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Appendix A.2, Lemma A.7, used in the proof of Chapter 3, Lemma 3.5.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker

/-- The diffusive middle-start finite event has a uniform positive
probability under centered finite-variance increments. -/
theorem eventually_diffusiveInteriorProbability_pos_uniform
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (drift : ℝ) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc (width n / 12) (11 / 12 * width n),
        q ≤ iidSequenceLaw ν
          (finiteInteriorEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
            (width n) drift start) := by
  let length : ℕ → ℕ :=
    Asymptotics.floorBlockLength (fun k => width k ^ 2)
  have hargument : Tendsto (fun n => width n ^ 2) atTop atTop := by
    have hmul : Tendsto (fun n => width n * width n) atTop atTop :=
      hwidth.atTop_mul_atTop₀ hwidth
    simpa [pow_two] using hmul
  have hlength : Tendsto length atTop atTop :=
    Asymptotics.tendsto_floorBlockLength_atTop hargument
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hstart : ∀ᶠ n : ℕ in atTop, drift ≤ width n / 12 := by
    filter_upwards [hwidth.eventually (eventually_gt_atTop (12 * drift))] with n hn
    linarith
  have hratio : Tendsto (fun n => Real.sqrt (length n) / width n)
      atTop (𝓝 1) := by
    have h := Asymptotics.tendsto_width_div_sqrt_floor_sq_sub_nat hwidth 0
    have hinv := h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [length, inv_div] using hinv
  have hoffset : Tendsto (fun n => drift / width n) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => drift) atTop (𝓝 drift)).div_atTop hwidth
  exact eventually_finiteInteriorProbability_pos_uniform
    hν hsigma hP hlength hwidthPos hstart hratio hoffset

/-- The middle-start entrance bound from the centered finite-variance
increment law alone. The Gaussian clock-process law required by the support
argument is obtained from the source Donsker limit. -/
theorem eventually_diffusiveInteriorProbability_pos_uniform_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (drift : ℝ) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc (width n / 12) (11 / 12 * width n),
        q ≤ iidSequenceLaw ν
          (finiteInteriorEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
            (width n) drift start) := by
  let νunit := ν.map (fun x => x / sigma)
  have hνunit : IsCenteredUnitSecondMoment νunit := hν.map_div hsigma
  have hsquare : Integrable (fun x : ℝ => x ^ 2) νunit := by
    apply (memLp_two_iff_integrable_sq
      stronglyMeasurable_id.aestronglyMeasurable).1
    exact IsCenteredUnitSecondMoment.memLp_two hνunit
  have hunitDOA' :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
      νunit hνunit.1 hsquare (by rw [hνunit.2]; norm_num)
  have hunitDOA : IsInDomainOfAttractionAlong νunit (gaussianReal 0 1)
      (fun n => Real.sqrt n) (fun _ => 0) := by
    simpa [hνunit.2] using hunitDOA'
  have hnormalization : ∀ n : ℕ, 0 < n → 0 < Real.sqrt (n : ℝ) := by
    intro n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have htight :=
    RandomWalk.FunctionalLimit.Normal.isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hunitDOA hnormalization
  have hstable : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (v := 1) (by norm_num)
  obtain ⟨P, hP, _sub, _strict, _limit⟩ :=
    RandomWalk.FunctionalLimit.Stable.exists_stableClockProcessLaw_of_tightSource
      hunitDOA hstable htight
  exact eventually_diffusiveInteriorProbability_pos_uniform
    hν hsigma hP hwidth drift

end ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker

end
