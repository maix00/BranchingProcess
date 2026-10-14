/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.FunctionalLimit
public import Topology.Cadlag.Skorokhod.LinearPath

/-!
# Brownian interior corridor in the diffusive entrance argument

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.brownianMiddlePathEvent`:
  the Brownian event printed in Wang Yiyang, Appendix A.2, with the
  endpoint window $(5/12,7/12)$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.interiorPathEvent`:
  $1/24<z+\sigma f(t)<23/24$ for $0\le t\le1$, with
  $11/24<z+\sigma f(1)<13/24$, a fixed subevent of the endpoint window
  $[5/12,7/12]$ in the thesis.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.interiorPathEvent_subset_brownianMiddlePathEvent`:
  the robust endpoint subevent belongs to the printed Brownian event.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.scaledInteriorPathEvent`:
  the corridor with spatial ratio $\sqrt n/\Delta$ and boundary offset
  $c/\Delta$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.interiorPathEvent_subset_scaledInteriorPathEvent`:
  the strict event lies in the scaled finite-width event when these
  parameters are close to $1$ and $0$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.mem_interiorPathEvent_of_linearApprox`:
  the line $t\mapsto(1/2-z)t/\sigma$, with a sufficiently small uniform
  error, lies in the interior event for $z\in[1/12,11/12]$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.linearBall_subset_interiorPathEvent`:
  a fixed Skorokhod ball around that line is contained in the interior event.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.eventually_interiorPathProbability_pos_uniform`:
  one positive lower bound for all $z\in[1/12,11/12]$ and all sufficiently
  large walk horizons, by Donsker's theorem and compactness.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.eventually_brownianMiddlePathProbability_pos_uniform`:
  the same lower bound for the exact endpoint window printed in the thesis.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.eventually_scaledInteriorPathProbability_pos_uniform`:
  the same lower bound survives the ratios $\sqrt n/\Delta\to1$ and
  $c/\Delta\to0$ in the finite-width corridor.

This is the Brownian support and compactness step in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma used in Chapter 3,
Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-- The Brownian middle-start event printed in Wang Yiyang,
Appendix A.2. -/
def brownianMiddlePathEvent (sigma z : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {path | (∀ t, 1 / 24 < z + sigma * path t ∧
      z + sigma * path t < 23 / 24) ∧
    5 / 12 < z + sigma * path ⊤ ∧
      z + sigma * path ⊤ < 7 / 12}

/-- The strict Brownian path event used for starts in the middle twelfths
of the entrance corridor. Its tighter endpoint window supplies a fixed
margin for the subsequent scale perturbation. -/
def interiorPathEvent (sigma z : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {path | (∀ t, 1 / 24 < z + sigma * path t ∧
      z + sigma * path t < 23 / 24) ∧
    11 / 24 < z + sigma * path ⊤ ∧
      z + sigma * path ⊤ < 13 / 24}

/-- The robust event is a subevent of the Brownian event in the printed
proof of Wang Yiyang, Appendix A.2. -/
theorem interiorPathEvent_subset_brownianMiddlePathEvent
    (sigma z : ℝ) :
    interiorPathEvent sigma z ⊆ brownianMiddlePathEvent sigma z := by
  intro path hpath
  exact ⟨hpath.1, by linarith [hpath.2.1], by linarith [hpath.2.2]⟩

/-- The normalized finite-width corridor used for the middle starting
interval. The ratio is `sqrt n / Delta` and `offset` is `c / Delta`. -/
def scaledInteriorPathEvent (sigma z ratio offset : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {path | (∀ t, offset ≤ z + ratio * sigma * path t ∧
      z + ratio * sigma * path t ≤ 1) ∧
    5 / 12 ≤ z + ratio * sigma * path ⊤ ∧
      z + ratio * sigma * path ⊤ ≤ 7 / 12}

/-- The strict Brownian interior event remains inside the finite-width
corridor when the spatial ratio tends to one and the moving-boundary
offset tends to zero. -/
theorem interiorPathEvent_subset_scaledInteriorPathEvent
    {sigma z ratio offset : ℝ}
    (hz : z ∈ Set.Icc (1 / 12) (11 / 12))
    (hratioLower : 99 / 100 ≤ ratio)
    (hratioUpper : ratio ≤ 101 / 100)
    (hoffset : offset ≤ 1 / 100) :
    interiorPathEvent sigma z ⊆
      scaledInteriorPathEvent sigma z ratio offset := by
  intro path hpath
  have hratioAbs : |ratio - 1| ≤ 1 / 100 := by
    rw [abs_le]
    constructor <;> linarith
  have hperturb (t : unitInterval) :
      |(ratio - 1) * (sigma * path t)| ≤ 1 / 100 := by
    have ht := hpath.1 t
    have hpathAbs : |sigma * path t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2, ht.1, ht.2]
    rw [abs_mul]
    calc
      |ratio - 1| * |sigma * path t| ≤
          (1 / 100) * 1 :=
        mul_le_mul hratioAbs hpathAbs (abs_nonneg _) (by norm_num)
      _ = 1 / 100 := by ring
  unfold scaledInteriorPathEvent
  constructor
  · intro t
    have ht := hpath.1 t
    have hp := abs_le.mp (hperturb t)
    constructor <;> nlinarith
  · have ht := hpath.2
    have hp := abs_le.mp (hperturb ⊤)
    constructor <;> nlinarith

/-- Uniform approximation of the straight line from `z` to `1/2`
keeps the translated path in the interior Brownian corridor. -/
theorem mem_interiorPathEvent_of_linearApprox
    {sigma z : ℝ} (_hsigma : 0 < sigma)
    (hz : z ∈ Set.Icc (1 / 12) (11 / 12))
    {path : CadlagPath unitInterval ℝ}
    (happrox : ∀ t,
      |sigma * path t - (1 / 2 - z) * (t : ℝ)| < 1 / 24) :
    path ∈ interiorPathEvent sigma z := by
  have hline (t : unitInterval) :
      1 / 12 ≤ z + (1 / 2 - z) * (t : ℝ) ∧
        z + (1 / 2 - z) * (t : ℝ) ≤ 11 / 12 := by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hlow := mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr ht1)
    have hhigh := mul_nonneg (sub_nonneg.mpr hz.2) (sub_nonneg.mpr ht1)
    constructor <;> nlinarith
  unfold interiorPathEvent
  constructor
  · intro t
    have h := abs_lt.mp (happrox t)
    have hl := hline t
    constructor <;> linarith
  · have h := abs_lt.mp (happrox ⊤)
    have htop : ((⊤ : unitInterval) : ℝ) = 1 := rfl
    rw [htop] at h
    constructor <;> linarith

/-- For all middle starting points, one common radius works around the
corresponding linear Brownian path. -/
theorem linearBall_subset_interiorPathEvent
    {sigma z : ℝ} (hsigma : 0 < sigma)
    (hz : z ∈ Set.Icc (1 / 12) (11 / 12)) :
    Metric.ball (Skorokhod.linearPath ((1 / 2 - z) / sigma))
        (1 / (100 * (sigma + 1))) ⊆ interiorPathEvent sigma z := by
  intro path hpath
  have hradius : 0 < 1 / (100 * (sigma + 1)) := by positivity
  have herror := Skorokhod.abs_sub_linear_lt_radius_mul_of_dist_lt
    hradius (Metric.mem_ball.mp hpath)
  have hslope : |1 / 2 - z| ≤ 5 / 12 := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hbound :
      sigma * (1 / (100 * (sigma + 1)) *
        (1 + |(1 / 2 - z) / sigma|)) < 1 / 24 := by
    rw [abs_div, abs_of_pos hsigma]
    have hden : 0 < 100 * (sigma + 1) := by positivity
    calc
      sigma * (1 / (100 * (sigma + 1)) *
          (1 + |1 / 2 - z| / sigma)) =
          (sigma + |1 / 2 - z|) / (100 * (sigma + 1)) := by
            field_simp [hsigma.ne']
      _ ≤ (sigma + 5 / 12) / (100 * (sigma + 1)) :=
        (div_le_div_iff_of_pos_right hden).2 (by linarith)
      _ < 1 / 24 := (div_lt_iff₀ hden).2 (by nlinarith)
  apply mem_interiorPathEvent_of_linearApprox hsigma hz
  intro t
  have h := herror t
  have heq : sigma * path t - (1 / 2 - z) * (t : ℝ) =
      sigma * (path t - ((1 / 2 - z) / sigma) * (t : ℝ)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hsigma]
  exact lt_trans (mul_lt_mul_of_pos_left h hsigma) hbound

/-- Donsker's theorem and the Brownian path support give a positive lower
bound uniform over the middle starting interval. This is the `p₀>0` and
compactness step in Wang Yiyang, Appendix A.2. -/
theorem eventually_interiorPathProbability_pos_uniform
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ Set.Icc (1 / 12) (11 / 12),
        q ≤ iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment ∈
              interiorPathEvent sigma z} := by
  let radius : ℝ := 1 / (100 * (sigma + 1))
  have hbound : 0 < 1 / sigma := by positivity
  have hradius : 0 < radius := by dsimp [radius]; positivity
  obtain ⟨q, hq, hball⟩ :=
    SmallDeviation.Entrance.eventually_measure_normalizedStep_linearBall_pos_on_Icc_of_centeredSecondMoment
      hν hsigma hP (1 / sigma) radius hbound hradius
  refine ⟨q, hq, ?_⟩
  filter_upwards [hball] with n hn
  intro z hz
  have hslope : (1 / 2 - z) / sigma ∈ Set.Icc (-(1 / sigma)) (1 / sigma) := by
    have habs : |1 / 2 - z| ≤ 5 / 12 := by
      rw [abs_le]
      constructor <;> linarith [hz.1, hz.2]
    have hnorm : |(1 / 2 - z) / sigma| ≤ 1 / sigma := by
      rw [abs_div, abs_of_pos hsigma]
      exact (div_le_div_iff_of_pos_right hsigma).2 (by linarith)
    exact abs_le.mp hnorm
  have hsubset :
      {increment | RandomWalk.normalizedStepCadlagPathIcc
        (fun _ => sigma * Real.sqrt n) n increment ∈
          Metric.ball (Skorokhod.linearPath ((1 / 2 - z) / sigma)) radius} ⊆
      {increment | RandomWalk.normalizedStepCadlagPathIcc
        (fun _ => sigma * Real.sqrt n) n increment ∈
          interiorPathEvent sigma z} := by
    intro increment hinc
    exact linearBall_subset_interiorPathEvent hsigma hz hinc
  exact (hn ((1 / 2 - z) / sigma) hslope).le.trans (measure_mono hsubset)

/-- The exact Brownian middle-start event printed in Wang Yiyang,
Appendix A.2, inherits the uniform Donsker lower bound from its robust
subevent. -/
theorem eventually_brownianMiddlePathProbability_pos_uniform
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ Set.Icc (1 / 12) (11 / 12),
        q ≤ iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment ∈
              brownianMiddlePathEvent sigma z} := by
  obtain ⟨q, hq, hbase⟩ :=
    eventually_interiorPathProbability_pos_uniform hν hsigma hP
  refine ⟨q, hq, ?_⟩
  filter_upwards [hbase] with n hn
  intro z hz
  exact (hn z hz).trans (measure_mono (by
    intro increment hinc
    exact interiorPathEvent_subset_brownianMiddlePathEvent sigma z hinc))

/-- The uniform Brownian interior estimate transfers to the finite-width
middle-start corridor as the scale ratio approaches one. This is the
compactness and Donsker step of Wang Yiyang, Appendix A.2. -/
theorem eventually_scaledInteriorPathProbability_pos_uniform
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P)
    {ratio offset : ℕ → ℝ}
    (hratio : Tendsto ratio atTop (𝓝 1))
    (hoffset : Tendsto offset atTop (𝓝 0)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ Set.Icc (1 / 12) (11 / 12),
        q ≤ iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment ∈
              scaledInteriorPathEvent sigma z (ratio n) (offset n)} := by
  obtain ⟨q, hq, hbase⟩ :=
    eventually_interiorPathProbability_pos_uniform hν hsigma hP
  have hratioLower : ∀ᶠ n : ℕ in atTop, 99 / 100 ≤ ratio n := by
    filter_upwards [hratio.eventually (Ioi_mem_nhds (by norm_num :
      (99 / 100 : ℝ) < 1))] with n hn
    exact hn.le
  have hratioUpper : ∀ᶠ n : ℕ in atTop, ratio n ≤ 101 / 100 := by
    filter_upwards [hratio.eventually (Iio_mem_nhds (by norm_num :
      (1 : ℝ) < 101 / 100))] with n hn
    exact hn.le
  have hoffsetUpper : ∀ᶠ n : ℕ in atTop, offset n ≤ 1 / 100 := by
    filter_upwards [hoffset.eventually (Iio_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 100))] with n hn
    exact hn.le
  refine ⟨q, hq, ?_⟩
  filter_upwards [hbase, hratioLower, hratioUpper, hoffsetUpper] with
    n hn hrlo hrhi ho
  intro z hz
  exact (hn z hz).trans (measure_mono (by
    intro increment hinc
    exact interiorPathEvent_subset_scaledInteriorPathEvent
      hz hrlo hrhi ho hinc))

end ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker

end
