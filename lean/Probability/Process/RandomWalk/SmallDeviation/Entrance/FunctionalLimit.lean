/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Real
public import Probability.Distributions.Stable.Attraction.Normal
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.PathLimit
public import Probability.Process.RandomWalk.Path.Skorokhod.Basic
public import Probability.Sequence.IID
public import Probability.Process.Stable.PathLaw.LinearTube
public import Mathlib.Topology.Compactness.Compact
public import Topology.Cadlag.Skorokhod.LinearPath

/-!
# Donsker transfer for a linear open tube

The Gaussian stable path-law linear-tube positivity theorem and the
normal-domain functional limit imply a positive lower bound, uniform for all
sufficiently large sample sizes, on the probability that a normalized
random-walk step path lies in a fixed `J₁` ball around a given line. The target
is a path law, so no particular Brownian sample-space realization is needed.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- Donsker's open-set lower bound for a linear path tube. The target is any
standard Gaussian stable path law, and the lower bound is positive and uniform
for all sufficiently large `n`. -/
theorem eventually_measure_normalizedStep_linearBall_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P)
    (slope radius : ℝ) (hradius : 0 < radius) :
    ∃ q : ENNReal, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q < iidSequenceLaw ν
        {increment | RandomWalk.normalizedStepCadlagPathIcc
          (fun n => Real.sqrt n) n increment ∈
            Metric.ball (Skorokhod.linearPath slope) radius} := by
  change (∫ x, x ∂ν) = 0 ∧ (∫ x, x ^ 2 ∂ν) = 1 at hν
  obtain ⟨hcentered, hsecondMoment⟩ := hν
  let normalization : ℕ → ℝ := fun n => Real.sqrt n
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν := by
    apply (memLp_two_iff_integrable_sq
      stronglyMeasurable_id.aestronglyMeasurable).1
    exact IsCenteredUnitSecondMoment.memLp_two ⟨hcentered, hsecondMoment⟩
  have hDOA' :=
    isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
      ν hcentered hsquare (by rw [hsecondMoment]; norm_num)
  have hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0) := by
    simpa [normalization, hsecondMoment] using hDOA'
  have hnormalization : ∀ n, 0 < n → 0 < normalization n := by
    intro n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hpathLimit :=
    RandomWalk.FunctionalLimit.Normal.tendsto_normalizedStepPathLaw_of_gaussian
      hDOA hnormalization hP
  have hballOpen : IsOpen (Metric.ball (Skorokhod.linearPath slope) radius) :=
    Metric.isOpen_ball
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    hpathLimit hballOpen
  have hpositive : 0 < P (Metric.ball (Skorokhod.linearPath slope) radius) :=
    hP.measure_linearPathBall_pos slope radius hradius
  obtain ⟨q, hqpos, hqle⟩ := exists_between hpositive
  have hqLiminf : q < atTop.liminf (fun n : ℕ =>
      RandomWalk.normalizedStepPathLaw ν normalization n
        (Metric.ball (Skorokhod.linearPath slope) radius)) :=
    hqle.trans_le hport
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ =>
      RandomWalk.normalizedStepPathLaw ν normalization n
        (Metric.ball (Skorokhod.linearPath slope) radius)) :=
    ⟨0, Filter.Eventually.of_forall fun _ => bot_le⟩
  have hevent := Filter.eventually_lt_of_lt_liminf hqLiminf hbounded
  have hmap (n : ℕ) :
      RandomWalk.normalizedStepPathLaw ν normalization n
          (Metric.ball (Skorokhod.linearPath slope) radius) =
        iidSequenceLaw ν {increment |
          RandomWalk.normalizedStepCadlagPathIcc normalization n increment ∈
            Metric.ball (Skorokhod.linearPath slope) radius} := by
    unfold RandomWalk.normalizedStepPathLaw
    exact Measure.map_apply_of_aemeasurable
      (RandomWalk.measurable_normalizedStepCadlagPathIcc normalization n).aemeasurable
      hballOpen.measurableSet
  refine ⟨q, hqpos, ?_⟩
  filter_upwards [hevent] with n hn
  rw [← hmap n]
  simpa [normalization] using hn

/-- The fixed linear-ball Donsker lower bound for a centered finite-variance
source with variance `sigma²`. This is the unit-variance result transported
through coordinatewise division by the positive standard deviation; the
original walk is normalized by `sigma * sqrt n`. -/
theorem eventually_measure_normalizedStep_linearBall_pos_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P)
    (slope radius : ℝ) (hradius : 0 < radius) :
    ∃ q : ENNReal, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q < iidSequenceLaw ν
        {increment | RandomWalk.normalizedStepCadlagPathIcc
          (fun _ => sigma * Real.sqrt n) n increment ∈
            Metric.ball (Skorokhod.linearPath slope) radius} := by
  let νunit := ν.map (fun x => x / sigma)
  have hνunit : IsCenteredUnitSecondMoment νunit := hν.map_div hsigma
  obtain ⟨q, hqpos, hqevent⟩ :=
    eventually_measure_normalizedStep_linearBall_pos hνunit hP slope radius hradius
  have hcoordinate : Measurable (fun x : ℕ → ℝ => fun k => x k / sigma) := by
    exact Measurable.of_eval fun k => by
      exact (measurable_id.div_const sigma).comp (measurable_pi_apply k)
  have hcoordinateLaw :
      (iidSequenceLaw ν).map (fun x : ℕ → ℝ => fun k => x k / sigma) =
        iidSequenceLaw νunit := by
    simpa [νunit] using
      iidSequenceLaw_map_coordinatewise ν (fun x => x / sigma)
        (measurable_id.div_const sigma)
  have hball : IsOpen (Metric.ball (Skorokhod.linearPath slope) radius) :=
    Metric.isOpen_ball
  have hpathScale {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ) :
      RandomWalk.normalizedStepCadlagPathIcc (fun _ => Real.sqrt n) n
          (fun k => increment k / sigma) =
        RandomWalk.normalizedStepCadlagPathIcc
          (fun _ => sigma * Real.sqrt n) n increment := by
    ext t
    exact RandomWalk.normalizedStepPath_div_const_eq hn hsigma increment t
  have hmeasureEq (n : ℕ) (hn : 0 < n) :
      iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} =
        iidSequenceLaw νunit
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} := by
    calc
      iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} =
        (iidSequenceLaw ν).map (fun x : ℕ → ℝ => fun k => x k / sigma)
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} := by
          have hset : MeasurableSet
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc
                    (fun _ => Real.sqrt n) n increment ∈
                  Metric.ball (Skorokhod.linearPath slope) radius} :=
            hball.measurableSet.preimage
              (RandomWalk.measurable_normalizedStepCadlagPathIcc
                (fun _ => Real.sqrt n) n)
          rw [Measure.map_apply hcoordinate hset]
          congr 1
          ext increment
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          rw [← hpathScale hn increment]
      _ = iidSequenceLaw νunit
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} := by
          rw [hcoordinateLaw]
  refine ⟨q, hqpos, ?_⟩
  filter_upwards [hqevent, Filter.eventually_gt_atTop 0] with n hqn hn
  rw [hmeasureEq n hn]
  exact hqn

/-- A finite subcover of a compact slope interval upgrades fixed-slope
Donsker lower bounds to one positive lower bound uniform over that interval.
Each center uses a ball of half the target radius; nearby linear centers are
within the remaining half-radius in the `J₁` metric. -/
theorem eventually_measure_normalizedStep_linearBall_pos_on_Icc
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P)
    (bound radius : ℝ) (hbound : 0 < bound) (hradius : 0 < radius) :
    ∃ q : ENNReal, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ slope ∈ Set.Icc (-bound) bound,
      q < iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun n => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} := by
  let Slope := {slope : ℝ // slope ∈ Set.Icc (-bound) bound}
  let neighborhood : Slope → Set ℝ := fun center =>
    Set.Ioo (center.1 - radius / 2) (center.1 + radius / 2)
  have hopen (center : Slope) : IsOpen (neighborhood center) := isOpen_Ioo
  have hcover' : Set.Icc (-bound) bound ⊆
      ⋃ center : Slope, neighborhood center := by
    intro slope hslope
    refine Set.mem_iUnion.mpr ⟨⟨slope, hslope⟩, ?_⟩
    change slope - radius / 2 < slope ∧ slope < slope + radius / 2
    constructor <;> linarith
  obtain ⟨centers, hcenters⟩ :=
    isCompact_Icc.elim_finite_subcover neighborhood hopen hcover'
  have hcentersNonempty : centers.Nonempty := by
    have hzero : (0 : ℝ) ∈ Set.Icc (-bound) bound := by
      constructor <;> linarith
    have hzeroCover := hcenters hzero
    rcases Set.mem_iUnion.mp hzeroCover with ⟨center, hcenterCover⟩
    rcases Set.mem_iUnion.mp hcenterCover with ⟨hcenter, _⟩
    exact ⟨center, hcenter⟩
  have hradiusHalf : 0 < radius / 2 := by linarith
  have hfixed (center : Slope) : ∃ q : ENNReal, 0 < q ∧
      ∀ᶠ n : ℕ in atTop,
        q < iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun n => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath center.1) (radius / 2)} := by
    exact eventually_measure_normalizedStep_linearBall_pos hν hP
      center.1 (radius / 2) hradiusHalf
  let centerBound : Slope → ℝ≥0∞ := fun center => Classical.choose (hfixed center)
  have hcenterBoundPos (center : Slope) : 0 < centerBound center :=
    (Classical.choose_spec (hfixed center)).1
  have hcenterBoundEvent (center : Slope) :
      ∀ᶠ n : ℕ in atTop,
        centerBound center < iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun n => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath center.1) (radius / 2)} :=
    (Classical.choose_spec (hfixed center)).2
  let bounds := centers.image centerBound
  have hboundsNonempty : bounds.Nonempty := by
    rcases hcentersNonempty with ⟨center, hcenter⟩
    exact ⟨centerBound center,
      Finset.mem_image.mpr ⟨center, hcenter, rfl⟩⟩
  let q := bounds.min' hboundsNonempty
  have hqpos : 0 < q := by
    obtain ⟨center, hcenter, hqEq⟩ :=
      Finset.mem_image.mp (Finset.min'_mem bounds hboundsNonempty)
    change 0 < bounds.min' hboundsNonempty
    rw [← hqEq]
    exact hcenterBoundPos center
  have hqle (center : Slope) (hcenter : center ∈ centers) :
      q ≤ centerBound center :=
    Finset.min'_le bounds (centerBound center)
      (Finset.mem_image.mpr ⟨center, hcenter, rfl⟩)
  have hcommon : ∀ᶠ n : ℕ in atTop,
      ∀ center ∈ centers,
        centerBound center < iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun n => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath center.1) (radius / 2)} := by
    apply centers.eventually_all.2
    intro center hcenter
    exact hcenterBoundEvent center
  refine ⟨q, hqpos, ?_⟩
  filter_upwards [hcommon] with n hn
  intro slope hslope
  have hslopeCover := hcenters hslope
  rcases Set.mem_iUnion.mp hslopeCover with ⟨center, hslopeCover⟩
  rcases Set.mem_iUnion.mp hslopeCover with ⟨hcenter, hslopeCenter⟩
  have hclose : |slope - center.1| < radius / 2 := by
    have hinterval := Set.mem_Ioo.mp hslopeCenter
    rw [abs_lt]
    constructor <;> linarith
  have hballSubset :
      Metric.ball (Skorokhod.linearPath center.1) (radius / 2) ⊆
        Metric.ball (Skorokhod.linearPath slope) radius := by
    intro path hpath
    rw [Metric.mem_ball] at hpath ⊢
    have hcenter :
        dist (Skorokhod.linearPath center.1)
          (Skorokhod.linearPath slope) < radius / 2 := by
      calc
        dist (Skorokhod.linearPath center.1)
            (Skorokhod.linearPath slope) ≤ |center.1 - slope| :=
          Skorokhod.dist_linearPath_le _ _
        _ = |slope - center.1| := by rw [abs_sub_comm]
        _ < radius / 2 := hclose
    calc
      dist path (Skorokhod.linearPath slope) ≤
          dist path (Skorokhod.linearPath center.1) +
            dist (Skorokhod.linearPath center.1)
              (Skorokhod.linearPath slope) := dist_triangle _ _ _
      _ < radius / 2 + radius / 2 := add_lt_add hpath hcenter
      _ = radius := by ring
  have hmeasure : iidSequenceLaw ν
      {increment | RandomWalk.normalizedStepCadlagPathIcc
        (fun n => Real.sqrt n) n increment ∈
          Metric.ball (Skorokhod.linearPath center.1) (radius / 2)} ≤
      iidSequenceLaw ν
        {increment | RandomWalk.normalizedStepCadlagPathIcc
          (fun n => Real.sqrt n) n increment ∈
            Metric.ball (Skorokhod.linearPath slope) radius} :=
    measure_mono (by
      intro increment hincrement
      exact hballSubset hincrement)
  calc
    q ≤ centerBound center := hqle center hcenter
    _ < iidSequenceLaw ν
        {increment | RandomWalk.normalizedStepCadlagPathIcc
          (fun n => Real.sqrt n) n increment ∈
            Metric.ball (Skorokhod.linearPath center.1) (radius / 2)} := hn center hcenter
    _ ≤ iidSequenceLaw ν
        {increment | RandomWalk.normalizedStepCadlagPathIcc
          (fun n => Real.sqrt n) n increment ∈
            Metric.ball (Skorokhod.linearPath slope) radius} := hmeasure

/-- The finite-net linear-ball estimate also holds uniformly on an arbitrary
compact slope interval for a centered source with variance `sigma²`. It is the
unit-variance finite-net theorem transported through coordinatewise division
by `sigma`; in particular the source slopes are unchanged. -/
theorem eventually_measure_normalizedStep_linearBall_pos_on_Icc_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P)
    (bound radius : ℝ) (hbound : 0 < bound) (hradius : 0 < radius) :
    ∃ q : ENNReal, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ slope ∈ Set.Icc (-bound) bound,
        q < iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} := by
  let νunit := ν.map (fun x => x / sigma)
  have hνunit : IsCenteredUnitSecondMoment νunit := hν.map_div hsigma
  obtain ⟨q, hqpos, hqevent⟩ :=
    eventually_measure_normalizedStep_linearBall_pos_on_Icc
      hνunit hP bound radius hbound hradius
  have hcoordinate : Measurable (fun x : ℕ → ℝ => fun k => x k / sigma) := by
    exact Measurable.of_eval fun k => by
      exact (measurable_id.div_const sigma).comp (measurable_pi_apply k)
  have hcoordinateLaw :
      (iidSequenceLaw ν).map (fun x : ℕ → ℝ => fun k => x k / sigma) =
        iidSequenceLaw νunit := by
    simpa [νunit] using
      iidSequenceLaw_map_coordinatewise ν (fun x => x / sigma)
        (measurable_id.div_const sigma)
  have hball (slope : ℝ) :
      IsOpen (Metric.ball (Skorokhod.linearPath slope) radius) :=
    Metric.isOpen_ball
  have hmeasureEq (n : ℕ) (hn : 0 < n) (slope : ℝ) :
      iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} =
        iidSequenceLaw νunit
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} := by
    have hpathScale {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ) :
        RandomWalk.normalizedStepCadlagPathIcc (fun _ => Real.sqrt n) n
            (fun k => increment k / sigma) =
          RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment := by
      ext t
      exact RandomWalk.normalizedStepPath_div_const_eq hn hsigma increment t
    calc
      iidSequenceLaw ν
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} =
        (iidSequenceLaw ν).map (fun x : ℕ → ℝ => fun k => x k / sigma)
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} := by
          have hset : MeasurableSet
              {increment : ℕ → ℝ |
                RandomWalk.normalizedStepCadlagPathIcc
                    (fun _ => Real.sqrt n) n increment ∈
                  Metric.ball (Skorokhod.linearPath slope) radius} :=
            (hball slope).measurableSet.preimage
              (RandomWalk.measurable_normalizedStepCadlagPathIcc
                (fun _ => Real.sqrt n) n)
          rw [Measure.map_apply hcoordinate hset]
          congr 1
          ext increment
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          rw [← hpathScale hn increment]
      _ = iidSequenceLaw νunit
          {increment | RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => Real.sqrt n) n increment ∈
              Metric.ball (Skorokhod.linearPath slope) radius} := by
          rw [hcoordinateLaw]
  refine ⟨q, hqpos, ?_⟩
  filter_upwards [hqevent, Filter.eventually_gt_atTop 0] with n hqn hn
  intro slope hslope
  rw [hmeasureEq n hn slope]
  exact hqn slope hslope


end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
