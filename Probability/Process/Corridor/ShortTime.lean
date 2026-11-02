/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import MeasureTheory.Measure.EventLimits
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing
public import Probability.Process.Path.Skorokhod.Corridor.RationalCoordinate
public import Topology.Cadlag.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Short-time corridors for càdlàg processes

## Public declarations

- `ProbabilityTheory.rationalInitialCorridorEvent X T a b` is
  \(\{\omega\mid\forall q\in\mathbb Q\cap[0,1],\;
  a<X(Tq,\omega)-X(0,\omega)<b\}\).
- `ProbabilityTheory.rationalInitialCorridorEvent_inter_positive_subset_return`:
  \(A_{T,-\delta,\delta}\cap\{X(T)-X(0)>0\}\subseteq
  R_{T,-\delta,\delta;0,c}\) whenever \(\delta\le c\).
- `ProbabilityTheory.rationalInitialCorridorEvent_inter_negative_subset_return`:
  \(A_{T,-\delta,\delta}\cap\{X(T)-X(0)<0\}\subseteq
  R_{T,-\delta,\delta;c,0}\) whenever \(c\le-\delta\).
- `ProbabilityTheory.nullMeasurableSet_rationalInitialCorridorEvent`:
  the event is null-measurable under \(P\) if every coordinate \(X_t\) is
  \(P\)-almost-everywhere measurable.
- `ProbabilityTheory.tendsto_measure_rationalInitialCorridorEvent`: for an
  if \(X\) is almost surely càdlàg and \(T_n\to0\), then for each
  \(\delta>0\),
  \(P(\forall q\in\mathbb Q\cap[0,1],\;
  |X(T_nq)-X(0)|<\delta)\to1\).

Here \(A_{T,a,b}\) denotes the rational-time corridor event in the first
declaration, and \(R_{T,a,b;c,d}\) denotes the corresponding corridor-return
event with terminal interval \([c,d]\).

Almost-sure right continuity at the starting time makes every fixed centered
spatial corridor overwhelmingly likely as its time horizon shrinks to zero.
Coordinate random variables only need to be almost-everywhere measurable.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

private theorem exists_initial_interval_subset_Ioo
    {f : ℝ≥0 → ℝ} (hf : IsCadlag f) {lower upper : ℝ}
    (hlower : lower < f 0) (hupper : f 0 < upper) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t ≤ δ → f t ∈ Set.Ioo lower upper := by
  have hcont : ContinuousAt f 0 := by
    have h := hf.isRightContinuous 0
    rw [continuousWithinAt_Ioi_iff_Ici] at h
    simpa [continuousWithinAt_univ] using h
  have hnear : {t : ℝ≥0 | f t ∈ Set.Ioo lower upper} ∈ 𝓝 (0 : ℝ≥0) :=
    hcont.eventually (isOpen_Ioo.mem_nhds ⟨hlower, hupper⟩)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ≥0 := ⟨r / 2, by positivity⟩
  refine ⟨δ, by exact_mod_cast half_pos hr, ?_⟩
  intro t ht
  apply hball
  rw [Metric.mem_ball, NNReal.dist_eq]
  have ht' : (t : ℝ) ≤ r / 2 := by exact_mod_cast ht
  simpa [abs_of_nonneg t.property] using (show (t : ℝ) < r by linarith)

private theorem eventually_initial_interval_subset_Ioo
    {f : ℝ≥0 → ℝ} (hf : IsCadlag f)
    {horizon : ℕ → ℝ≥0} (hhorizon : Filter.Tendsto horizon Filter.atTop (𝓝 0))
    {lower upper : ℝ} (hlower : lower < f 0) (hupper : f 0 < upper) :
    ∀ᶠ n in Filter.atTop, ∀ t : ℝ≥0, t ≤ horizon n →
      f t ∈ Set.Ioo lower upper := by
  obtain ⟨δ, hδ, hpath⟩ := exists_initial_interval_subset_Ioo hf hlower hupper
  have hnear : Set.Iio δ ∈ 𝓝 (0 : ℝ≥0) :=
    isOpen_Iio.mem_nhds hδ
  filter_upwards [hhorizon.eventually hnear] with n hn t ht
  exact hpath t (le_of_lt (lt_of_le_of_lt ht hn))

def rationalInitialCorridorEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (horizon : ℝ≥0) (lower upper : ℝ) : Set Ω :=
  (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
    rationalCoordinateCorridor lower upper

theorem rationalInitialCorridorEvent_inter_positive_subset_return
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (horizon : ℝ≥0)
    (δ coreUpper : ℝ) (hcore : δ ≤ coreUpper) :
    rationalInitialCorridorEvent X horizon (-δ) δ ∩
        {ω | 0 < X horizon ω - X 0 ω} ⊆
      (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper := by
  intro ω hω
  refine ⟨hω.1, ?_, ?_⟩
  · simpa [RationalCoordinate.toNNReal_top] using hω.2
  · have htop := Set.mem_iInter.mp hω.1 ⊤
    change -δ < X (horizon * RationalCoordinate.toNNReal ⊤) ω - X 0 ω ∧
      X (horizon * RationalCoordinate.toNNReal ⊤) ω - X 0 ω < δ at htop
    simpa [RationalCoordinate.toNNReal_top] using lt_of_lt_of_le htop.2 hcore

theorem rationalInitialCorridorEvent_inter_negative_subset_return
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (horizon : ℝ≥0)
    (δ coreLower : ℝ) (hcore : coreLower ≤ -δ) :
    rationalInitialCorridorEvent X horizon (-δ) δ ∩
        {ω | X horizon ω - X 0 ω < 0} ⊆
      (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ) δ coreLower 0 := by
  intro ω hω
  refine ⟨hω.1, ?_, ?_⟩
  · have htop := Set.mem_iInter.mp hω.1 ⊤
    change -δ < X (horizon * RationalCoordinate.toNNReal ⊤) ω - X 0 ω ∧
      X (horizon * RationalCoordinate.toNNReal ⊤) ω - X 0 ω < δ at htop
    simpa [RationalCoordinate.toNNReal_top] using lt_of_le_of_lt hcore htop.1
  · simpa [RationalCoordinate.toNNReal_top] using hω.2

theorem nullMeasurableSet_rationalInitialCorridorEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (horizon : ℝ≥0) (lower upper : ℝ) :
    NullMeasurableSet (rationalInitialCorridorEvent X horizon lower upper) P := by
  have hmap : AEMeasurable
      (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) P := by
    rw [aemeasurable_pi_iff]
    intro q
    exact (hX _).sub (hX 0)
  exact hmap.nullMeasurableSet_preimage
    (measurableSet_rationalCoordinateCorridor lower upper)

/-- Centered rational-time increment corridors of fixed positive width have probability tending to one as the
time horizon tends to zero. -/
theorem tendsto_measure_rationalInitialCorridorEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
    {horizon : ℕ → ℝ≥0} (hhorizon : Tendsto horizon atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => P (rationalInitialCorridorEvent X (horizon n) (-δ) δ))
      atTop (𝓝 1) := by
  let A : ℕ → Set Ω := fun n => rationalInitialCorridorEvent X (horizon n) (-δ) δ
  have hA : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    exact nullMeasurableSet_rationalInitialCorridorEvent P X hX _ _ _
  have hnear : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n := by
    filter_upwards [hcadlag] with ω hω
    have hlocal := eventually_initial_interval_subset_Ioo hω hhorizon
      (show X 0 ω - δ < X 0 ω by linarith)
      (show X 0 ω < X 0 ω + δ by linarith)
    filter_upwards [hlocal] with n hn
    change (fun q => X (horizon n * RationalCoordinate.toNNReal q) ω - X 0 ω) ∈
      rationalCoordinateCorridor (-δ) δ
    simp only [rationalCoordinateCorridor, Set.mem_iInter,
      Set.mem_ofPred_eq, Set.mem_Ioo]
    intro q
    have htime : horizon n * RationalCoordinate.toNNReal q ≤ horizon n := by
      calc
        horizon n * RationalCoordinate.toNNReal q ≤ horizon n * 1 :=
          mul_le_mul_of_nonneg_left (RationalCoordinate.toNNReal_le_one q) (horizon n).property
        _ = horizon n := mul_one _
    have hq := hn _ htime
    constructor <;> linarith [hq.1, hq.2]
  have hnear_iff : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (ω ∈ A n ↔ ω ∈ Set.univ) := by
    filter_upwards [hnear] with ω hω
    filter_upwards [hω] with n hn
    simp [hn]
  simpa [A, measure_univ] using
    tendsto_measure_of_ae_tendsto_indicator_of_nullMeasurableSet
      P atTop A Set.univ hA MeasurableSet.univ.nullMeasurableSet hnear_iff

end ProbabilityTheory
