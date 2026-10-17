/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.DescendingLocalTime
public import Probability.Sequence.IID.Basic

/-!
# Descending ladder-height renewal function

The public definitions and theorems in this file are:

- ProbabilityTheory.RandomWalk.strictDescendingLadderHeight:
  $H_k^-=-S_{T_k^-}$ if $T_k^-<\infty$, and infinity otherwise.
- ProbabilityTheory.RandomWalk.measurableSet_strictDescendingLadderHeight_le:
  the finite descending ladder-height event $\{H_k^-\le x\}$ is measurable.
- ProbabilityTheory.RandomWalk.strictDescendingLadderHeight_measurable:
  $H_k^-:\mathbb R^{\mathbb N}\to\mathbb R\cup\{\infty\}$ is measurable.
- ProbabilityTheory.RandomWalk.strictDescendingLadderHeight_zero:
  $H_0^-=0$.
- ProbabilityTheory.RandomWalk.strictDescendingLadderHeight_nonneg:
  $H_k^-\ge0$ in $\mathbb R\cup\{\infty\}$.
- ProbabilityTheory.RandomWalk.strictDescendingLadderHeight_mono:
  $k\le l$ implies $H_k^-\le H_l^-$.
- ProbabilityTheory.RandomWalk.descendingLadderRenewalFunction:
  $V_\nu(x)=\sum_{k\ge0}\mathbb P_\nu(H_k^-\le x)$.
- ProbabilityTheory.RandomWalk.descendingLadderRenewalFunction_eq_lintegral_count:
  $V_\nu(x)=\mathbb E_\nu[\sum_{k\ge0}1_{\{H_k^-\le x\}}]$.
- ProbabilityTheory.RandomWalk.descendingLadderRenewalFunction_mono:
  $x\le y$ implies $V_\nu(x)\le V_\nu(y)$.
- ProbabilityTheory.RandomWalk.descendingLadderRenewalFunction_measurable:
  $x\mapsto V_\nu(x)$ is Borel measurable.
- ProbabilityTheory.RandomWalk.one_le_descendingLadderRenewalFunction:
  $V_\nu(x)\ge1$ for $x\ge0$.
- ProbabilityTheory.RandomWalk.descendingLadderRenewalFunction_eq_zero_of_neg:
  $V_\nu(x)=0$ for $x<0$.

The renewal function is the one used by Francesco Caravenna and Loïc
Chaumont, *Invariance principles for random walks conditioned to stay
positive*, definition (1.1) and Lemma 2.1, DOI 10.1214/07-AIHP119.
L. Chaumont and R. A. Doney, *Invariance principles for local times at the
maximum of random walks and Lévy processes*, Ann. Probab. 38(4) (2010),
1368--1389, Lemma 5, DOI 10.1214/09-AOP512, use the analogous renewal
function for the descending ladder process.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

/-- Magnitude of the height at a strict descending ladder time. -/
noncomputable def strictDescendingLadderHeight
    (increment : ℕ → ℝ) (k : ℕ) : WithTop ℝ :=
  strictAscendingLadderHeight (fun i => -increment i) k

/-- The descending ladder-height event is measurable; it is the reflected
ascending ladder-height event. -/
theorem measurableSet_strictDescendingLadderHeight_le
    (k : ℕ) (x : ℝ) :
    MeasurableSet
      {increment : ℕ → ℝ |
        strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)} := by
  have hneg : Measurable (fun increment : ℕ → ℝ =>
      fun i => -increment i) := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).neg
  simpa [strictDescendingLadderHeight, Set.preimage_ofPred_eq] using
    (measurableSet_strictAscendingLadderHeight_le k x).preimage hneg

/-- The extended-real descending ladder height is measurable. -/
theorem strictDescendingLadderHeight_measurable (k : ℕ) :
    Measurable (fun increment : ℕ → ℝ =>
      strictDescendingLadderHeight increment k) := by
  have hneg : Measurable (fun increment : ℕ → ℝ =>
      fun i => -increment i) := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).neg
  exact (strictAscendingLadderHeight_measurable k).comp hneg

/-- The zeroth descending ladder height is the initial height zero. -/
theorem strictDescendingLadderHeight_zero (increment : ℕ → ℝ) :
    strictDescendingLadderHeight increment 0 = 0 :=
  strictAscendingLadderHeight_zero (fun i => -increment i)

/-- Descending ladder heights are the ascending ladder heights of the
reflected walk and hence are nonnegative. -/
theorem strictDescendingLadderHeight_nonneg
    (increment : ℕ → ℝ) (k : ℕ) :
    (0 : WithTop ℝ) ≤ strictDescendingLadderHeight increment k :=
  strictAscendingLadderHeight_nonneg (fun i => -increment i) k

/-- Strict descending ladder heights increase with the ladder index. -/
theorem strictDescendingLadderHeight_mono
    (increment : ℕ → ℝ) :
    Monotone (strictDescendingLadderHeight increment) :=
  strictAscendingLadderHeight_mono (fun i => -increment i)

/-- The renewal mass accumulated by the descending ladder heights up
to x under an i.i.d. increment law. -/
noncomputable def descendingLadderRenewalFunction
    (ν : Measure ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, iidSequenceLaw ν
    {increment | strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)}

/-- The renewal function is the expected number of descending ladder
heights in the interval from zero to `x`, as in Caravenna--Chaumont,
definition (1.1). -/
theorem descendingLadderRenewalFunction_eq_lintegral_count
    (ν : Measure ℝ) (x : ℝ) :
    descendingLadderRenewalFunction ν x =
      ∫⁻ increment, ∑' k : ℕ,
        if strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)
        then (1 : ℝ≥0∞) else 0 ∂iidSequenceLaw ν := by
  unfold descendingLadderRenewalFunction
  have hmeas (k : ℕ) : MeasurableSet
      {increment : ℕ → ℝ |
        strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)} :=
    measurableSet_strictDescendingLadderHeight_le k x
  have hind (k : ℕ) :
      (fun increment : ℕ → ℝ =>
        if strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)
        then (1 : ℝ≥0∞) else 0) =
      {increment | strictDescendingLadderHeight increment k ≤
        (x : WithTop ℝ)}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext increment
    simp [Set.indicator]
  have hterm (k : ℕ) :
      iidSequenceLaw ν
        {increment | strictDescendingLadderHeight increment k ≤
          (x : WithTop ℝ)} =
      ∫⁻ increment,
        (if strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)
         then (1 : ℝ≥0∞) else 0) ∂iidSequenceLaw ν := by
    rw [hind k, lintegral_indicator_const₀ (hmeas k).nullMeasurableSet,
      one_mul]
  calc
    (∑' k : ℕ, iidSequenceLaw ν
      {increment | strictDescendingLadderHeight increment k ≤
        (x : WithTop ℝ)}) =
        ∑' k : ℕ, ∫⁻ increment,
          (if strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)
           then (1 : ℝ≥0∞) else 0) ∂iidSequenceLaw ν := by
      apply tsum_congr
      exact hterm
    _ = ∫⁻ increment, ∑' k : ℕ,
          (if strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)
           then (1 : ℝ≥0∞) else 0) ∂iidSequenceLaw ν := by
      rw [lintegral_tsum]
      intro k
      rw [hind k]
      exact (aemeasurable_const).indicator₀
        (hmeas k).nullMeasurableSet

/-- Larger height windows contain all the previous renewal mass. -/
theorem descendingLadderRenewalFunction_mono
    (ν : Measure ℝ) : Monotone (descendingLadderRenewalFunction ν) := by
  intro x y hxy
  unfold descendingLadderRenewalFunction
  apply ENNReal.tsum_le_tsum
  intro k
  apply measure_mono
  intro increment hin
  exact hin.trans (WithTop.coe_le_coe.mpr hxy)

/-- The monotone descending ladder-height renewal function is Borel
measurable in its height argument. -/
theorem descendingLadderRenewalFunction_measurable
    (ν : Measure ℝ) :
    Measurable (descendingLadderRenewalFunction ν) :=
  (descendingLadderRenewalFunction_mono ν).measurable

/-- The zeroth descending ladder level contributes one unit of renewal
mass on every nonnegative height interval. -/
theorem one_le_descendingLadderRenewalFunction
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ descendingLadderRenewalFunction ν x := by
  have hzero :
      {increment : ℕ → ℝ |
        strictDescendingLadderHeight increment 0 ≤ (x : WithTop ℝ)} =
      Set.univ := by
    ext increment
    simp [strictDescendingLadderHeight_zero, hx]
  calc
    (1 : ℝ≥0∞) = iidSequenceLaw ν
        {increment | strictDescendingLadderHeight increment 0 ≤
          (x : WithTop ℝ)} := by rw [hzero]; simp
    _ ≤ descendingLadderRenewalFunction ν x := by
      unfold descendingLadderRenewalFunction
      exact ENNReal.le_tsum
        (f := fun k : ℕ => iidSequenceLaw ν
          {increment | strictDescendingLadderHeight increment k ≤
            (x : WithTop ℝ)}) 0

/-- No descending ladder height falls below the initial height zero. -/
theorem descendingLadderRenewalFunction_eq_zero_of_neg
    (ν : Measure ℝ) {x : ℝ} (hx : x < 0) :
    descendingLadderRenewalFunction ν x = 0 := by
  unfold descendingLadderRenewalFunction
  have hempty (k : ℕ) :
      {increment : ℕ → ℝ |
        strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)} =
      ∅ := by
    ext increment
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hheight
    have hnonneg := strictDescendingLadderHeight_nonneg increment k
    exact (not_le_of_gt (WithTop.coe_lt_coe.mpr hx))
      (hnonneg.trans hheight)
  simp [hempty]

end ProbabilityTheory.RandomWalk

end
