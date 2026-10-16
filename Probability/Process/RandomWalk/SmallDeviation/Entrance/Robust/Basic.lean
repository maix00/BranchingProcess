/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.MovingInterior

/-!
# Robust endpoint of a diffusive entrance

Write $S_j=\sum_{i=0}^{j-1}\xi_i$ for the partial sums of the increments,
$h_j=cj/\Delta^2$ for the moving-boundary displacement, and $x$ for the
starting point. The public declarations in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.robustMovingTransitionEvent`:
  $\mathcal R_{n,\Delta,c}(x)=\{\xi:h_j\le x+S_j\le\Delta+h_j\ (1\le j\le n),\
  x+S_n\in[h_n+2\Delta/5,h_n+3\Delta/5]\}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.robustMovingTransitionEvent_subset_movingTransitionEvent`:
  $\mathcal R_{n,\Delta,c}(x)\subseteq\mathcal A_{n,\Delta,c}(x)$, where
  $\mathcal A_{n,\Delta,c}(x)$ has the same path bounds and terminal interval
  $[h_n+\Delta/3,h_n+2\Delta/3]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measurableSet_robustMovingTransitionEvent`:
  membership in $\mathcal R_{n,\Delta,c}(x)$ depends only on
  $\xi_0,\ldots,\xi_{n-1}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteInteriorEvent_subset_robustMovingTransitionEvent`:
  if $\Delta>0$, $c\ge0$, $n\le\Delta^2$, and $60c\le\Delta$, then
  $\mathcal I_{n,\Delta,c}(x)\subseteq\mathcal R_{n,\Delta,c}(x)$, where
  $\mathcal I_{n,\Delta,c}(x)=\{\xi:c\le x+S_j\le\Delta\ (1\le j\le n),\
  x+S_n\in[5\Delta/12,7\Delta/12]\}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.eventually_middleRobustTransitionProbability_pos`:
  if $\Delta_n\to\infty$, $c\ge0$, and the centered increment law has
  variance $\sigma^2>0$, then some $q>0$ satisfies
  $(\operatorname{iidSequenceLaw}\,\nu)(\mathcal R_{\lfloor\Delta_n^2\rfloor,
  \Delta_n,c}(x))\ge q$ eventually, uniformly for
  $x\in[\Delta_n/12,11\Delta_n/12]$.

The middle-start and two edge constructions are those in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Appendix A.2, Lemma A.7, used in
Chapter 3, Lemma 3.5. This module uses a narrower terminal interval to supply
the first horizontal staircase block in that proof.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The entrance corridor with the smaller terminal window needed for the
first horizontal staircase block. -/
def robustMovingTransitionEvent (n : ℕ) (width drift start : ℝ) :
    Set (ℕ → ℝ) :=
  movingTransitionEvent n width drift start ∩
    {increment |
      drift * (n : ℝ) / width ^ 2 + 2 * width / 5 ≤
        start + AdditivePath.displacement n increment ∧
      start + AdditivePath.displacement n increment ≤
        drift * (n : ℝ) / width ^ 2 + 3 * width / 5}

/-- The robust entrance event retains all moving-corridor constraints. -/
theorem robustMovingTransitionEvent_subset_movingTransitionEvent
    (n : ℕ) (width drift start : ℝ) :
    robustMovingTransitionEvent n width drift start ⊆
      movingTransitionEvent n width drift start := by
  exact Set.inter_subset_left

private lemma displacement_measurable_prefix
    (n j : ℕ) (hj : j ≤ n) :
    Measurable[sequencePrefixFiltration (E := ℝ) n]
      (AdditivePath.displacement j) := by
  unfold AdditivePath.displacement
  apply Finset.measurable_sum
  intro k hk
  exact sequenceCoordinate_measurable n
    ⟨k, (Finset.mem_range.mp hk).trans_le hj⟩

/-- All constraints of the robust event depend only on the first `n`
increments. -/
theorem measurableSet_robustMovingTransitionEvent
    (n : ℕ) (width drift start : ℝ) :
    MeasurableSet[sequencePrefixFiltration (E := ℝ) n]
      (robustMovingTransitionEvent n width drift start) := by
  have hpath : MeasurableSet[sequencePrefixFiltration (E := ℝ) n]
      {increment : ℕ → ℝ |
        ∀ k : Fin n,
          drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 ≤
            start + AdditivePath.displacement (k + 1) increment ∧
          start + AdditivePath.displacement (k + 1) increment ≤
            width + drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2} := by
    rw [← Set.iInter_ofPred]
    apply MeasurableSet.iInter
    intro k
    have hposition : Measurable[sequencePrefixFiltration (E := ℝ) n]
        (fun increment : ℕ → ℝ =>
          start + AdditivePath.displacement (k + 1) increment) :=
      measurable_const.add
        (displacement_measurable_prefix n (k + 1) k.isLt)
    exact (measurableSet_Ici.preimage hposition).inter
      (measurableSet_Iic.preimage hposition)
  have hend : MeasurableSet[sequencePrefixFiltration (E := ℝ) n]
      {increment : ℕ → ℝ |
        drift * (n : ℝ) / width ^ 2 + width / 3 ≤
          start + AdditivePath.displacement n increment ∧
        start + AdditivePath.displacement n increment ≤
          drift * (n : ℝ) / width ^ 2 + 2 * width / 3} := by
    have hposition : Measurable[sequencePrefixFiltration (E := ℝ) n]
        (fun increment : ℕ → ℝ =>
          start + AdditivePath.displacement n increment) :=
      measurable_const.add (displacement_measurable_prefix n n le_rfl)
    exact (measurableSet_Ici.preimage hposition).inter
      (measurableSet_Iic.preimage hposition)
  have hrobust : MeasurableSet[sequencePrefixFiltration (E := ℝ) n]
      {increment : ℕ → ℝ |
        drift * (n : ℝ) / width ^ 2 + 2 * width / 5 ≤
          start + AdditivePath.displacement n increment ∧
        start + AdditivePath.displacement n increment ≤
          drift * (n : ℝ) / width ^ 2 + 3 * width / 5} := by
    have hposition : Measurable[sequencePrefixFiltration (E := ℝ) n]
        (fun increment : ℕ → ℝ =>
          start + AdditivePath.displacement n increment) :=
      measurable_const.add (displacement_measurable_prefix n n le_rfl)
    exact (measurableSet_Ici.preimage hposition).inter
      (measurableSet_Iic.preimage hposition)
  simpa only [robustMovingTransitionEvent, movingTransitionEvent,
    Set.ofPred_and] using (hpath.inter hend).inter hrobust

/-- The Brownian interior-corridor event fits the stronger endpoint window
when the drift over the diffusive entrance is small compared with its width. -/
theorem finiteInteriorEvent_subset_robustMovingTransitionEvent
    {n : ℕ} {width drift start : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hn : (n : ℝ) ≤ width ^ 2)
    (hlarge : 60 * drift ≤ width) :
    FunctionalLimit.Donsker.Entrance.finiteInteriorEvent n width drift start ⊆
      robustMovingTransitionEvent n width drift start := by
  intro increment hinc
  have hlargeOld : 12 * drift ≤ width := by nlinarith [hlarge, hdrift]
  have hmove := finiteInteriorEvent_subset_movingTransitionEvent
    hwidth hdrift hn hlargeOld hinc
  have hsq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  have hshift : drift * (n : ℝ) / width ^ 2 ≤ drift := by
    exact (div_le_iff₀ hsq).2
      (mul_le_mul_of_nonneg_left hn hdrift)
  have hshiftNonneg : 0 ≤ drift * (n : ℝ) / width ^ 2 := by positivity
  refine ⟨hmove, ?_⟩
  exact ⟨by nlinarith [hinc.2.1, hshift, hlarge],
    by nlinarith [hinc.2.2, hshiftNonneg, hwidth]⟩

/-- Middle starting points reach the robust window with probability
bounded below uniformly at sufficiently large diffusive widths. -/
theorem eventually_middleRobustTransitionProbability_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {drift : ℝ} (hdrift : 0 ≤ drift) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc (width n / 12) (11 / 12 * width n),
        q ≤ iidSequenceLaw ν
          (robustMovingTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
            (width n) drift start) := by
  obtain ⟨q, hq, hmiddle⟩ :=
    FunctionalLimit.Donsker.Entrance.eventually_diffusiveInteriorProbability_pos_uniform_of_centeredSecondMoment
      hν hsigma hwidth drift
  refine ⟨q, hq, ?_⟩
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hwidthLarge : ∀ᶠ n : ℕ in atTop, 60 * drift ≤ width n := by
    filter_upwards [hwidth.eventually
      (eventually_ge_atTop (60 * drift))] with n hn
    exact hn
  filter_upwards [hmiddle, hwidthPos, hwidthLarge] with n hn hw hl
  intro start hs
  have hfloor :
      ((Asymptotics.floorBlockLength (fun k => width k ^ 2) n : ℕ) : ℝ) ≤
        width n ^ 2 := Nat.floor_le (sq_nonneg _)
  exact (hn start hs).trans (measure_mono
    (finiteInteriorEvent_subset_robustMovingTransitionEvent
      hw hdrift hfloor hl))

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
