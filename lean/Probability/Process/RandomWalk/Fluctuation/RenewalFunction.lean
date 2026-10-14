/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.DescendingLocalTime
public import Probability.Sequence.IID

/-!
# Descending ladder-height renewal function

The public definitions and theorems in this file are:

- ProbabilityTheory.RandomWalk.strictDescendingLadderHeight:
  $H_k^-=-S_{T_k^-}$ if $T_k^-<\infty$, and infinity otherwise.
- ProbabilityTheory.RandomWalk.measurableSet_strictDescendingLadderHeight_le:
  the finite descending ladder-height event $\{H_k^-\le x\}$ is measurable.
- ProbabilityTheory.RandomWalk.descendingLadderRenewalFunction:
  $V_\nu(x)=\sum_{k\ge0}\mathbb P_\nu(H_k^-\le x)$.
- ProbabilityTheory.RandomWalk.descendingLadderRenewalFunction_mono:
  $x\le y$ implies $V_\nu(x)\le V_\nu(y)$.

The renewal function is the one used by Francesco Caravenna and Loïc
Chaumont, *Invariance principles for random walks conditioned to stay
positive*, definition (1.1) and Lemma 2.1, DOI 10.1214/07-AIHP119.
Chaumont and Doney, *Invariance principles for local times at the maximum
of random walks and Lévy processes*, Lemma 5, use the analogous renewal
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

/-- The renewal mass accumulated by the descending ladder heights up
to x under an i.i.d. increment law. -/
noncomputable def descendingLadderRenewalFunction
    (ν : Measure ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, iidSequenceLaw ν
    {increment | strictDescendingLadderHeight increment k ≤ (x : WithTop ℝ)}

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

end ProbabilityTheory.RandomWalk

end
