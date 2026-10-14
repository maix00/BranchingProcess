/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.MovingInterior

/-!
# Robust endpoint of a diffusive entrance

The public object and theorem in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.robustMovingTransitionEvent`:
  the moving entrance event with terminal point in
  $[h_n+2\Delta/5,h_n+3\Delta/5]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.robustMovingTransitionEvent_subset_movingTransitionEvent`:
  this robust event is contained in $\mathcal A_\Delta(x)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measurableSet_robustMovingTransitionEvent`:
  the robust event belongs to the natural increment domain at time $n$.

The middle-start and two edge constructions in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma, have terminal
  intervals within this robust range for sufficiently large $\Delta$;
  their printed endpoint bounds retain fixed-length error terms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

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

private theorem displacement_measurable_prefix
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
