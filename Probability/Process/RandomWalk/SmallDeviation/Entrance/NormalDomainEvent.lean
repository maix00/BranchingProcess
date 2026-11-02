/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Algebra.BigOperators.PartialSum
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Finite normal-domain entrance events

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteNormalizedStepKnots`:
  maps $x\in\mathbb R^n$ to the normalized partial-sum knots
  $j\mapsto scale^{-1}\sum_{i<j}x_i$ for $0\le j\le n$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteMovingEntranceEvent`:
  for \(z_j=\frac{1}{scale}\sum_{i<j}x_i\), the event
  \(\{x:\forall j\le n,\ -u+\mathrm{drift}\,j\le z_j\le
  1-u+\mathrm{drift}\,j,\quad
  \frac13-u+\mathrm{drift}\,n\le z_n\le
  \frac23-u+\mathrm{drift}\,n\}\).
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.mem_finiteMovingEntranceEvent_iff`:
  states exactly the displayed partial-sum membership equivalence.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.measurableSet_finiteMovingEntranceEvent`:
  states that this event belongs to the finite product \(\sigma\)-algebra.

The knot map is the common coordinate representation for these events and
their endpoint bridges. The càdlàg interpolation and its $J_1$-ball encoding
remain internal proof support under `Entrance/Lemmas/Rotation/`.

These events are used in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Appendix A.2, Lemma A.7, used in the proof of Chapter 3, Lemma 3.5.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The normalized partial-sum knots of a finite increment vector. -/
noncomputable abbrev finiteNormalizedStepKnots (scale : ℝ) {n : ℕ}
    (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun j => scale⁻¹ * Fin.partialSum x j

/-- The finite-step entrance event in the original moving corridor. Time is
normalized to `[0,1]`; `drift` is the boundary displacement per step in these
spatial units, and the endpoint window is the central third of the corridor. -/
def finiteMovingEntranceEvent {n : ℕ} (scale drift u : ℝ) :
    Set (Fin n → ℝ) :=
  {x | (∀ j : Fin (n + 1),
      finiteNormalizedStepKnots scale x j ∈
        Set.Icc (-u + drift * (j.val : ℝ))
          (1 - u + drift * (j.val : ℝ))) ∧
    finiteNormalizedStepKnots scale x (Fin.last n) ∈
      Set.Icc (1 / 3 - u + drift * (n : ℝ))
        (2 / 3 - u + drift * (n : ℝ))}

/-- Membership in the finite moving entrance event is exactly the family of
scaled partial-sum inequalities that defines the event. -/
theorem mem_finiteMovingEntranceEvent_iff
    {n : ℕ} (scale drift u : ℝ) (x : Fin n → ℝ) :
    x ∈ finiteMovingEntranceEvent (n := n) scale drift u ↔
      (∀ j : Fin (n + 1),
        scale⁻¹ * Fin.partialSum x j ∈
          Set.Icc (-u + drift * (j.val : ℝ))
            (1 - u + drift * (j.val : ℝ))) ∧
        scale⁻¹ * Fin.partialSum x (Fin.last n) ∈
          Set.Icc (1 / 3 - u + drift * (n : ℝ))
            (2 / 3 - u + drift * (n : ℝ)) := by
  unfold finiteMovingEntranceEvent finiteNormalizedStepKnots
  rfl

/-- The finite entrance event is measurable as a finite conjunction of
interval constraints on partial sums. -/
theorem measurableSet_finiteMovingEntranceEvent
    {n : ℕ} (scale drift u : ℝ) :
    MeasurableSet (finiteMovingEntranceEvent (n := n) scale drift u) := by
  have hpartial (j : Fin (n + 1)) :
      Measurable (fun x : Fin n → ℝ => Fin.partialSum x j) := by
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
        have hsum :
            (fun x : Fin n → ℝ => Fin.partialSum x j.succ) =
              fun x => Fin.partialSum x j.castSucc + x j :=
          funext fun x => Fin.partialSum_succ x j
        rw [hsum]
        exact ih.add (measurable_pi_apply j)
  have hknots (j : Fin (n + 1)) :
      Measurable (fun x : Fin n → ℝ =>
        finiteNormalizedStepKnots scale x j) := by
    dsimp [finiteNormalizedStepKnots]
    exact measurable_const.mul (hpartial j)
  unfold finiteMovingEntranceEvent
  apply MeasurableSet.inter
  · have hEq :
        {x : Fin n → ℝ |
          ∀ j : Fin (n + 1),
            finiteNormalizedStepKnots scale x j ∈
              Set.Icc (-u + drift * (j.val : ℝ))
                (1 - u + drift * (j.val : ℝ))} =
          ⋂ j : Fin (n + 1),
            {x : Fin n → ℝ |
              finiteNormalizedStepKnots scale x j ∈
                Set.Icc (-u + drift * (j.val : ℝ))
                  (1 - u + drift * (j.val : ℝ))} := by
      ext x
      simp
    have hI : MeasurableSet (⋂ j : Fin (n + 1),
        {x : Fin n → ℝ |
          finiteNormalizedStepKnots scale x j ∈
            Set.Icc (-u + drift * (j.val : ℝ))
              (1 - u + drift * (j.val : ℝ))}) :=
      MeasurableSet.iInter fun j => measurableSet_Icc.preimage (hknots j)
    rw [← hEq] at hI
    exact hI
  · exact measurableSet_Icc.preimage (hknots (Fin.last n))

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
