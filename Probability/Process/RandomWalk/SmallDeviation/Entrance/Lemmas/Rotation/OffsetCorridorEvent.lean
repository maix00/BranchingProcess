/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomainEvent
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.FinitePath
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.LinearTube

/-!
# Offset-corridor event for the entrance-rotation proof

## Internal proof declarations

The drift-removed event, its equivalence with the public moving entrance
event, and the resulting measurability fact are package-private steps in the
cyclic-rotation proof. The public event and its measurability statement remain
in `Entrance/NormalDomainEvent.lean`.
-/

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The static offset corridor obtained by removing the linear boundary drift
from the normalized finite partial-sum path. -/
def finiteDriftRemovedOffsetCorridorEvent (scale drift u : ℝ) {n : ℕ} :
    Set (Fin n → ℝ) :=
  {x | offsetCorridorPath u
    (Fin.removeLinearDrift drift (finiteNormalizedStepKnots scale x))}

/-- Removing the linear boundary drift identifies this static corridor with
the public moving entrance event, including its central endpoint window. -/
lemma finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent
    {n : ℕ} (scale drift u : ℝ) (x : Fin n → ℝ) :
    x ∈ finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u ↔
      x ∈ finiteMovingEntranceEvent (n := n) scale drift u := by
  have hmain : x ∈ finiteMovingEntranceEvent (n := n) scale drift u ↔
      (∀ j : Fin (n + 1),
        finiteNormalizedStepKnots scale x j ∈
          Set.Icc (-u + drift * (j.val : ℝ))
            (1 - u + drift * (j.val : ℝ))) ∧
        finiteNormalizedStepKnots scale x (Fin.last n) ∈
          Set.Icc (1 / 3 - u + drift * (n : ℝ))
            (2 / 3 - u + drift * (n : ℝ)) := by
    simpa [finiteNormalizedStepKnots] using
      (mem_finiteMovingEntranceEvent_iff scale drift u x)
  change offsetCorridorPath u
      (Fin.removeLinearDrift drift (finiteNormalizedStepKnots scale x)) ↔ _
  rw [hmain]
  unfold offsetCorridorPath Fin.removeLinearDrift
  simp only [nsmul_eq_mul, mul_comm] at *
  have hlastVal : ((Fin.last n).val : ℝ) = (n : ℝ) := by simp
  constructor
  · rintro ⟨hpath, hend⟩
    refine ⟨fun j => ?_, ?_⟩
    · rcases Set.mem_Icc.mp (hpath j) with ⟨hlo, hhi⟩
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    · rcases Set.mem_Icc.mp hend with ⟨hlo, hhi⟩
      rw [hlastVal] at hlo hhi
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  · rintro ⟨hpath, hend⟩
    refine ⟨fun j => ?_, ?_⟩
    · rcases Set.mem_Icc.mp (hpath j) with ⟨hlo, hhi⟩
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    · rcases Set.mem_Icc.mp hend with ⟨hlo, hhi⟩
      rw [hlastVal]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- Measurability of the drift-removed representation follows from its
equivalence with the public entrance event. -/
lemma measurableSet_finiteDriftRemovedOffsetCorridorEvent
    {n : ℕ} (scale drift u : ℝ) :
    MeasurableSet (finiteDriftRemovedOffsetCorridorEvent
      (n := n) scale drift u) := by
  have hevent : finiteDriftRemovedOffsetCorridorEvent
      (n := n) scale drift u =
        finiteMovingEntranceEvent (n := n) scale drift u := by
    ext x
    exact finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent
      scale drift u x
  rw [hevent]
  exact measurableSet_finiteMovingEntranceEvent scale drift u

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
