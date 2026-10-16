/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Equiv
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Measurable singleton-walk representation

The deterministic equivalence between a singleton branching walk and its
initial position with optional increments is measurable in both directions.
The option-valued coordinates retain edges absent after extinction.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Walk

variable {Mark Position : Type*}
  [MeasurableSpace Mark] [MeasurableSpace Position]

/-- A singleton branching walk is measurably equivalent to its initial
position and its possibly absent increments. -/
def measurableEquivInitialOptionalIncrements :
    Combinatorics.Branching.Walk Mark Position ≃ᵐ
      Position × (ℕ → Option Mark) := by
  let e : Combinatorics.Branching.Walk Mark Position ≃
      Position × (ℕ → Option Mark) :=
    Combinatorics.Branching.Walk.equivInitialOptionalIncrements
  refine ⟨e, ?_, ?_⟩
  · have hwalk : Measurable
        (fun w : Combinatorics.Branching.Walk Mark Position =>
          (w.step, w.initial)) :=
      Measurable.of_comap_le le_rfl
    have hinitial : Measurable
        (fun w : Combinatorics.Branching.Walk Mark Position =>
          w.initial PUnit.unit) :=
      (measurable_pi_apply PUnit.unit).comp (measurable_snd.comp hwalk)
    have hincrements : Measurable
        (fun w : Combinatorics.Branching.Walk Mark Position =>
          Combinatorics.Branching.Walk.increments w) := by
      rw [measurable_pi_iff]
      intro n
      exact (measurable_pi_apply PUnit.unit).comp
        ((measurable_pi_apply (Combinatorics.Branching.Walk.lineNode n)).comp
          ((measurable_pi_apply PUnit.unit).comp (measurable_fst.comp hwalk)))
    change Measurable (fun w =>
      (w.initial PUnit.unit, Combinatorics.Branching.Walk.increments w))
    exact hinitial.prodMk hincrements
  · rw [measurable_comap_iff]
    change Measurable (fun p : Position × (ℕ → Option Mark) =>
      ((Combinatorics.Branching.Walk.ofOptionalIncrements p.1 p.2).step,
       (Combinatorics.Branching.Walk.ofOptionalIncrements p.1 p.2).initial))
    have hstep : Measurable
        (fun p : Position × (ℕ → Option Mark) =>
          (Combinatorics.Branching.Walk.ofOptionalIncrements p.1 p.2).step) := by
      rw [measurable_pi_iff]
      intro root
      cases root
      rw [measurable_pi_iff]
      intro u
      rw [measurable_pi_iff]
      intro i
      exact (measurable_pi_apply u.length).comp measurable_snd
    have hinitial : Measurable
        (fun p : Position × (ℕ → Option Mark) =>
          (Combinatorics.Branching.Walk.ofOptionalIncrements p.1 p.2).initial) := by
      rw [measurable_pi_iff]
      intro root
      cases root
      exact measurable_fst
    exact hstep.prodMk hinitial

end ProbabilityTheory.BranchingRandomWalk.Walk

end
