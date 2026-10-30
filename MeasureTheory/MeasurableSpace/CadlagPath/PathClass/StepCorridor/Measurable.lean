/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Basic
public import MeasureTheory.MeasurableSpace.CadlagPath.PathClass.StepCorridor.Boundary
public import Topology.Cadlag.Skorokhod.Evaluation.Joint
public import Topology.Cadlag.Skorokhod.Evaluation.Measurable

/-!
# Borel relations for strict corridor events

This file establishes the exact Borel path-time violation relation for the
pointwise-strict `M₁` and `M₂` corridor events. Their failure remains the
projection of the actual violation relation; it is not replaced by a
uniform-margin event or by finite-coordinate constraints. Null-measurability
of the projection under finite path laws is proved separately in
`PathClass/StepCorridor/NullMeasurable.lean` using the repository's axiom-clean
capacitability result.

## Public declarations

- For a continuous admissible corridor, the path-time violation relation is
  Borel, and its projection gives the exact complement of the strict corridor.
-/

open Skorokhod.PathClass.StepCorridor

@[expose] public section

open MeasureTheory
open scoped Topology

namespace Skorokhod.PathClass.StepCorridor

private lemma strict_between_failure_iff {l x u : EReal} :
    (l < x → u ≤ x) ↔ x ≤ l ∨ u ≤ x := by
  constructor
  · intro h
    by_cases hxl : x ≤ l
    · exact Or.inl hxl
    · right
      have hlx : l < x := lt_of_not_ge hxl
      exact h hlx
  · rintro (hxl | hxu) hlx
    · exact (not_lt_of_ge hxl hlx).elim
    · exact hxu

/-- A path violates a step corridor at a specified time.  Time is the first
coordinate so the exact existential-time event is the second projection of
this Borel relation. -/
def ContinuousAdmissibleStepCorridor.violationAt (c : ContinuousAdmissibleStepCorridor) :
    Set (unitInterval × CadlagPath unitInterval ℝ) :=
  {p | (p.2 p.1 : EReal) ≤ c.lower.eval p.1 ∨
      c.upper.eval p.1 ≤ (p.2 p.1 : EReal)}

/-- The set of paths that violate a corridor at some time.  This is a
projection of `violationAt`; no measurability of this projection is assumed. -/
def ContinuousAdmissibleStepCorridor.violationSet (c : ContinuousAdmissibleStepCorridor) : Set (CadlagPath unitInterval ℝ) :=
  {path | ∃ t : unitInterval, (t, path) ∈ c.violationAt}

/-- The path-time violation relation for a finite step corridor is Borel. -/
theorem ContinuousAdmissibleStepCorridor.measurableSet_violationAt (c : ContinuousAdmissibleStepCorridor) :
    MeasurableSet c.violationAt := by
  have hpath : Measurable
      (fun p : unitInterval × CadlagPath unitInterval ℝ => (p.2 p.1 : EReal)) :=
    EReal.measurableEmbedding_coe.measurable.comp
      (Skorokhod.measurable_joint_apply.comp measurable_swap)
  have hlower : Measurable (fun p : unitInterval × CadlagPath unitInterval ℝ =>
      c.lower.eval p.1) := c.lower.eval_measurable.comp measurable_fst
  have hupper : Measurable (fun p : unitInterval × CadlagPath unitInterval ℝ =>
      c.upper.eval p.1) := c.upper.eval_measurable.comp measurable_fst
  change MeasurableSet {p : unitInterval × CadlagPath unitInterval ℝ |
      (p.2 p.1 : EReal) ≤ c.lower.eval p.1 ∨
        c.upper.eval p.1 ≤ (p.2 p.1 : EReal)}
  exact (measurableSet_le hpath hlower).union (measurableSet_le hupper hpath)

/-- The complement of the exact pointwise-strict `M₂` corridor is the union
of the bad initial-value set and the projection of the Borel path-time
violation relation. -/
theorem ContinuousAdmissibleStepCorridor.compl_toSet_eq_violationSet (c : ContinuousAdmissibleStepCorridor) :
    c.toSetᶜ = {path | path ⊥ ≠ 0} ∪ c.violationSet := by
  classical
  ext path
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq,
    ContinuousAdmissibleStepCorridor.toSet, FiniteStepCorridor.toSet, corridorSet]
  constructor
  · intro hnot
    by_cases hstart : path ⊥ = 0
    · right
      have hnot_corridor :
          ¬ ∀ t : unitInterval,
            c.lower.eval t < (path t : EReal) ∧
              (path t : EReal) < c.upper.eval t := by
        intro hcorridor
        exact hnot ⟨hstart, hcorridor⟩
      push Not at hnot_corridor
      obtain ⟨t, hbad⟩ := hnot_corridor
      refine ⟨t, ?_⟩
      change (path t : EReal) ≤ c.lower.eval t ∨
        c.upper.eval t ≤ (path t : EReal)
      exact (strict_between_failure_iff).1 hbad
    · exact Or.inl hstart
  · rintro (hstart | ⟨t, hbad⟩) hcorridor
    · exact hstart hcorridor.1
    · rcases hcorridor with ⟨_, hcorridor⟩
      change (path t : EReal) ≤ c.lower.eval t ∨
        c.upper.eval t ≤ (path t : EReal) at hbad
      rcases hbad with hlow | hupp
      · exact (not_lt_of_ge hlow) (hcorridor t).1
      · exact (not_lt_of_ge hupp) (hcorridor t).2

end Skorokhod.PathClass.StepCorridor
