/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Basic
public import Topology.Cadlag.Skorokhod.JointEvaluation
public import Topology.Cadlag.Skorokhod.Integral
public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Measurability interfaces for strict corridor events

This file establishes the exact product-space violation relation for the
pointwise-strict `M₁` and `M₂` corridor events.  Their failure is the projection
of a Borel set of path-time pairs; it is not replaced by a uniform-margin
event or by finite-coordinate constraints.  Projection measurability is kept
as an explicit law-specific premise: the available Choquet projection theorem
in the pinned BrownianMotion dependency transitively depends on unresolved
proofs, so it is not used in the verified path.
-/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

private theorem strict_between_failure_iff {l x u : EReal} :
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

/-- The corridor constraints observed on a finite set of times, including the
path's pinned initial value. -/
def finiteCorridorEvent (upper lower : StepBoundary)
    (times : Finset unitInterval) : Set (CadlagPath unitInterval ℝ) :=
  {path | path ⊥ = 0 ∧ ∀ t ∈ times,
    lower.eval t < (path t : EReal) ∧ (path t : EReal) < upper.eval t}

/-- A path violates a step corridor at a specified time.  Time is the first
coordinate so the exact existential-time event is the second projection of
this Borel relation. -/
def M2Corridor.violationAt (c : M2Corridor) :
    Set (unitInterval × CadlagPath unitInterval ℝ) :=
  {p | (p.2 p.1 : EReal) ≤ c.lower.eval p.1 ∨
      c.upper.eval p.1 ≤ (p.2 p.1 : EReal)}

/-- The set of paths that violate a corridor at some time.  This is a
projection of `violationAt`; no measurability of this projection is assumed. -/
def M2Corridor.violationSet (c : M2Corridor) : Set (CadlagPath unitInterval ℝ) :=
  {path | ∃ t : unitInterval, (t, path) ∈ c.violationAt}

/-- The path-time violation relation for a finite step corridor is Borel. -/
theorem M2Corridor.measurableSet_violationAt (c : M2Corridor) :
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
theorem M2Corridor.compl_toSet_eq_violationSet (c : M2Corridor) :
    c.toSetᶜ = {path | path ⊥ ≠ 0} ∪ c.violationSet := by
  classical
  ext path
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq,
    M2Corridor.toSet, M1Corridor.toSet, corridorSet]
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

/-- Failure of the pinned initial value is Borel measurable. -/
theorem M2Corridor.measurableSet_badStart :
    MeasurableSet {path : CadlagPath unitInterval ℝ | path ⊥ ≠ 0} := by
  have hstart : Measurable (fun path : CadlagPath unitInterval ℝ => path ⊥) :=
    Skorokhod.measurable_apply ⊥
  have heq :
      {path : CadlagPath unitInterval ℝ | path ⊥ = 0} =
        (fun path : CadlagPath unitInterval ℝ => path ⊥) ⁻¹' ({0} : Set ℝ) := by
    ext path
    rfl
  rw [show {path : CadlagPath unitInterval ℝ | path ⊥ ≠ 0} =
      {path | path ⊥ = 0}ᶜ by ext path; simp]
  rw [heq]
  exact (measurableSet_singleton (0 : ℝ)).preimage hstart |>.compl

/-- Null-measurability of the exact existential-time projection is the
explicit hypothesis needed to obtain null-measurability of the pointwise-
strict corridor event.  The other part of the complement, the pinned initial
value, is Borel. -/
theorem M2Corridor.nullMeasurableSet_toSet_of_violationSet
    (c : M2Corridor) (P : Measure (CadlagPath unitInterval ℝ))
    (hviolation : NullMeasurableSet c.violationSet P) :
    NullMeasurableSet c.toSet P := by
  have hcompl : NullMeasurableSet c.toSetᶜ P := by
    rw [c.compl_toSet_eq_violationSet]
    exact M2Corridor.measurableSet_badStart.nullMeasurableSet.union
      hviolation
  exact hcompl.of_compl

/-- A finite-coordinate strict corridor event is Borel measurable in the
Skorokhod `J₁` topology. -/
theorem measurableSet_finiteCorridorEvent (upper lower : StepBoundary)
    (times : Finset unitInterval) :
    MeasurableSet (finiteCorridorEvent upper lower times) := by
  classical
  unfold finiteCorridorEvent
  have hstart : MeasurableSet {path : CadlagPath unitInterval ℝ | path ⊥ = 0} := by
    have heval : Measurable (fun path : CadlagPath unitInterval ℝ => path ⊥) :=
      Skorokhod.measurable_apply ⊥
    exact (measurableSet_singleton (0 : ℝ)).preimage heval
  have hpoint (t : unitInterval) :
      MeasurableSet {path : CadlagPath unitInterval ℝ |
        lower.eval t < (path t : EReal) ∧ (path t : EReal) < upper.eval t} := by
    have heval : Measurable (fun path : CadlagPath unitInterval ℝ =>
        (path t : EReal)) :=
      EReal.measurableEmbedding_coe.measurable.comp
        (Skorokhod.measurable_apply t)
    have hleft : Measurable (fun _ : CadlagPath unitInterval ℝ => lower.eval t) :=
      measurable_const
    have hright : Measurable (fun _ : CadlagPath unitInterval ℝ => upper.eval t) :=
      measurable_const
    exact (measurableSet_lt hleft heval).inter (measurableSet_lt heval hright)
  have hfinite : MeasurableSet
      (⋂ t ∈ times, {path : CadlagPath unitInterval ℝ |
        lower.eval t < (path t : EReal) ∧ (path t : EReal) < upper.eval t}) := by
    refine Finset.measurableSet_biInter (s := times) ?_
    intro t ht
    exact hpoint t
  simpa only [Set.ofPred_and, Set.ofPred_forall, Set.mem_iInter] using hstart.inter hfinite

/-- Every path in an exact `M₁` corridor satisfies each finite-coordinate
restriction of that corridor. -/
theorem M1Corridor.toSet_subset_finiteCorridorEvent
    (c : M1Corridor) (times : Finset unitInterval) :
    c.toSet ⊆ finiteCorridorEvent c.upper c.lower times := by
  intro path hpath
  rcases hpath with ⟨hstart, hcorridor⟩
  refine ⟨hstart, ?_⟩
  intro t ht
  exact hcorridor t

/-- Every path in an exact `M₂` corridor satisfies each finite-coordinate
restriction of its underlying `M₁` corridor. -/
theorem M2Corridor.toSet_subset_finiteCorridorEvent
    (c : M2Corridor) (times : Finset unitInterval) :
    c.toSet ⊆ finiteCorridorEvent c.upper c.lower times := by
  exact c.toM1Corridor.toSet_subset_finiteCorridorEvent times

/-- A Borel representative of the exact pointwise-strict corridor event for a
particular path law.  The representative may be obtained, for example, by a
separate boundary-null argument.  This certificate is measure-specific and
does not alter the definition of `M2Corridor.toSet`. -/
structure M2Corridor.BorelRepresentative
    (c : M2Corridor) (P : Measure (CadlagPath unitInterval ℝ)) where
  set : Set (CadlagPath unitInterval ℝ)
  measurable : MeasurableSet set
  ae_eq : c.toSet =ᵐ[P] set

/-- Pull back the exact corridor event along an almost-everywhere measurable
path-valued random variable.  The proof uses a measurable version of the path
map and a Borel representative under its pushforward law. -/
theorem M2Corridor.nullMeasurableSet_preimage_toSet
    {Ω : Type*} [MeasurableSpace Ω] (c : M2Corridor)
    (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → CadlagPath unitInterval ℝ) (hX : AEMeasurable X P)
    (hrep : c.BorelRepresentative (P.map hX.mk)) :
    NullMeasurableSet (X ⁻¹' c.toSet) P := by
  classical
  let X' := hX.mk
  have hX'meas : Measurable X' := hX.measurable_mk
  let Q : Measure (CadlagPath unitInterval ℝ) := P.map X'
  have hQfinite : IsFiniteMeasure Q := by
    exact Measure.isFiniteMeasure_map P X'
  let _ : IsFiniteMeasure Q := hQfinite
  have hrep' : c.BorelRepresentative Q := hrep
  have hmap : Filter.Tendsto X' (ae P) (ae Q) :=
    Measure.tendsto_ae_map (μ := P) hX'meas.aemeasurable
  have hpreimage_eq : X ⁻¹' c.toSet =ᵐ[P] X' ⁻¹' hrep'.set := by
    filter_upwards [hX.ae_eq_mk, hmap hrep'.ae_eq] with ω hXω hcorridor
    simp only [Set.mem_preimage]
    rw [hXω]
    exact hcorridor
  have hmeas : MeasurableSet (X' ⁻¹' hrep'.set) := hX'meas hrep'.measurable
  exact hmeas.nullMeasurableSet.congr hpreimage_eq.symm

/-- An exact `M₂` corridor event is null-measurable whenever its path law has
a Borel representative up to a null set.  Mathlib's `NullMeasurableSet` is
the appropriate interface for probabilities and integrals under completed
measures. -/
theorem M2Corridor.nullMeasurableSet_toSet_of_borelRepresentative
    (c : M2Corridor) (P : Measure (CadlagPath unitInterval ℝ))
    (h : c.BorelRepresentative P) : NullMeasurableSet c.toSet P := by
  exact h.measurable.nullMeasurableSet.congr h.ae_eq.symm

/-- The measure of the exact corridor event agrees with that of any Borel
representative certified up to a null set. -/
theorem M2Corridor.measure_toSet_eq_borelRepresentative
    (c : M2Corridor) (P : Measure (CadlagPath unitInterval ℝ))
    (h : c.BorelRepresentative P) : P c.toSet = P h.set :=
  measure_congr h.ae_eq

end ProbabilityTheory.Process.SmallDeviation.Mogulskii
