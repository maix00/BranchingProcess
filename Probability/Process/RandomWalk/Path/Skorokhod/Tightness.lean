/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Tight
public import Probability.Process.RandomWalk.Path.Skorokhod
public import Probability.Process.RandomWalk.Path.Skorokhod.Basic

/-!
# Tightness of fixed random-walk path laws

For each fixed step count, the normalized path law is a continuous image of
the countable product law of the increments. Mathlib's tightness theorem for
finite measures on Polish spaces therefore gives tightness of each individual
path law and of every finite family of such laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

/-- Every fixed-step normalized random-walk path law is tight. -/
theorem isTightMeasureSet_singleton_normalizedStepPathLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (scale : ℕ → ℝ) (n : ℕ) :
    IsTightMeasureSet {normalizedStepPathLaw ν scale n} := by
  let hsource : IsTightMeasureSet {independentIncrementLaw ν} :=
    isTightMeasureSet_singleton
  have hmap := hsource.map (continuous_normalizedStepCadlagPathIcc scale n)
  simpa [normalizedStepPathLaw, independentIncrementLaw] using hmap

private theorem isTightMeasureSet_of_finite_singletons
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (S : Set (Measure X))
    (hfinite : S.Finite)
    (htight : ∀ μ ∈ S, IsTightMeasureSet {μ}) :
    IsTightMeasureSet S := by
  induction S, hfinite using Set.Finite.induction_on with
  | empty =>
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro ε hε
      exact ⟨∅, isCompact_empty, by simp⟩
  | @insert μ S hμ hS ih =>
      rw [Set.forall_mem_insert] at htight
      exact htight.1.union (ih htight.2)

/-- Every finite set of fixed-step normalized random-walk path laws is tight.
This supplies the finite-index part of an asymptotic path-tightness argument. -/
theorem isTightMeasureSet_normalizedStepPathLaw_image_of_finite
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (scale : ℕ → ℝ)
    {I : Set ℕ} (hI : I.Finite) :
    IsTightMeasureSet (normalizedStepPathLaw ν scale '' I) := by
  apply isTightMeasureSet_of_finite_singletons
    (normalizedStepPathLaw ν scale '' I) (hI.image _)
  intro μ hμ
  obtain ⟨n, hn, rfl⟩ := hμ
  exact isTightMeasureSet_singleton_normalizedStepPathLaw ν scale n

end ProbabilityTheory.RandomWalk

end
