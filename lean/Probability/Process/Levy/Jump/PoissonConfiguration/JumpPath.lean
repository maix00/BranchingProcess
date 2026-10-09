/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Probability.RandomMeasure.Poisson.UniquePoint

/-!
# The path of a single selected jump

The large-jump path is a time-indexed integral against the part of a Poisson
random measure in a prescribed mark region. On the event that the region
contains exactly one point, the entire path is a single step function.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The (possibly killed) large-jump contribution from a mark region. -/
noncomputable def poissonJumpPath {Ω : Type} [MeasurableSpace Ω]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → unitInterval × ℝ)
    (A : Set (unitInterval × ℝ)) (ω : Ω) (t : unitInterval) : ℝ :=
  ∫ z in A, if z.1 ≤ t then z.2 else 0 ∂(poissonRandomMeasure K X ω)

/-- A unique point in `J`, with no other point in `B`, gives a single-jump
path simultaneously at every time, without choosing a measurable jump slot. -/
theorem poissonJumpPath_eq_singleJump_of_one_zero
    {Ω : Type} [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ}
    {X : ℕ → ℕ → Ω → unitInterval × ℝ}
    {m : Measure (unitInterval × ℝ)} [SigmaFinite m]
    {J B : Set (unitInterval × ℝ)}
    (hJ : MeasurableSet J) (hB : MeasurableSet B) (ω : Ω)
    (hOne : (poissonRandomMeasure K X ω : Measure (unitInterval × ℝ)) J = 1)
    (hZero : (poissonRandomMeasure K X ω : Measure (unitInterval × ℝ)) B = 0) :
    ∃ p : ℕ × ℕ,
      p.2 < K p.1 ω ∧ X p.1 p.2 ω ∈ J ∧
      ∀ t : unitInterval,
        poissonJumpPath K X (J ∪ B) ω t =
          if (X p.1 p.2 ω).1 ≤ t then (X p.1 p.2 ω).2 else 0 := by
  obtain ⟨p, hpK, hpJ, hmeasure⟩ :=
    poissonRandomMeasure_restrict_union_eq_dirac_of_one_zero
      (m := m) hJ hB ω hOne hZero
  refine ⟨p, hpK, hpJ, ?_⟩
  intro t
  unfold poissonJumpPath
  rw [hmeasure, integral_dirac]

end ProbabilityTheory
