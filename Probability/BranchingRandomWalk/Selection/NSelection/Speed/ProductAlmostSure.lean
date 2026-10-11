/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Speed
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
# Almost-sure limits under product measures

If a measurable family of trajectories has a prescribed asymptotic speed for
almost every second coordinate at almost every first coordinate, then the
same speed holds almost surely under the product measure. This is the
parameter-integration step used when a fresh branching field is independent
of a random finite initial population.
-/

open MeasureTheory
open Filter
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching.Selection.NSelection

/-- Lift sectionwise almost-sure convergence of measurable trajectories to
almost-sure convergence under the product measure. -/
theorem ae_hasAsymptoticSpeed_prod_of_ae_sections
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y)
    (trajectory : X → Y → ℕ → ℝ)
    (hmeasurable : ∀ n, Measurable (fun p : X × Y => trajectory p.1 p.2 n))
    (speed : ℝ)
    [SFinite ν]
    (hsections : ∀ᵐ x ∂μ,
      ∀ᵐ y ∂ν,
        HasAsymptoticSpeed (𝕜 := ℝ) (fun n => trajectory x y n) speed) :
    ∀ᵐ p ∂μ.prod ν,
      HasAsymptoticSpeed (𝕜 := ℝ) (fun n => trajectory p.1 p.2 n) speed := by
  have hscaled (n : ℕ) : Measurable (fun p : X × Y =>
      (n : ℝ)⁻¹ * trajectory p.1 p.2 n) :=
    measurable_const.mul (hmeasurable n)
  have hevent : MeasurableSet {p : X × Y |
      HasAsymptoticSpeed (𝕜 := ℝ)
        (fun n => trajectory p.1 p.2 n) speed} := by
    change MeasurableSet {p : X × Y |
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * trajectory p.1 p.2 n)
        atTop (𝓝 speed)}
    exact measurableSet_tendsto (𝓝 speed) hscaled
  rw [Measure.ae_prod_iff_ae_ae hevent]
  exact hsections

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
