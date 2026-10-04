/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Window
public import Probability.BranchingRandomWalk.Walk.Basic

/-!
# Window events for the singleton-slot branching walk

This module connects path windows in the branching-walk realization to
ordinary increment-window events. The general measurable window API lives in
`Probability.Process.RandomWalk.Path.Window`.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching
open Combinatorics.Branching.Walk
open ProbabilityTheory.RandomWalk

def ProcessInClosedInterval {Mark : Type*} [MeasurableSpace Mark]
    (d : Mark → ℝ) (lower upper : ℝ) (n : ℕ)
    (walk : Walk Mark ℝ) : Prop :=
  ∀ k : Fin (n + 1),
    process d k walk ∈ some '' Set.Icc lower upper

theorem measurableSet_processInClosedInterval
    {Mark : Type*} [MeasurableSpace Mark]
    (d : Mark → ℝ) (hd : Measurable d)
    (lower upper : ℝ) (n : ℕ) :
    MeasurableSet {walk : Walk Mark ℝ |
      ProcessInClosedInterval d lower upper n walk} := by
  rw [show {walk : Walk Mark ℝ |
      ProcessInClosedInterval d lower upper n walk} =
      ⋂ k : Fin (n + 1),
        process d k ⁻¹' (some '' Set.Icc lower upper) by
    ext walk
    simp [ProcessInClosedInterval]]
  exact MeasurableSet.iInter fun k =>
    (measurableSet_option_some_image measurableSet_Icc).preimage
      (process_measurable d hd k)

theorem processInClosedInterval_ofIncrements_iff
    (lower upper : ℝ) (n : ℕ) (initial : ℝ)
    (increment : ℕ → ℝ) :
    ProcessInClosedInterval id lower upper n
        (Walk.ofIncrements initial increment) ↔
      InClosedInterval lower upper n initial increment := by
  simp only [ProcessInClosedInterval, process_ofIncrements,
    Set.mem_image, Option.some.injEq, InClosedInterval,
    InWindows, history]
  constructor
  · intro h k
    obtain ⟨x, hx, rfl⟩ := h k
    simpa [AdditivePath.displacement] using hx
  · intro h k
    refine ⟨initial + ∑ j ∈ Finset.range (k : ℕ), increment j, ?_, rfl⟩
    simpa [AdditivePath.displacement] using h k


end ProbabilityTheory.BranchingRandomWalk.RandomWalk

end
