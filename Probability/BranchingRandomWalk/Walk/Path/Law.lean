/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Walk.Basic
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Laws of observed single-lineage paths

The process observed from a possibly killed singleton-slot walk is an
`Option`-valued path.  This file identifies its full path law, under the
increment-path encoding, with the law of the corresponding directly summed
position path.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching

/-- Observe a possibly killed random walk at every discrete time. -/
noncomputable def processPath
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] (d : Mark → Position) :
    Walk Mark Position → ℕ → Option Position :=
  fun walk n => process d n walk

/-- The full observed path is measurable, by coordinatewise measurability. -/
theorem processPath_measurable
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (d : Mark → Position) (hd : Measurable d) :
    Measurable (processPath d : Walk Mark Position → ℕ → Option Position) := by
  change Measurable (fun walk : Walk Mark Position =>
    fun n => process d n walk)
  rw [measurable_pi_iff]
  exact fun n => process_measurable d hd n

/-- Encode an increment path as the full `Option`-valued position path.  The
`some` constructor records that the increment-encoded walk is never killed. -/
def positionPath
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] (d : Mark → Position) (initial : Position) :
    (ℕ → Mark) → ℕ → Option Position :=
  fun increment n =>
    some (Walk.positionProcess initial n (d ∘ increment))

/-- The directly summed full position path is measurable. -/
theorem positionPath_measurable
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (d : Mark → Position) (hd : Measurable d) (initial : Position) :
    Measurable (positionPath d initial : (ℕ → Mark) → ℕ → Option Position) := by
  have hmap : Measurable (fun increment : ℕ → Mark => d ∘ increment) := by
    rw [measurable_pi_iff]
    exact fun n => hd.comp (measurable_pi_apply n)
  change Measurable (fun increment : ℕ → Mark =>
    fun n => some (Walk.positionProcess initial n (d ∘ increment)))
  rw [measurable_pi_iff]
  exact fun n => measurable_option_some.comp
    ((Walk.positionProcess_measurable initial n).comp hmap)

/-- Pointwise, observing the increment-encoded walk at all times is the same
as directly summing its mapped increments. -/
@[simp] theorem processPath_ofIncrements
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] (d : Mark → Position)
    (initial : Position) (increment : ℕ → Mark) :
    processPath d (Walk.ofIncrements initial increment) =
      positionPath d initial increment := by
  funext n
  exact process_ofIncrements d initial increment n

/-- Full path pushforward law for any law on increment paths.  No independence
assumption on the increments is needed. -/
theorem map_processPath_map_ofIncrements
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (d : Mark → Position) (hd : Measurable d) (initial : Position)
    (μ : Measure (ℕ → Mark)) :
    Measure.map (processPath d)
        (Measure.map (Walk.ofIncrements initial) μ) =
      Measure.map (positionPath d initial) μ := by
  rw [Measure.map_map (processPath_measurable d hd)
    (measurable_ofIncrements initial)]
  congr 1
  funext increment
  exact processPath_ofIncrements d initial increment

/-- Specialization of the full path pushforward law to the random-walk law
induced by an increment-path law. -/
theorem map_processPath_ofIncrementLaw
    {Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (d : Mark → Position) (hd : Measurable d) (initial : Position)
    (incrementLaw : Measure (ℕ → Mark))
    [IsProbabilityMeasure incrementLaw] :
    Measure.map (processPath d)
        ((ofIncrementLaw initial incrementLaw : RandomWalk Mark Position).law) =
      Measure.map (positionPath d initial) incrementLaw := by
  rw [ofIncrementLaw_law]
  exact map_processPath_map_ofIncrements d hd initial incrementLaw

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
