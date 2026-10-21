/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Block.Measurable
public import Probability.Process.RandomWalk.Path.Event.Oscillation
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Oscillation events for finite random-walk blocks

For a finite increment block $x=(x_0,\ldots,x_{m-1})$, let
$S_j=\sum_{i<j}x_i$. This module defines the measurable events
$\{|S_i-S_j|\le w\ (0\le i,j\le m)\}$ and
$\{|S_i-S_j|<w\ (0\le i,j\le m)\}$. It also records the half-open
prefix version, which observes $0\le i,j<m$, and the deterministic
translation from an additive-path segment to its increment block.

The public declarations are:

- `blockOscillationEvent` and `blockOscillationLTEvent`: weak and strict
  pairwise range bounds for all positions in a finite increment block.
- `blockOscillationPrefixLTEvent`: the strict pairwise range bound before
  the terminal increment of a block.
- the corresponding `measurableSet_...` theorems.
- `blockOscillationEvent_of_additiveSegment`: an oscillation bound on an
  additive-path segment implies the weak finite-block event.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The event that the partial-sum path of one finite increment block has
oscillation at most `width`. -/
def blockOscillationEvent (width : ℝ) (length : ℕ) :
    Set (Fin length → ℝ) :=
  {increments | OscillationBounded
    (fun time : Fin (length + 1) => Fin.partialSum increments time) width}

/-- The finite-block oscillation event is measurable. -/
theorem measurableSet_blockOscillationEvent (width : ℝ) (length : ℕ) :
    MeasurableSet (blockOscillationEvent width length) := by
  rw [show blockOscillationEvent width length =
      ⋂ i : Fin (length + 1), ⋂ j : Fin (length + 1),
        {increments : Fin length → ℝ |
          |Fin.partialSum increments i - Fin.partialSum increments j| ≤
            width} by
    ext increments
    simp [blockOscillationEvent, OscillationBounded]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    have hdiff : Measurable (fun increments : Fin length → ℝ =>
        Fin.partialSum increments i - Fin.partialSum increments j) :=
      (measurable_finPartialSum i).sub (measurable_finPartialSum j)
    exact measurableSet_Iic.preimage
      (continuous_abs.measurable.comp hdiff)

/-- The finite-block path has range strictly less than `width`, expressed as
the pairwise strict-distance condition used for a block event. -/
def blockOscillationLTEvent (width : ℝ) (length : ℕ) :
    Set (Fin length → ℝ) :=
  {increments | ∀ i j : Fin (length + 1),
    |Fin.partialSum increments i - Fin.partialSum increments j| < width}

/-- The strict finite-block range event is measurable. -/
theorem measurableSet_blockOscillationLTEvent (width : ℝ) (length : ℕ) :
    MeasurableSet (blockOscillationLTEvent width length) := by
  rw [show blockOscillationLTEvent width length =
      ⋂ i : Fin (length + 1), ⋂ j : Fin (length + 1),
        {increments : Fin length → ℝ |
          |Fin.partialSum increments i - Fin.partialSum increments j| <
            width} by
    ext increments
    simp [blockOscillationLTEvent]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    have hdiff : Measurable (fun increments : Fin length → ℝ =>
        Fin.partialSum increments i - Fin.partialSum increments j) :=
      (measurable_finPartialSum i).sub (measurable_finPartialSum j)
    exact measurableSet_Iio.preimage
      (continuous_abs.measurable.comp hdiff)

/-- Oscillation of a block before its final coordinate. This is the event that
arises on a half-open time cell: the value at the right knot belongs to the
next cell, so the preceding cell only constrains positions at offsets strictly
less than its full block length. -/
def blockOscillationPrefixLTEvent (width : ℝ) (length : ℕ) :
    Set (Fin length → ℝ) :=
  {increments | ∀ i j : Fin length,
    |Fin.partialSum increments i.castSucc -
      Fin.partialSum increments j.castSucc| < width}

/-- The strict range event observing every partial sum before the final
coordinate of a finite increment block is measurable. -/
theorem measurableSet_blockOscillationPrefixLTEvent
    (width : ℝ) (length : ℕ) :
    MeasurableSet (blockOscillationPrefixLTEvent width length) := by
  rw [show blockOscillationPrefixLTEvent width length =
      ⋂ i : Fin length, ⋂ j : Fin length,
        {increments : Fin length → ℝ |
          |Fin.partialSum increments i.castSucc -
            Fin.partialSum increments j.castSucc| < width} by
    ext increments
    simp [blockOscillationPrefixLTEvent]]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => by
    have hdiff : Measurable (fun increments : Fin length → ℝ =>
        Fin.partialSum increments i.castSucc -
          Fin.partialSum increments j.castSucc) :=
      (measurable_finPartialSum i.castSucc).sub
        (measurable_finPartialSum j.castSucc)
    exact measurableSet_Iio.preimage
      (continuous_abs.measurable.comp hdiff)

/-- An oscillation bound for the additive path over one segment implies the
finite-block oscillation event for the increments in that segment. -/
theorem blockOscillationEvent_of_additiveSegment
    {start length : ℕ} {increment : ℕ → ℝ} {width : ℝ}
    (hsegment : OscillationBounded
      (fun k : Fin (length + 1) =>
        AdditivePath.displacement (start + (k : ℕ)) increment) width) :
    blockOscillationEvent width length
      (Combinatorics.Sequence.blockCoordinates start length increment) := by
  change OscillationBounded
    (fun k : Fin (length + 1) =>
      Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates start length increment) k)
    width
  intro i j
  change |Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates start length increment) i -
    Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates start length increment) j| ≤ width
  have hpartial (k : Fin (length + 1)) :
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates start length increment) k =
        AdditivePath.displacement (start + (k : ℕ)) increment -
          AdditivePath.displacement start increment := by
    rw [partialSum_blockCoordinates, AdditivePath.displacement_add_eq_add_blockSum]
    ring
  rw [hpartial i, hpartial j]
  calc
    |(AdditivePath.displacement (start + (i : ℕ)) increment -
          AdditivePath.displacement start increment) -
      (AdditivePath.displacement (start + (j : ℕ)) increment -
          AdditivePath.displacement start increment)| =
        |AdditivePath.displacement (start + (i : ℕ)) increment -
          AdditivePath.displacement (start + (j : ℕ)) increment| := by
      congr 1
      ring
    _ ≤ width := hsegment i j

end ProbabilityTheory.RandomWalk

end
