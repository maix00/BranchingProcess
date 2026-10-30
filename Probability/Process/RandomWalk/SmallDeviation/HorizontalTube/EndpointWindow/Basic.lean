/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Constructions.Pi
public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.Path.Block.Corridor.Basic
import Probability.Process.RandomWalk.Path.Block.Corridor.Measure

/-!
# Horizontal tubes with endpoint windows

## Public declarations

For increments $\xi=(\xi_i)_{i\ge0}$, write
$Y_j=\sum_{i=0}^{j-1}\xi_i$.

The public definitions in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.relativeHorizontalTubeEndpointWindowEvent`: for a lower edge $r$, width $\Delta$, horizon $L$, and endpoint fractions $u,v$, it describes paths satisfying $r\le Y_j\le r+\Delta$ for $1\le j\le L$ and $Y_L\in[r+u\Delta,r+v\Delta]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeEndpointWindowEvent`: for tube parameter $a$, width $\Delta$, and horizon $L$, it describes paths satisfying $-a\Delta\le Y_j\le(1-a)\Delta$ and $(u-a)\Delta\le Y_L\le(v-a)\Delta$. This is the event used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii).
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeEndpointWindowProbability`: the probability of that normalized tube event under a law on increment sequences.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.endpointWindowBlockEvent`: a strict centered tube event with endpoint in the open window centered at `i * spacing` and half-width `windowRadius`.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.endpointWindowReturnBlockEvent`: the corresponding open corridor event for a return block, including an endpoint window.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.measurableSet_endpointWindowBlockEvent` and `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.measurableSet_endpointWindowReturnBlockEvent`: measurability of these finite-block events in the IID increment coordinates.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open ProbabilityTheory.RandomWalk
open MeasureTheory
open scoped ENNReal

/-- A horizontal tube with a specified lower edge and endpoint window. -/
def relativeHorizontalTubeEndpointWindowEvent (lower width : ℝ)
    (horizon : ℕ) (v₁ v₂ : ℝ) : Set (ℕ → ℝ) :=
  {increment | (∀ k : Fin horizon,
      lower ≤ AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤ lower + width) ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc (lower + v₁ * width) (lower + v₂ * width)}

/-- The closed tube with walls `-a * width` and `(1 - a) * width`, together
with a terminal interval from `(u - a) * width` to `(v - a) * width`.
This is the normalized endpoint-window form used in finite-variance tube
estimates, as in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (master's thesis, Fudan University, 2026), Chapter 3,
Lemma 3.1(ii). -/
def horizontalTubeEndpointWindowEvent (a width : ℝ) (horizon : ℕ)
    (u v : ℝ) : Set (ℕ → ℝ) :=
  {increment | InHorizontalTube a width horizon increment ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc ((u - a) * width) ((v - a) * width)}

/-- The probability, under a law on increment sequences, of remaining in a
closed horizontal tube and ending in the prescribed terminal interval. -/
def horizontalTubeEndpointWindowProbability (law : Measure (ℕ → ℝ))
    (a width : ℝ) (horizon : ℕ) (u v : ℝ) : ℝ≥0∞ :=
  law (horizontalTubeEndpointWindowEvent a width horizon u v)


namespace EndpointWindow

/-- A strict centered tube event with endpoint in a window centered at the
`i`th point of a mesh of spacing `spacing`. -/
def endpointWindowBlockEvent (radius spacing windowRadius : ℝ)
    (i : ℤ) (length : ℕ) : Set (ℕ → ℝ) :=
  {increment | InOpenHorizontalTube (1 / 2) (2 * radius) length increment ∧
    AdditivePath.displacement length increment ∈
      Set.Ioo ((i : ℝ) * spacing - windowRadius)
        ((i : ℝ) * spacing + windowRadius)}

/-- Endpoint-window block events are measurable in the IID increment path. -/
theorem measurableSet_endpointWindowBlockEvent
    (radius spacing windowRadius : ℝ) (i : ℤ) (length : ℕ) :
    MeasurableSet (endpointWindowBlockEvent radius spacing windowRadius i length) := by
  exact (ProbabilityTheory.RandomWalk.measurableSet_inOpenHorizontalTube
      (1 / 2) (2 * radius) length).inter
    (measurableSet_Ioo.preimage (displacement_measurable length))

/-- The return event for an endpoint window. The incoming core radius is
`3 * spacing`; its margin and the endpoint-window radius are removed from the
allowed corridor before taking the block. -/
def endpointWindowReturnBlockEvent (lower upper spacing windowRadius : ℝ)
    (i : ℤ) (length : ℕ) : Set (ℕ → ℝ) :=
  {increment | InOpenPartialSumCorridor
      (lower + 3 * spacing + windowRadius)
      (upper - 3 * spacing - windowRadius)
      (Combinatorics.Sequence.blockCoordinates 0 length increment) ∧
    Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment)
      (Fin.last length) ∈ Set.Ioo
        ((i : ℝ) * spacing - windowRadius)
        ((i : ℝ) * spacing + windowRadius)}

/-- Measurability of an endpoint-window return event in the IID increment
coordinates. -/
theorem measurableSet_endpointWindowReturnBlockEvent
    (lower upper spacing windowRadius : ℝ) (i : ℤ) (length : ℕ) :
    MeasurableSet
      (endpointWindowReturnBlockEvent lower upper spacing windowRadius i length) := by
  let coordinates : (ℕ → ℝ) → (Fin length → ℝ) :=
    fun increment => Combinatorics.Sequence.blockCoordinates 0 length increment
  have hcoordinates : Measurable coordinates := by
    apply Measurable.of_eval
    intro k
    change Measurable (fun increment : ℕ → ℝ => increment (0 + (k : ℕ)))
    simpa using (measurable_pi_apply (k : ℕ))
  change MeasurableSet (coordinates ⁻¹'
    {block : Fin length → ℝ |
      InOpenPartialSumCorridorEndsIn
        (lower + 3 * spacing + windowRadius)
        (upper - 3 * spacing - windowRadius)
        ((i : ℝ) * spacing - windowRadius)
        ((i : ℝ) * spacing + windowRadius) block})
  exact (measurableSet_inOpenPartialSumCorridorEndsIn _ _ _ _).preimage
    hcoordinates

end EndpointWindow


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
