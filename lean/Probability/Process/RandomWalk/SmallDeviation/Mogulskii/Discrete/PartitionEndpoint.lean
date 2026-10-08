/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Corridor.Measure
public import Probability.Process.RandomWalk.Path.Block.Law

/-!
# Endpoint-core events on discrete corridor cells

An incoming core contracts the cell corridor. A slightly wider outgoing core
is reached by an open endpoint band. These events depend only on the
increments in their own floor-rounded cell, so their probabilities factor
under an IID increment law.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

open ProbabilityTheory.RandomWalk

/-- The local event for one finite-partition cell. Relative partial sums stay
inside the corridor contracted by the incoming core; the endpoint band
connects the incoming core center to the outgoing core center. The band
radius is half the increase in core radius, matching the source lower
construction and leaving strict room inside the outgoing core. -/
def partitionCellCoreReturnBlockEvent {length : ℕ}
    (innerLower innerUpper startCenter startRadius endCenter endRadius : ℝ)
    (block : Fin length → ℝ) : Prop :=
  InOpenPartialSumCorridorEndsIn
    (innerLower + startRadius - startCenter)
    (innerUpper - startRadius - startCenter)
    (endCenter - startCenter - (endRadius - startRadius) / 2)
    (endCenter - startCenter + (endRadius - startRadius) / 2)
    block

/-- A finite endpoint-core cell event is measurable in the product sigma
algebra on its IID increment coordinates. -/
theorem measurableSet_partitionCellCoreReturnBlockEvent {length : ℕ}
    (innerLower innerUpper startCenter startRadius endCenter endRadius : ℝ) :
    MeasurableSet {block : Fin length → ℝ |
      partitionCellCoreReturnBlockEvent innerLower innerUpper startCenter
        startRadius endCenter endRadius block} := by
  exact measurableSet_inOpenPartialSumCorridorEndsIn _ _ _ _

/-- If the starting position is in the incoming core, every partial-sum
position of a core-return block lies in the prescribed inner cell corridor. -/
theorem partitionCellCoreReturnBlockEvent_positions_mem
    {length : ℕ} {innerLower innerUpper startCenter startRadius endCenter endRadius x : ℝ}
    {block : Fin length → ℝ}
    (hstart : x ∈ Set.Icc (startCenter - startRadius) (startCenter + startRadius))
    (hevent : partitionCellCoreReturnBlockEvent innerLower innerUpper startCenter
      startRadius endCenter endRadius block) :
    ∀ k : Fin (length + 1),
      innerLower < x + Fin.partialSum block k ∧
        x + Fin.partialSum block k < innerUpper := by
  intro k
  have hsum := hevent.1 k
  change innerLower + startRadius - startCenter < Fin.partialSum block k ∧
      Fin.partialSum block k < innerUpper - startRadius - startCenter at hsum
  constructor <;> nlinarith [hstart.1, hstart.2]

/-- The open endpoint band in a core-return block lands strictly inside the
outgoing core, uniformly over every starting point in the incoming core. -/
theorem partitionCellCoreReturnBlockEvent_endpoint_mem
    {length : ℕ} {innerLower innerUpper startCenter startRadius endCenter endRadius x : ℝ}
    {block : Fin length → ℝ}
    (hradius : startRadius < endRadius)
    (hstart : x ∈ Set.Icc (startCenter - startRadius) (startCenter + startRadius))
    (hevent : partitionCellCoreReturnBlockEvent innerLower innerUpper
      startCenter startRadius endCenter endRadius block) :
    x + Fin.partialSum block (Fin.last length) ∈
      Set.Ioo (endCenter - endRadius) (endCenter + endRadius) := by
  have hend := hevent.2
  change Fin.partialSum block (Fin.last length) ∈
    Set.Ioo (endCenter - startCenter - (endRadius - startRadius) / 2)
      (endCenter - startCenter + (endRadius - startRadius) / 2) at hend
  rcases hend with ⟨hendLower, hendUpper⟩
  rcases hstart with ⟨hstartLower, hstartUpper⟩
  constructor <;> nlinarith [hradius]

/-- The finite family of endpoint-core events on adjacent variable-length
IID increment blocks factors exactly into the corresponding one-cell
probabilities. -/
theorem iidSequenceLaw_forall_partitionCellCoreReturnBlockEvent_eq_prod
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (length : ℕ → ℕ) (blocks : ℕ)
    (innerLower innerUpper startCenter startRadius endCenter endRadius :
      Fin blocks → ℝ) :
    iidSequenceLaw ν {increment : ℕ → ℝ |
      ∀ i : Fin blocks,
        Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart length i.val) (length i.val) increment ∈
          {block | partitionCellCoreReturnBlockEvent
            (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
            (endCenter i) (endRadius i) block}} =
      ∏ i : Fin blocks, iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length i.val) increment ∈
          {block | partitionCellCoreReturnBlockEvent
            (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
            (endCenter i) (endRadius i) block}} := by
  exact iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    ν length blocks
    (fun i => {block | partitionCellCoreReturnBlockEvent
      (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
      (endCenter i) (endRadius i) block})
    (fun i => measurableSet_partitionCellCoreReturnBlockEvent
      (innerLower i) (innerUpper i) (startCenter i) (startRadius i)
      (endCenter i) (endRadius i))

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

end
