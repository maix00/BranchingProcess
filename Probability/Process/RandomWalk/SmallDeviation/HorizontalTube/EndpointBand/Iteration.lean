/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand.Basic
public import Probability.Kernel.Bridge
public import Probability.Kernel.Survival.Return.VariableBlocks
public import Probability.Process.RandomWalk.Kernel.Killed.Basic
import all Probability.Process.RandomWalk.Kernel.Killed.Return.Bridge
import all Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Lemmas.IndexSelection

/-!
# Iteration of finite endpoint-band block bounds

The endpoint-corridor bridge event and its finite geometry are defined in
`EndpointBand/Basic.lean`. This module transfers its seven endpoint-window
probability bounds to killed bridge rows and composes return blocks followed by
one exit block.

## Public declarations

- `bridgeKernel_apply_univ_lower_of_endpointCorridorBridgeEvents`:
  if each of the seven shifted bridge events has probability at least $p$,
  then every row of the corresponding killed bridge kernel has mass at least
  $p$.
- `iidSequenceLaw_staysIn_endsIn_ge_of_endpointCorridorBridgeEvents`:
  $r$ return blocks followed by one exit block give a corridor-and-endpoint
  event of probability at least $p^{r+1}$.

This finite return-kernel iteration formalizes Lemma 3(d) of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081. -/

open MeasureTheory Set
open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube
open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand

/-- Finitely many translated endpoint windows give a uniform lower row bound
for the killed transition between endpoint cores. -/
theorem bridgeKernel_apply_univ_lower_of_endpointCorridorBridgeEvents
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {allowedLower allowedUpper epsilon sourceCenter targetCenter : ℝ}
    (hepsilon : 0 < epsilon) (length : ℕ) (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilon
          sourceCenter targetCenter i length)) :
    ∀ x : Set.Icc (sourceCenter - 3 * epsilon)
        (sourceCenter + 3 * epsilon),
      lowerBound ≤ ProbabilityTheory.Kernel.bridgeKernel
        (RandomWalk.killedIncrementKernel ν (Set.Icc allowedLower allowedUpper)
          measurableSet_Icc)
        (Set.Icc (sourceCenter - 3 * epsilon) (sourceCenter + 3 * epsilon))
        (Set.Icc (targetCenter - 3 * epsilon) (targetCenter + 3 * epsilon))
        measurableSet_Icc length x Set.univ := by
  intro x
  have hxlocal : (x : ℝ) - sourceCenter ∈ Set.Icc (-3 * epsilon) (3 * epsilon) := by
    rcases x.property with ⟨hlo, hhi⟩
    constructor <;> nlinarith
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointWindowIndex hepsilon hxlocal
  rw [ProbabilityTheory.Kernel.bridgeKernel_apply_univ,
    RandomWalk.killedIncrementKernel_pow_apply_eq_staysIn_endsIn
      ν (Set.Icc allowedLower allowedUpper) measurableSet_Icc
      (Set.Icc (targetCenter - 3 * epsilon) (targetCenter + 3 * epsilon))
      measurableSet_Icc length (x : ℝ)]
  calc
    lowerBound ≤ iidSequenceLaw ν
        (endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilon
          sourceCenter targetCenter i length) := hband i hi
    _ ≤ iidSequenceLaw ν
        {increment | RandomWalk.StaysIn (Set.Icc allowedLower allowedUpper)
          length (x : ℝ) increment ∧
          (x : ℝ) + AdditivePath.displacement length increment ∈
            Set.Icc (targetCenter - 3 * epsilon) (targetCenter + 3 * epsilon)} :=
      measure_mono (by
        intro increment hevent
        exact endpointCorridorBridgeBlockEvent_subset_killedBridgeEvent
          hepsilon x.property (by simpa using hnear) increment hevent)

/-- Endpoint-window estimates for all repeated returns and the final bridge
compose into a lower bound for one exact-length corridor cell transition. -/
theorem iidSequenceLaw_staysIn_endsIn_ge_of_endpointCorridorBridgeEvents
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {allowedLower allowedUpper epsilon sourceCenter targetCenter : ℝ}
    (hepsilon : 0 < epsilon) (returnLengths : List ℕ) (exitLength : ℕ)
    (lowerBound : ENNReal)
    (hreturnEvents : ∀ length ∈ returnLengths, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowReturnBlockEvent (allowedLower - sourceCenter)
          (allowedUpper - sourceCenter) epsilon epsilon i length))
    (hexitEvents : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilon
          sourceCenter targetCenter i exitLength)) :
    ∀ x : Set.Icc (sourceCenter - 3 * epsilon) (sourceCenter + 3 * epsilon),
      lowerBound ^ returnLengths.length * lowerBound ≤
        iidSequenceLaw ν
          {increment | RandomWalk.StaysIn (Set.Icc allowedLower allowedUpper)
              (ProbabilityTheory.Kernel.returnKernelSequenceLength returnLengths +
                exitLength) (x : ℝ) increment ∧
            (x : ℝ) + AdditivePath.displacement
              (ProbabilityTheory.Kernel.returnKernelSequenceLength returnLengths +
                exitLength) increment ∈
              Set.Icc (targetCenter - 3 * epsilon) (targetCenter + 3 * epsilon)} := by
  let core : Set ℝ := Set.Icc (sourceCenter - 3 * epsilon)
    (sourceCenter + 3 * epsilon)
  let target : Set ℝ := Set.Icc (targetCenter - 3 * epsilon)
    (targetCenter + 3 * epsilon)
  have hreturn : ∀ length ∈ returnLengths, ∀ x : core,
      lowerBound ≤ RandomWalk.returnKernel ν
        (Set.Icc allowedLower allowedUpper) measurableSet_Icc core measurableSet_Icc
        length x Set.univ := by
    intro length hmem x
    have hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ iidSequenceLaw ν
          (endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilon
            sourceCenter sourceCenter i length) := by
      intro i hi
      rw [← endpointWindowReturnBlockEvent_eq_endpointCorridorBridgeBlockEvent
        allowedLower allowedUpper epsilon sourceCenter i length]
      exact hreturnEvents length hmem i hi
    have hrow := bridgeKernel_apply_univ_lower_of_endpointCorridorBridgeEvents
      ν hepsilon length lowerBound hband x
    simpa [RandomWalk.returnKernel, ProbabilityTheory.Kernel.returnKernel,
      ProbabilityTheory.Kernel.bridgeKernel, core,
      RandomWalk.killedIncrementKernel] using hrow
  have hexit : ∀ x : core, lowerBound ≤ ProbabilityTheory.Kernel.bridgeKernel
      (RandomWalk.killedIncrementKernel ν (Set.Icc allowedLower allowedUpper)
        measurableSet_Icc) core target measurableSet_Icc exitLength x Set.univ := by
    intro x
    have hrow := bridgeKernel_apply_univ_lower_of_endpointCorridorBridgeEvents
      ν hepsilon exitLength lowerBound hexitEvents x
    simpa [core, target] using hrow
  intro x
  simpa [core, target, RandomWalk.returnKernel] using
    RandomWalk.iidSequenceLaw_staysIn_endsIn_ge_of_returnSequenceExit
      ν (Set.Icc allowedLower allowedUpper) core target measurableSet_Icc
      measurableSet_Icc measurableSet_Icc returnLengths exitLength
      lowerBound lowerBound hreturn hexit x

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand

end
