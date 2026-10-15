/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.EndpointBands.Geometry
public import Probability.Kernel.Survival.VariableBlocks
public import Analysis.Asymptotics.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.Horizontal

/-!
# Iteration of finite endpoint-band block bounds

The endpoint-band events and their finite geometry are defined in
`EndpointBands/Geometry.lean`. This module turns one-block lower bounds into
killed-kernel row bounds and iterates the resulting return kernel.

The public theorems in this file are:

- `bridgeKernel_apply_univ_lower_of_endpointCorridorBridgeEvents`
  and `returnKernel_apply_univ_lower_of_endpointBandReturnEvents`:
  if each of the seven shifted block events has probability at least $p$,
  then every row of the corresponding killed bridge or return kernel has
  mass at least $p$.
- `iidSequenceLaw_staysIn_endsIn_ge_of_endpointCorridorBridgeEvents`:
  $r$ return blocks followed by one exit block give a corridor-and-endpoint
  event of probability at least $p^{r+1}$.
- `iidSequenceLaw_staysIn_ge_pow_of_endpointBandReturnBlockSequence`
  and `iidSequenceLaw_staysIn_ge_pow_of_balancedEndpointBandBlocks`:
  $r$ consecutive return blocks, including balanced varying lengths,
  give corridor survival probability at least $p^r$.
- `returnKernel_apply_univ_lower_of_endpointBands`:
  the symmetric endpoint-band events give the uniform return row bound $p$.
- `horizontalTubeProbability_ge_pow_endpointBands` and
  `horizontalTubeProbability_ge_pow_endpointBands_of_horizon_le`:
  $p^r\le\mathbb P(T_{r\ell})$ and the same bound for every
  horizon $N\le r\ell$.

This is the finite return-kernel iteration in Mogul'skii,
*Small Deviations in a Space of Trajectories*, Lemma 3(d).
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

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
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointBandIndex hepsilon hxlocal
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
        (endpointBandReturnBlockEvent (allowedLower - sourceCenter)
          (allowedUpper - sourceCenter) epsilon i length))
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
      rw [← endpointBandReturnBlockEvent_eq_endpointCorridorBridgeBlockEvent
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

private theorem endpointBandReturnBlockEvent_subset_returnEvent
    {lower upper ε x : ℝ} {length : ℕ} (hε : 0 < ε)
    (hx : x ∈ Set.Icc (-3 * ε) (3 * ε))
    {i : ℤ}
    (hnear : x + (i : ℝ) * ε ∈ Set.Icc 0 ε)
    (increment : ℕ → ℝ)
    (hevent : increment ∈ endpointBandReturnBlockEvent lower upper ε i length) :
    StaysIn (Set.Icc lower upper) length x increment ∧
      x + AdditivePath.displacement length increment ∈ Set.Icc (-3 * ε) (3 * ε) := by
  rcases hevent with ⟨hpath, hend⟩
  have hstay : StaysIn (Set.Icc lower upper) length x increment := by
    intro k
    have hk := hpath k.succ
    have hsum :
        Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment)
          k.succ = AdditivePath.displacement (k + 1) increment := by
      rw [RandomWalk.partialSum_blockCoordinates,
        AdditivePath.blockSum_eq_displacement_natAdd]
      simp
    rw [hsum] at hk
    constructor <;> rcases hk with ⟨hklo, hkhi⟩ <;>
      nlinarith [hx.1, hx.2, hε]
  have hlast :
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment)
        (Fin.last length) = AdditivePath.displacement length increment := by
    rw [RandomWalk.partialSum_blockCoordinates,
      AdditivePath.blockSum_eq_displacement_natAdd]
    simp
  rw [hlast] at hend
  have hend' : x + AdditivePath.displacement length increment ∈
      Set.Icc (-3 * ε) (3 * ε) := by
    rcases hnear with ⟨hnearLower, hnearUpper⟩
    rcases hend with ⟨hendLower, hendUpper⟩
    constructor
    · have hbandLower :
          ((i : ℝ) - 1) * ε = (i : ℝ) * ε - ε := by ring
      rw [hbandLower] at hendLower
      nlinarith [hε]
    · have hbandUpper :
          ((i : ℝ) + 1) * ε = (i : ℝ) * ε + ε := by ring
      rw [hbandUpper] at hendUpper
      nlinarith [hε]
  exact ⟨hstay, hend'⟩

/-- For any open interval, finitely many endpoint-band events give a
uniform one-block return transition for the additive walk killed outside
that interval. The corridor may be shifted and asymmetric. -/
theorem returnKernel_apply_univ_lower_of_endpointBandReturnEvents
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {lower upper ε : ℝ} (hε : 0 < ε) (length : ℕ) (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointBandReturnBlockEvent lower upper ε i length)) :
    ∀ x : Set.Icc (-3 * ε) (3 * ε),
      lowerBound ≤ returnKernel ν (Set.Icc lower upper) measurableSet_Icc
        (Set.Icc (-3 * ε) (3 * ε)) measurableSet_Icc length x univ := by
  intro x
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointBandIndex hε x.property
  rw [returnKernel_apply_univ_eq_staysIn_endsIn]
  calc
    lowerBound ≤ iidSequenceLaw ν (endpointBandReturnBlockEvent lower upper ε i length) :=
      hband i hi
    _ ≤ iidSequenceLaw ν {increment |
          StaysIn (Set.Icc lower upper) length x increment ∧
            x + AdditivePath.displacement length increment ∈
              Set.Icc (-3 * ε) (3 * ε)} :=
      measure_mono (by
        intro increment hevent
        exact endpointBandReturnBlockEvent_subset_returnEvent hε x.property
          hnear increment hevent)

/-- Endpoint-band return estimates compose over an exact finite partition
with varying block lengths. The endpoint is required to return to the core
after each block, so the sequence-kernel lower bound applies; its embedded
mass is then bounded by ordinary survival over the exact sum of the lengths. -/
theorem iidSequenceLaw_staysIn_ge_pow_of_endpointBandReturnBlockSequence
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {lower upper ε : ℝ} (hε : 0 < ε) (lengths : List ℕ)
    (lowerBound : ENNReal)
    (hband : ∀ length ∈ lengths, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointBandReturnBlockEvent lower upper ε i length)) :
    ∀ x : Set.Icc (-3 * ε) (3 * ε),
      lowerBound ^ lengths.length ≤
        iidSequenceLaw ν
          {increment | StaysIn (Set.Icc lower upper)
            (ProbabilityTheory.Kernel.returnKernelSequenceLength lengths)
            (x : ℝ) increment} := by
  let allowed : Set ℝ := Set.Icc lower upper
  let core : Set ℝ := Set.Icc (-3 * ε) (3 * ε)
  let K := ProbabilityTheory.RandomWalk.killedIncrementKernel ν allowed measurableSet_Icc
  have hrow : ∀ length ∈ lengths, ∀ x : core,
      lowerBound ≤ ProbabilityTheory.Kernel.returnKernel K core
        measurableSet_Icc length x Set.univ := by
    intro length hmem x
    have h := returnKernel_apply_univ_lower_of_endpointBandReturnEvents
      ν hε length lowerBound (by
        intro i hi
        exact hband length hmem i hi) x
    simpa [K, core, allowed, ProbabilityTheory.RandomWalk.returnKernel] using h
  intro x
  have hproduct :=
    ProbabilityTheory.Kernel.pow_le_returnKernelSequence_apply_univ
      K core measurableSet_Icc lengths lowerBound hrow x
  have hdom := ProbabilityTheory.Kernel.returnKernelSequence_apply_preimage_le
    K core measurableSet_Icc lengths x Set.univ
      MeasurableSet.univ
  have hdom' :
      ProbabilityTheory.Kernel.returnKernelSequence K core measurableSet_Icc
          lengths x Set.univ ≤
        (K ^ ProbabilityTheory.Kernel.returnKernelSequenceLength lengths)
          (x : ℝ) Set.univ := by
    simpa using hdom
  calc
    lowerBound ^ lengths.length ≤
        ProbabilityTheory.Kernel.returnKernelSequence K core measurableSet_Icc
          lengths x Set.univ := hproduct
    _ ≤ iidSequenceLaw ν
        {increment | StaysIn allowed
          (ProbabilityTheory.Kernel.returnKernelSequenceLength lengths)
          (x : ℝ) increment} := by
      rw [← ProbabilityTheory.RandomWalk.killedIncrementKernel_pow_apply_univ
        ν allowed measurableSet_Icc
        (ProbabilityTheory.Kernel.returnKernelSequenceLength lengths) (x : ℝ)]
      exact hdom'

/-- A floor-sized reference length can be adjusted into an exact finite
partition by distributing its remainder across the blocks. If each of the
two possible adjacent lengths has the seven endpoint-band lower bounds, the
whole cell survival probability gets the product bound with no leftover
segment. -/
theorem iidSequenceLaw_staysIn_ge_pow_of_balancedEndpointBandBlocks
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {lower upper ε : ℝ} (hε : 0 < ε)
    (total referenceLength : ℕ)
    (hcount : 0 < Asymptotics.balancedBlockCount total referenceLength)
    (lowerBound : ENNReal)
    (hshort : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointBandReturnBlockEvent lower upper ε i
          (Asymptotics.balancedBlockShortLength total referenceLength)))
    (hlong : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointBandReturnBlockEvent lower upper ε i
          (Asymptotics.balancedBlockShortLength total referenceLength + 1))) :
    ∀ x : Set.Icc (-3 * ε) (3 * ε),
      lowerBound ^ Asymptotics.balancedBlockCount total referenceLength ≤
        iidSequenceLaw ν
          {increment | StaysIn (Set.Icc lower upper) total (x : ℝ) increment} := by
  let lengths := Asymptotics.balancedBlockLengths total referenceLength
  have hband : ∀ length ∈ lengths, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointBandReturnBlockEvent lower upper ε i length) := by
    intro length hmem i hi
    rcases Asymptotics.mem_balancedBlockLengths hmem with h | h
    · simpa [h] using hshort i hi
    · simpa [h] using hlong i hi
  have hsequence := iidSequenceLaw_staysIn_ge_pow_of_endpointBandReturnBlockSequence
    ν hε lengths lowerBound hband
  have hlength : lengths.length =
      Asymptotics.balancedBlockCount total referenceLength := by
    simpa [lengths] using Asymptotics.balancedBlockLengths_length hcount
  have htotal : ProbabilityTheory.Kernel.returnKernelSequenceLength lengths = total := by
    rw [ProbabilityTheory.Kernel.returnKernelSequenceLength_eq_sum]
    simpa [lengths] using Asymptotics.balancedBlockLengths_sum hcount
  intro x
  simpa [hlength, htotal] using hsequence x

/-- The seven endpoint-band estimates in Mogulskii's lower block comparison
give a uniform one-block transition from the return core back to itself. -/
private theorem endpointBandBlockEvent_subset_returnEvent
    {radius ε x : ℝ} {length : ℕ} (hε : 0 < ε)
    (hx : x ∈ Set.Icc (-3 * ε) (3 * ε))
    {i : ℤ}
    (hnear : x + (i : ℝ) * ε ∈ Set.Icc 0 ε)
    (increment : ℕ → ℝ)
    (hevent : increment ∈ endpointBandBlockEvent radius ε i length) :
    StaysIn (Set.Icc (-(radius + 4 * ε)) (radius + 4 * ε)) length x increment ∧
      x + AdditivePath.displacement length increment ∈ Set.Icc (-3 * ε) (3 * ε) := by
  rcases hevent with ⟨hpath, hend⟩
  have hstay :
      StaysIn (Set.Icc (-(radius + 4 * ε)) (radius + 4 * ε)) length x increment := by
    intro k
    have hk := hpath k
    change -(1 / 2 : ℝ) * (2 * radius) < AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment < (1 - 1 / 2 : ℝ) * (2 * radius) at hk
    constructor <;> nlinarith [hx.1, hx.2, hk.1, hk.2, hε]
  have hend' : x + AdditivePath.displacement length increment ∈
      Set.Icc (-3 * ε) (3 * ε) := by
    rcases hnear with ⟨hnearLower, hnearUpper⟩
    rcases hend with ⟨hendLower, hendUpper⟩
    constructor
    · have hbandLower :
          ((i : ℝ) - 1) * ε = (i : ℝ) * ε - ε := by ring
      rw [hbandLower] at hendLower
      nlinarith [hε]
    · have hbandUpper :
          ((i : ℝ) + 1) * ε = (i : ℝ) * ε + ε := by ring
      rw [hbandUpper] at hendUpper
      nlinarith [hε]
  exact ⟨hstay, hend'⟩

theorem returnKernel_apply_univ_lower_of_endpointBands
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius ε : ℝ} (hε : 0 < ε) (length : ℕ) (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν (endpointBandBlockEvent radius ε i length)) :
    ∀ x : Set.Icc (-3 * ε) (3 * ε),
      lowerBound ≤ returnKernel ν
        (Set.Icc (-(radius + 4 * ε)) (radius + 4 * ε)) measurableSet_Icc
        (Set.Icc (-3 * ε) (3 * ε)) measurableSet_Icc length x univ := by
  intro x
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointBandIndex hε x.property
  rw [returnKernel_apply_univ_eq_staysIn_endsIn]
  calc
    lowerBound ≤ iidSequenceLaw ν (endpointBandBlockEvent radius ε i length) :=
      hband i hi
    _ ≤ iidSequenceLaw ν {increment |
          StaysIn (Set.Icc (-(radius + 4 * ε)) (radius + 4 * ε)) length x increment ∧
            x + AdditivePath.displacement length increment ∈ Set.Icc (-3 * ε) (3 * ε)} :=
      measure_mono (by
        intro increment hevent
        exact endpointBandBlockEvent_subset_returnEvent hε x.property
          hnear increment hevent)

/-- The finite endpoint-band lower estimates iterate to a lower bound for a
horizontal tube.  This is the discrete block lower bound in the form used
before the Donsker transfer in Lemma 4. -/
theorem horizontalTubeProbability_ge_pow_endpointBands
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius ε : ℝ} (hε : 0 < ε) (blocks length : ℕ) (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν (endpointBandBlockEvent radius ε i length)) :
    lowerBound ^ blocks ≤
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (2 * (radius + 4 * ε)) (blocks * length) := by
  have hrow := returnKernel_apply_univ_lower_of_endpointBands
    ν hε length lowerBound hband
  have hallowed :
      Set.Icc (-(radius + 4 * ε)) (radius + 4 * ε) =
        Set.Icc (2 * (radius + 4 * ε) * (-(1 / 2 : ℝ)))
          (2 * (radius + 4 * ε) * (1 - 1 / 2 : ℝ)) := by
    congr 1 <;> ring
  have hrow' : ∀ x : Set.Icc (-3 * ε) (3 * ε),
      lowerBound ≤ Kernel.returnKernel
        (killedIncrementKernel ν
            (Set.Icc (2 * (radius + 4 * ε) * (-(1 / 2 : ℝ)))
              (2 * (radius + 4 * ε) * (1 - 1 / 2 : ℝ))) measurableSet_Icc)
        (Set.Icc (-3 * ε) (3 * ε)) measurableSet_Icc length x univ := by
    intro x
    have hx := hrow x
    change lowerBound ≤ Kernel.returnKernel
      (killedIncrementKernel ν (Set.Icc (-(radius + 4 * ε)) (radius + 4 * ε))
        measurableSet_Icc)
      (Set.Icc (-3 * ε) (3 * ε)) measurableSet_Icc length x univ at hx
    simpa only [hallowed] using hx
  have hmain := horizontalTubeProbability_ge_pow_returnBlock ν
    (a := (1 / 2 : ℝ)) (width := 2 * (radius + 4 * ε))
    (returnSet := Set.Icc (-3 * ε) (3 * ε)) measurableSet_Icc
    (by
      change -3 * ε ≤ 0 ∧ 0 ≤ 3 * ε
      constructor <;> nlinarith [hε]) lowerBound blocks length hrow'
  simpa [mul_assoc] using hmain

/-- Use one extra complete block to cover an arbitrary horizon. Since
confinement on the longer concatenated path implies confinement on the
requested prefix, this is the lower-bound counterpart of discarding a tail
in the upper block estimate. -/
theorem horizontalTubeProbability_ge_pow_endpointBands_of_horizon_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius ε : ℝ} (hε : 0 < ε) (blocks length horizon : ℕ)
    (hcover : horizon ≤ blocks * length) (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν (endpointBandBlockEvent radius ε i length)) :
    lowerBound ^ blocks ≤
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (2 * (radius + 4 * ε)) horizon := by
  exact (horizontalTubeProbability_ge_pow_endpointBands
      ν hε blocks length lowerBound hband).trans
    (horizontalTubeProbability_mono_horizon
      (iidSequenceLaw ν) (1 / 2) (2 * (radius + 4 * ε)) hcover)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
