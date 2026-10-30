/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic
import Probability.Process.RandomWalk.Path.Block.Partition.Basic
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Kernel.BlockIteration
public import Probability.Process.RandomWalk.Kernel.Killed.Return.Basic
public import Combinatorics.Sequence.BalancedPartition
public import Probability.Kernel.Survival.Return.VariableBlocks
import all Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Lemmas.IndexSelection
/-!
# Endpoint windows with separate mesh and width

The lattice used to select a return band and the half-width of that band are
independent parameters.  This distinction is needed when a weak-limit
Portmanteau argument enlarges the endpoint window while keeping the return
core mesh fixed.

For $S_k=\sum_{j<k}\xi_j$, the block event is
\[
 E_i=\left\{\xi:|S_k|<r\ (1\leq k\leq\ell),\quad
 S_\ell\in(id-w,id+w)\right\}.
\]
If each of the seven window probabilities is at least $p$, the return-kernel
row bound on the core $[-3d,3d]$ is at least $p$, and $m$ such returns give
$p^m\leq\mathbb P_\nu(T_{m\ell}(r))$, where
$T_N(r)=\{\xi:|S_k|<r\text{ for }1\leq k\leq N\}$.

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.returnKernel_apply_univ_lower_of_endpointWindowEvents`:
  a common lower bound for endpoint windows gives the same lower bound for
  every return-kernel row on the core `[-3 * spacing, 3 * spacing]`.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.horizontalTubeProbability_ge_pow_endpointWindows`:
  iterating `blocks` such return steps gives a horizontal-tube probability at
  least `lowerBound ^ blocks`.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.horizontalTubeProbability_ge_pow_endpointWindows_of_horizon_le`:
  the same lower bound holds for every horizon covered by those complete
  return blocks.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.returnKernel_apply_univ_lower_of_endpointWindowReturnEvents`:
  a uniform lower bound for open return-window events gives the same lower
  bound for every killed-kernel row on the return core.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.iidSequenceLaw_staysIn_ge_pow_of_endpointWindowReturnBlockSequence`:
  return-window block bounds with varying lengths give the corresponding
  power lower bound for exact finite partitions.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.iidSequenceLaw_staysIn_ge_pow_of_balancedEndpointWindowReturnBlocks`:
  the return-window bound applies to the two adjacent lengths in a balanced
  partition of a prescribed horizon.

The seven-window return iteration follows Lemma 3(d) of A. A. Mogul'skii,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081. This module keeps the window mesh and
window half-width independent for the Portmanteau transfer.
-/

open MeasureTheory Set
open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

/-- An endpoint-window block gives a killed-walk path whose endpoint returns
to the core `[-3 * spacing, 3 * spacing]`. -/
private lemma endpointWindowBlockEvent_subset_returnEvent
    {radius spacing windowRadius x : ℝ} {length : ℕ}
    (hspacing : 0 < spacing) (hwindow : 0 < windowRadius)
    (hwindowLe : windowRadius ≤ 2 * spacing)
    (hx : x ∈ Set.Icc (-3 * spacing) (3 * spacing)) {i : ℤ}
    (hnear : x + (i : ℝ) * spacing ∈ Set.Icc 0 spacing)
    (increment : ℕ → ℝ)
    (hevent : increment ∈ endpointWindowBlockEvent radius spacing
      windowRadius i length) :
    StaysIn (Set.Icc (-(radius + 3 * spacing + windowRadius))
      (radius + 3 * spacing + windowRadius)) length x increment ∧
      x + AdditivePath.displacement length increment ∈
        Set.Icc (-3 * spacing) (3 * spacing) := by
  rcases hevent with ⟨hpath, hend⟩
  have hstay : StaysIn (Set.Icc
      (-(radius + 3 * spacing + windowRadius))
      (radius + 3 * spacing + windowRadius)) length x increment := by
    intro k
    have hk := hpath k
    change -(1 / 2 : ℝ) * (2 * radius) <
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment <
        (1 - 1 / 2 : ℝ) * (2 * radius) at hk
    constructor <;> nlinarith [hx.1, hx.2, hk.1, hk.2, hspacing.le,
      hwindow.le]
  have hend' : x + AdditivePath.displacement length increment ∈
      Set.Icc (-3 * spacing) (3 * spacing) := by
    rcases hnear with ⟨hnearLower, hnearUpper⟩
    rcases hend with ⟨hendLower, hendUpper⟩
    constructor
    · nlinarith [hx.1, hnearLower, hwindowLe]
    · nlinarith [hx.2, hnearUpper, hwindowLe]
  exact ⟨hstay, hend'⟩

/-- A finite collection of endpoint windows gives a uniform return row bound
for the killed walk.  The window half-width may differ from the mesh spacing,
provided it is at most twice that spacing. -/
theorem returnKernel_apply_univ_lower_of_endpointWindowEvents
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius spacing windowRadius : ℝ}
    (hspacing : 0 < spacing) (hwindow : 0 < windowRadius)
    (hwindowLe : windowRadius ≤ 2 * spacing) (length : ℕ)
    (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowBlockEvent radius spacing windowRadius i length)) :
    ∀ x : Set.Icc (-3 * spacing) (3 * spacing),
      lowerBound ≤ returnKernel ν
        (Set.Icc (-(radius + 3 * spacing + windowRadius))
          (radius + 3 * spacing + windowRadius)) measurableSet_Icc
        (Set.Icc (-3 * spacing) (3 * spacing)) measurableSet_Icc length x univ := by
  intro x
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointWindowIndex hspacing x.property
  rw [returnKernel_apply_univ_eq_staysIn_endsIn]
  calc
    lowerBound ≤ iidSequenceLaw ν
        (endpointWindowBlockEvent radius spacing windowRadius i length) := hband i hi
    _ ≤ iidSequenceLaw ν {increment |
          StaysIn (Set.Icc (-(radius + 3 * spacing + windowRadius))
              (radius + 3 * spacing + windowRadius)) length x increment ∧
            x + AdditivePath.displacement length increment ∈
              Set.Icc (-3 * spacing) (3 * spacing)} :=
      measure_mono (by
        intro increment hevent
        exact endpointWindowBlockEvent_subset_returnEvent hspacing hwindow
          hwindowLe x.property hnear increment hevent)

private lemma endpointWindowReturnBlockEvent_subset_returnEvent
    {lower upper spacing windowRadius x : ℝ} {length : ℕ}
    (hspacing : 0 < spacing) (hwindow : 0 < windowRadius)
    (hwindowLe : windowRadius ≤ 2 * spacing)
    (hx : x ∈ Set.Icc (-3 * spacing) (3 * spacing)) {i : ℤ}
    (hnear : x + (i : ℝ) * spacing ∈ Set.Icc 0 spacing)
    (increment : ℕ → ℝ)
    (hevent : increment ∈ endpointWindowReturnBlockEvent lower upper
      spacing windowRadius i length) :
    StaysIn (Set.Icc lower upper) length x increment ∧
      x + AdditivePath.displacement length increment ∈
        Set.Icc (-3 * spacing) (3 * spacing) := by
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
    rcases hx with ⟨hxlo, hxhi⟩
    rcases hk with ⟨hklo, hkhi⟩
    constructor <;> nlinarith [hspacing.le, hwindow.le]
  have hlast :
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment)
        (Fin.last length) = AdditivePath.displacement length increment := by
    rw [RandomWalk.partialSum_blockCoordinates,
      AdditivePath.blockSum_eq_displacement_natAdd]
    simp
  rw [hlast] at hend
  rcases hend with ⟨hendlo, hendhi⟩
  rcases hnear with ⟨hnearlo, hnearhi⟩
  have hend' : x + AdditivePath.displacement length increment ∈
      Set.Icc (-3 * spacing) (3 * spacing) := by
    constructor <;> nlinarith [hspacing.le, hwindowLe]
  exact ⟨hstay, hend'⟩

/-- Uniform lower bounds for return-window events give a uniform lower bound
for every row of the killed return kernel on the centered core. -/
theorem returnKernel_apply_univ_lower_of_endpointWindowReturnEvents
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {lower upper spacing windowRadius : ℝ}
    (hspacing : 0 < spacing) (hwindow : 0 < windowRadius)
    (hwindowLe : windowRadius ≤ 2 * spacing) (length : ℕ)
    (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowReturnBlockEvent lower upper spacing windowRadius i length)) :
    ∀ x : Set.Icc (-3 * spacing) (3 * spacing),
      lowerBound ≤ returnKernel ν (Set.Icc lower upper) measurableSet_Icc
        (Set.Icc (-3 * spacing) (3 * spacing)) measurableSet_Icc length x univ := by
  intro x
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointWindowIndex hspacing x.property
  rw [returnKernel_apply_univ_eq_staysIn_endsIn]
  calc
    lowerBound ≤ iidSequenceLaw ν
        (endpointWindowReturnBlockEvent lower upper spacing windowRadius i length) :=
      hband i hi
    _ ≤ iidSequenceLaw ν {increment |
          StaysIn (Set.Icc lower upper) length x increment ∧
            x + AdditivePath.displacement length increment ∈
              Set.Icc (-3 * spacing) (3 * spacing)} :=
      measure_mono (by
        intro increment hevent
        exact endpointWindowReturnBlockEvent_subset_returnEvent hspacing
          hwindow hwindowLe x.property hnear increment hevent)

/-- Return-window estimates compose over an exact finite partition with
varying block lengths. -/
theorem iidSequenceLaw_staysIn_ge_pow_of_endpointWindowReturnBlockSequence
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {lower upper spacing windowRadius : ℝ}
    (hspacing : 0 < spacing) (hwindow : 0 < windowRadius)
    (hwindowLe : windowRadius ≤ 2 * spacing) (lengths : List ℕ)
    (lowerBound : ENNReal)
    (hband : ∀ length ∈ lengths, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowReturnBlockEvent lower upper spacing windowRadius i length)) :
    ∀ x : Set.Icc (-3 * spacing) (3 * spacing),
      lowerBound ^ lengths.length ≤ iidSequenceLaw ν
        {increment | StaysIn (Set.Icc lower upper)
          (ProbabilityTheory.Kernel.returnKernelSequenceLength lengths)
          (x : ℝ) increment} := by
  let allowed : Set ℝ := Set.Icc lower upper
  let core : Set ℝ := Set.Icc (-3 * spacing) (3 * spacing)
  let K := ProbabilityTheory.RandomWalk.killedIncrementKernel ν allowed measurableSet_Icc
  have hrow : ∀ length ∈ lengths, ∀ x : core,
      lowerBound ≤ ProbabilityTheory.Kernel.returnKernel K core
        measurableSet_Icc length x Set.univ := by
    intro length hmem x
    have h := returnKernel_apply_univ_lower_of_endpointWindowReturnEvents
      ν hspacing hwindow hwindowLe length lowerBound (by
        intro i hi
        exact hband length hmem i hi) x
    simpa [K, core, allowed, ProbabilityTheory.RandomWalk.returnKernel] using h
  intro x
  have hproduct :=
    ProbabilityTheory.Kernel.pow_le_returnKernelSequence_apply_univ
      K core measurableSet_Icc lengths lowerBound hrow x
  have hdom := ProbabilityTheory.Kernel.returnKernelSequence_apply_preimage_le
    K core measurableSet_Icc lengths x Set.univ MeasurableSet.univ
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

/-- If every return window has lower bound `p` for both adjacent block
lengths, a balanced partition of the horizon gives the product bound. -/
theorem iidSequenceLaw_staysIn_ge_pow_of_balancedEndpointWindowReturnBlocks
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {lower upper spacing windowRadius : ℝ}
    (hspacing : 0 < spacing) (hwindow : 0 < windowRadius)
    (hwindowLe : windowRadius ≤ 2 * spacing)
    (total referenceLength : ℕ)
    (hcount : 0 < Combinatorics.Sequence.balancedBlockCount total referenceLength)
    (lowerBound : ENNReal)
    (hshort : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowReturnBlockEvent lower upper spacing windowRadius i
          (Combinatorics.Sequence.balancedBlockShortLength total referenceLength)))
    (hlong : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowReturnBlockEvent lower upper spacing windowRadius i
          (Combinatorics.Sequence.balancedBlockShortLength total referenceLength + 1))) :
    ∀ x : Set.Icc (-3 * spacing) (3 * spacing),
      lowerBound ^ Combinatorics.Sequence.balancedBlockCount total referenceLength ≤
        iidSequenceLaw ν
          {increment | StaysIn (Set.Icc lower upper) total (x : ℝ) increment} := by
  let lengths := Combinatorics.Sequence.balancedBlockLengths total referenceLength
  have hband : ∀ length ∈ lengths, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowReturnBlockEvent lower upper spacing windowRadius i length) := by
    intro length hmem i hi
    rcases Combinatorics.Sequence.mem_balancedBlockLengths hmem with h | h
    · simpa [h] using hshort i hi
    · simpa [h] using hlong i hi
  have hsequence := iidSequenceLaw_staysIn_ge_pow_of_endpointWindowReturnBlockSequence
    ν hspacing hwindow hwindowLe lengths lowerBound hband
  have hlength : lengths.length =
      Combinatorics.Sequence.balancedBlockCount total referenceLength := by
    simpa [lengths] using Combinatorics.Sequence.balancedBlockLengths_length hcount
  have htotal : ProbabilityTheory.Kernel.returnKernelSequenceLength lengths = total := by
    rw [ProbabilityTheory.Kernel.returnKernelSequenceLength_eq_sum]
    simpa [lengths] using Combinatorics.Sequence.balancedBlockLengths_sum hcount
  intro x
  simpa [hlength, htotal] using hsequence x

/-- Endpoint-window return bounds iterate to the horizontal tube with the
outer corridor enlarged by the core radius and window half-width. -/
theorem horizontalTubeProbability_ge_pow_endpointWindows
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius spacing windowRadius : ℝ}
    (hspacing : 0 < spacing) (hwindow : 0 < windowRadius)
    (hwindowLe : windowRadius ≤ 2 * spacing)
    (blocks length : ℕ) (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowBlockEvent radius spacing windowRadius i length)) :
    lowerBound ^ blocks ≤
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
        (2 * (radius + 3 * spacing + windowRadius)) (blocks * length) := by
  have hrow := returnKernel_apply_univ_lower_of_endpointWindowEvents
    ν hspacing hwindow hwindowLe length lowerBound hband
  have hallowed :
      Set.Icc (-(radius + 3 * spacing + windowRadius))
          (radius + 3 * spacing + windowRadius) =
        Set.Icc (2 * (radius + 3 * spacing + windowRadius) * (-(1 / 2 : ℝ)))
          (2 * (radius + 3 * spacing + windowRadius) * (1 - 1 / 2 : ℝ)) := by
    congr 1 <;> ring
  have hrow' : ∀ x : Set.Icc (-3 * spacing) (3 * spacing),
      lowerBound ≤ Kernel.returnKernel
        (killedIncrementKernel ν
          (Set.Icc (2 * (radius + 3 * spacing + windowRadius) * (-(1 / 2 : ℝ)))
            (2 * (radius + 3 * spacing + windowRadius) * (1 - 1 / 2 : ℝ)))
          measurableSet_Icc)
        (Set.Icc (-3 * spacing) (3 * spacing)) measurableSet_Icc
        length x univ := by
    intro x
    have hx := hrow x
    change lowerBound ≤ Kernel.returnKernel
      (killedIncrementKernel ν
        (Set.Icc (-(radius + 3 * spacing + windowRadius))
          (radius + 3 * spacing + windowRadius)) measurableSet_Icc)
      (Set.Icc (-3 * spacing) (3 * spacing)) measurableSet_Icc
      length x univ at hx
    simpa only [hallowed] using hx
  have hmain := horizontalTubeProbability_ge_pow_returnBlock ν
    (a := (1 / 2 : ℝ))
    (width := 2 * (radius + 3 * spacing + windowRadius))
    (returnSet := Set.Icc (-3 * spacing) (3 * spacing)) measurableSet_Icc
    (by
      change -3 * spacing ≤ 0 ∧ 0 ≤ 3 * spacing
      constructor <;> nlinarith [hspacing])
    lowerBound blocks length hrow'
  simpa [mul_assoc] using hmain

/-- A tube bound from complete endpoint-window return blocks also bounds every
shorter horizon, since confinement on the longer path implies confinement on
its prefix. -/
theorem horizontalTubeProbability_ge_pow_endpointWindows_of_horizon_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius spacing windowRadius : ℝ}
    (hspacing : 0 < spacing) (hwindow : 0 < windowRadius)
    (hwindowLe : windowRadius ≤ 2 * spacing)
    (blocks length horizon : ℕ) (hcover : horizon ≤ blocks * length)
    (lowerBound : ENNReal)
    (hband : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ iidSequenceLaw ν
        (endpointWindowBlockEvent radius spacing windowRadius i length)) :
    lowerBound ^ blocks ≤ horizontalTubeProbability (iidSequenceLaw ν)
      (1 / 2) (2 * (radius + 3 * spacing + windowRadius)) horizon := by
  exact (horizontalTubeProbability_ge_pow_endpointWindows
      ν hspacing hwindow hwindowLe blocks length lowerBound hband).trans
    (horizontalTubeProbability_mono_horizon (iidSequenceLaw ν) (1 / 2)
      (2 * (radius + 3 * spacing + windowRadius)) hcover)

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

end
