/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.EndpointBands

/-!
# Endpoint windows with separate mesh and width

The lattice used to select a return band and the half-width of that band are
independent parameters.  This distinction is needed when a weak-limit
Portmanteau argument enlarges the endpoint window while keeping the return
core mesh fixed.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

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

/-- The return event for an endpoint window.  The incoming core radius is
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

private theorem endpointWindowBlockEvent_subset_returnEvent
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
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointBandIndex hspacing x.property
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
