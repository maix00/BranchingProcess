/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Probability.Process.RandomWalk.Kernel.Killed.Return
public import Probability.Process.RandomWalk.Path.Window
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.Horizontal

/-!
# Finite endpoint bands for the horizontal lower block bound

This is the discrete endpoint-band construction in Mogulskii's Lemma 3(d).
The finite indices `-3, ..., 3` compensate for the current position inside
the return core.  Once one-block lower bounds for these seven events are
available, a killed-walk return kernel iterates them without any forced
entrance path.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- A block stays in the open interval `(-radius, radius)` and its final
displacement lies in a band of width `2 ε` centered at the shift `i ε`. -/
def endpointBandBlockEvent (radius ε : ℝ) (i : ℤ) (length : ℕ) : Set (ℕ → ℝ) :=
  {increment | InOpenHorizontalTube (1 / 2) (2 * radius) length increment ∧
    AdditivePath.displacement length increment ∈
      Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)}

/-- The endpoint-band block event is measurable in the IID increment path. -/
theorem measurableSet_endpointBandBlockEvent (radius ε : ℝ) (i : ℤ)
    (length : ℕ) :
    MeasurableSet (endpointBandBlockEvent radius ε i length) := by
  exact (ProbabilityTheory.RandomWalk.measurableSet_inOpenHorizontalTube
      (1 / 2) (2 * radius) length).inter
    (measurableSet_Ioo.preimage (displacement_measurable length))

/-- Every point in the return core is within one band width of one of the
seven integer shifts used by the lower block comparison. -/
theorem exists_nearbyEndpointBandIndex {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Set.Icc (-3 * ε) (3 * ε)) :
    ∃ i ∈ Finset.Icc (-3 : ℤ) 3,
      x + (i : ℝ) * ε ∈ Set.Icc 0 ε := by
  let t : ℝ := x / ε + 3
  let j : ℕ := ⌊t⌋₊
  let i : ℤ := 3 - (j : ℤ)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    have hxdiv : -3 ≤ x / ε := (le_div_iff₀ hε).2 (by nlinarith [hx.1])
    linarith
  have ht6 : t ≤ 6 := by
    dsimp [t]
    have hxdiv : x / ε ≤ 3 := (div_le_iff₀ hε).2 (by nlinarith [hx.2])
    linarith
  have hjle : (j : ℝ) ≤ t := by
    dsimp [j]
    exact Nat.floor_le ht0
  have htlt : t < (j : ℝ) + 1 := by
    dsimp [j]
    exact Nat.lt_floor_add_one t
  have hjle6 : j ≤ 6 := by
    have hcast : (j : ℝ) ≤ 6 := hjle.trans ht6
    exact_mod_cast hcast
  refine ⟨i, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    constructor <;> dsimp [i] <;> omega
  · have hcast : (i : ℝ) = 3 - (j : ℝ) := by
      simp [i]
    rw [hcast]
    have hidentity : x + (3 - (j : ℝ)) * ε = ε * (t - (j : ℝ)) := by
      dsimp [t]
      field_simp [hε.ne']
      ring
    rw [hidentity]
    have hrem0 : 0 ≤ t - (j : ℝ) := by linarith
    have hrem1 : t - (j : ℝ) ≤ 1 := by linarith
    constructor
    · exact mul_nonneg hε.le hrem0
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hrem1 hε.le

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
  have hstay' :
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
  exact ⟨hstay', hend'⟩

/-- The seven endpoint-band estimates in Mogulskii's lower block comparison
give a uniform one-block transition from the return core back to itself. -/
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
