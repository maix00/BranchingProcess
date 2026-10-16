/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Probability.Process.RandomWalk.Kernel.Killed.Bridge
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.Path.Window.Core
public import Probability.Process.RandomWalk.Path.Block.Corridor.Measure

/-!
# Finite endpoint bands for the horizontal lower block bound

The public definitions and theorems in this file are:

- `endpointBandBlockEvent` and `endpointBandReturnBlockEvent`:
  a block stays inside a horizontal corridor and has terminal displacement
  in $((i-1)\varepsilon,(i+1)\varepsilon)$ for $i\in\mathbb Z$;
  the return event contracts an asymmetric corridor by $4\varepsilon$.
- `endpointCorridorBlockEvent` and `endpointCorridorBridgeBlockEvent`:
  the same block event with arbitrary open corridor and endpoint interval,
  translated from source center $s$ to target center $t$.
- `endpointBandReturnBlockEvent_eq_endpointCorridorBridgeBlockEvent`
  and `endpointCorridorBridgeBlockEvent_scale`:
  same-center return events are bridge events, and simultaneous scaling
  of all spatial parameters agrees with scaling the corridor and endpoint.
- `measurableSet_endpointBandReturnBlockEvent`,
  `measurableSet_endpointCorridorBlockEvent`,
  `measurableSet_endpointCorridorBridgeBlockEvent`, and
  `measurableSet_endpointBandBlockEvent`:
  measurability of the four finite block events.
- `endpointCorridorBridgeBlockEvent_subset_killedBridgeEvent`:
  the contracted open bridge event lies inside the corresponding closed
  killed-walk bridge event.
- `exists_nearbyEndpointBandIndex`:
  $x\in[-3\varepsilon,3\varepsilon]$ gives an integer
  $i\in[-3,3]$ with $x+i\varepsilon\in[0,\varepsilon]$.

These seven endpoint shifts give the finite geometry in Mogul'skii,
*Small Deviations in a Space of Trajectories*, Lemma 3(d).


The original bibliography is A. A. Mogul'skii, “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(1) (1975), 726--736, DOI 10.1137/1119081. -/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- A block stays in the open interval `(-radius, radius)` and its final
displacement lies in a band of width `2 ε` centered at the shift `i ε`. -/
def endpointBandBlockEvent (radius ε : ℝ) (i : ℤ) (length : ℕ) : Set (ℕ → ℝ) :=
  {increment | InOpenHorizontalTube (1 / 2) (2 * radius) length increment ∧
    AdditivePath.displacement length increment ∈
      Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)}

/-- A shifted and possibly asymmetric corridor version of an endpoint-band
block. `lower` and `upper` describe the state corridor in which the walk is
to survive; the increment path is contracted by `4 * ε` so that any starting
state in the return core remains inside it. -/
def endpointBandReturnBlockEvent (lower upper ε : ℝ) (i : ℤ) (length : ℕ) :
    Set (ℕ → ℝ) :=
  {increment | InOpenPartialSumCorridor (lower + 4 * ε) (upper - 4 * ε)
      (Combinatorics.Sequence.blockCoordinates 0 length increment) ∧
    Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment)
        (Fin.last length) ∈ Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)}

/-- A finite block stays in an open partial-sum corridor and ends in an
arbitrary open displacement interval. This is the bridge-event form used when
the incoming and outgoing endpoint cores have different centers. -/
def endpointCorridorBlockEvent (lower upper endpointLower endpointUpper : ℝ)
    (length : ℕ) : Set (ℕ → ℝ) :=
  {increment | InOpenPartialSumCorridor lower upper
      (Combinatorics.Sequence.blockCoordinates 0 length increment) ∧
    Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment)
      (Fin.last length) ∈ Set.Ioo endpointLower endpointUpper}

/-- A translated bridge event for a block that starts near `sourceCenter`,
stays in a contracted allowed corridor, and ends near `targetCenter`. The
integer index selects one of finitely many endpoint windows. -/
def endpointCorridorBridgeBlockEvent (allowedLower allowedUpper epsilon
    sourceCenter targetCenter : ℝ) (i : ℤ) (length : ℕ) : Set (ℕ → ℝ) :=
  endpointCorridorBlockEvent
    (allowedLower + 4 * epsilon - sourceCenter)
    (allowedUpper - 4 * epsilon - sourceCenter)
    (targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon)
    (targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon)
    length

/-- A same-center bridge is exactly the translated endpoint-band return
event. -/
theorem endpointBandReturnBlockEvent_eq_endpointCorridorBridgeBlockEvent
    (allowedLower allowedUpper epsilon sourceCenter : ℝ) (i : ℤ)
    (length : ℕ) :
    endpointBandReturnBlockEvent (allowedLower - sourceCenter)
        (allowedUpper - sourceCenter) epsilon i length =
      endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilon
        sourceCenter sourceCenter i length := by
  ext increment
  simp only [endpointBandReturnBlockEvent, endpointCorridorBridgeBlockEvent,
    endpointCorridorBlockEvent, Set.mem_ofPred_eq]
  rw [show allowedLower - sourceCenter + 4 * epsilon =
      allowedLower + 4 * epsilon - sourceCenter by ring,
    show allowedUpper - sourceCenter - 4 * epsilon =
      allowedUpper - 4 * epsilon - sourceCenter by ring]
  simp

/-- Scaling all spatial coordinates of a bridge event scales its relative
corridor and endpoint interval by the same positive or negative factor. -/
theorem endpointCorridorBridgeBlockEvent_scale
    (allowedLower allowedUpper epsilon sourceCenter targetCenter scale : ℝ)
    (i : ℤ) (length : ℕ) :
    endpointCorridorBridgeBlockEvent
        (allowedLower * scale) (allowedUpper * scale) (epsilon * scale)
        (sourceCenter * scale) (targetCenter * scale) i length =
      endpointCorridorBlockEvent
        ((allowedLower + 4 * epsilon - sourceCenter) * scale)
        ((allowedUpper - 4 * epsilon - sourceCenter) * scale)
        ((targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon) * scale)
        ((targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon) * scale)
        length := by
  ext increment
  simp only [endpointCorridorBridgeBlockEvent, endpointCorridorBlockEvent,
    Set.mem_ofPred_eq]
  rw [show allowedLower * scale + 4 * (epsilon * scale) - sourceCenter * scale =
      (allowedLower + 4 * epsilon - sourceCenter) * scale by ring,
    show allowedUpper * scale - 4 * (epsilon * scale) - sourceCenter * scale =
      (allowedUpper - 4 * epsilon - sourceCenter) * scale by ring,
    show targetCenter * scale - sourceCenter * scale + ((i : ℝ) - 1) *
        (epsilon * scale) =
      (targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon) * scale by ring,
    show targetCenter * scale - sourceCenter * scale + ((i : ℝ) + 1) *
        (epsilon * scale) =
      (targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon) * scale by ring]

/-- The shifted endpoint-band event is measurable in the product sigma
algebra on the IID increment coordinates. -/
theorem measurableSet_endpointBandReturnBlockEvent
    (lower upper ε : ℝ) (i : ℤ) (length : ℕ) :
    MeasurableSet (endpointBandReturnBlockEvent lower upper ε i length) := by
  let coordinates : (ℕ → ℝ) → (Fin length → ℝ) :=
    fun increment => Combinatorics.Sequence.blockCoordinates 0 length increment
  have hcoordinates : Measurable coordinates := by
    apply Measurable.of_eval
    intro k
    change Measurable (fun increment : ℕ → ℝ => increment (0 + (k : ℕ)))
    simpa using (measurable_pi_apply (k : ℕ))
  change MeasurableSet (coordinates ⁻¹'
    {block : Fin length → ℝ |
      InOpenPartialSumCorridorEndsIn (lower + 4 * ε) (upper - 4 * ε)
        (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε) block})
  exact (measurableSet_inOpenPartialSumCorridorEndsIn _ _ _ _).preimage
    hcoordinates

/-- Measurability of a block event with an arbitrary open displacement band. -/
theorem measurableSet_endpointCorridorBlockEvent
    (lower upper endpointLower endpointUpper : ℝ) (length : ℕ) :
    MeasurableSet
      (endpointCorridorBlockEvent lower upper endpointLower endpointUpper length) := by
  let coordinates : (ℕ → ℝ) → (Fin length → ℝ) :=
    fun increment => Combinatorics.Sequence.blockCoordinates 0 length increment
  have hcoordinates : Measurable coordinates := by
    apply Measurable.of_eval
    intro k
    change Measurable (fun increment : ℕ → ℝ => increment (0 + (k : ℕ)))
    simpa using (measurable_pi_apply (k : ℕ))
  change MeasurableSet (coordinates ⁻¹'
    {block : Fin length → ℝ |
      InOpenPartialSumCorridorEndsIn lower upper endpointLower endpointUpper block})
  exact (measurableSet_inOpenPartialSumCorridorEndsIn _ _ _ _).preimage
    hcoordinates

/-- Measurability of a translated bridge event. -/
theorem measurableSet_endpointCorridorBridgeBlockEvent
    (allowedLower allowedUpper epsilon sourceCenter targetCenter : ℝ)
    (i : ℤ) (length : ℕ) :
    MeasurableSet
      (endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilon
        sourceCenter targetCenter i length) := by
  exact measurableSet_endpointCorridorBlockEvent _ _ _ _ _

/-- A translated endpoint-window event gives a killed-walk bridge between two
equal-radius cores. -/
theorem endpointCorridorBridgeBlockEvent_subset_killedBridgeEvent
    {allowedLower allowedUpper epsilon sourceCenter targetCenter x : ℝ}
    {i : ℤ} {length : ℕ} (hepsilon : 0 < epsilon)
    (hstart : x ∈ Set.Icc (sourceCenter - 3 * epsilon)
      (sourceCenter + 3 * epsilon))
    (hnear : x - sourceCenter + (i : ℝ) * epsilon ∈ Set.Icc 0 epsilon)
    (increment : ℕ → ℝ)
    (hevent : increment ∈ endpointCorridorBridgeBlockEvent
      allowedLower allowedUpper epsilon sourceCenter targetCenter i length) :
    RandomWalk.StaysIn (Set.Icc allowedLower allowedUpper) length x increment ∧
      x + AdditivePath.displacement length increment ∈
        Set.Icc (targetCenter - 3 * epsilon) (targetCenter + 3 * epsilon) := by
  rcases hevent with ⟨hpath, hend⟩
  have hstay : RandomWalk.StaysIn (Set.Icc allowedLower allowedUpper)
      length x increment := by
    intro k
    have hk := hpath k.succ
    have hsum :
        Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment)
          k.succ = AdditivePath.displacement (k + 1) increment := by
      rw [RandomWalk.partialSum_blockCoordinates,
        AdditivePath.blockSum_eq_displacement_natAdd]
      simp
    rw [hsum] at hk
    rcases hk with ⟨hklo, hkhi⟩
    rcases hstart with ⟨hstartlo, hstarthi⟩
    change x + AdditivePath.displacement (k + 1) increment ∈
      Set.Icc allowedLower allowedUpper
    constructor
    · nlinarith [hstartlo, hklo]
    · nlinarith [hstarthi, hkhi]
  have hlast :
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 length increment)
        (Fin.last length) = AdditivePath.displacement length increment := by
    rw [RandomWalk.partialSum_blockCoordinates,
      AdditivePath.blockSum_eq_displacement_natAdd]
    simp
  rw [hlast] at hend
  rcases hend with ⟨hendlo, hendhi⟩
  rcases hnear with ⟨hnearlo, hnearhi⟩
  have htargetlo : targetCenter - 3 * epsilon ≤
      x + AdditivePath.displacement length increment := by
    have hbandlo :
        targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon =
          targetCenter - sourceCenter + (i : ℝ) * epsilon - epsilon := by ring
    rw [hbandlo] at hendlo
    nlinarith [hnearlo]
  have htargethi : x + AdditivePath.displacement length increment ≤
      targetCenter + 3 * epsilon := by
    have hbandhi :
        targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon =
          targetCenter - sourceCenter + (i : ℝ) * epsilon + epsilon := by ring
    rw [hbandhi] at hendhi
    nlinarith [hnearhi]
  exact ⟨hstay, ⟨htargetlo, htargethi⟩⟩

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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
