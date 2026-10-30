/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Process.RandomWalk.Path.Window.Basic
import Probability.Process.RandomWalk.Path.Block.Corridor.Measure
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic

/-!
# Translated endpoint bridges for finite horizontal tubes

## Public declarations

The general mesh and endpoint-window events belong to
`ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow`.
This module owns their translated bridge geometry:

* `endpointCorridorBlockEvent lower upper endpointLower endpointUpper length`
  requires every partial sum in $(\mathrm{lower},\mathrm{upper})$ and the
  terminal sum in $(\mathrm{endpointLower},\mathrm{endpointUpper})$.
  `endpointCorridorBridgeBlockEvent allowedLower allowedUpper ε s t i length`
  uses the relative corridor
  $(\mathrm{allowedLower}+4\varepsilon-s,
  \mathrm{allowedUpper}-4\varepsilon-s)$ and endpoint band
  $(t-s+(i-1)\varepsilon,t-s+(i+1)\varepsilon)$.
* `endpointWindowReturnBlockEvent_eq_endpointCorridorBridgeBlockEvent` links
  a same-center return window to its translated bridge form, and
  `endpointCorridorBridgeBlockEvent_scale` scales every spatial parameter
  together.
* `measurableSet_endpointCorridorBlockEvent` and
  `measurableSet_endpointCorridorBridgeBlockEvent` prove measurability of the
  bridge events on the product space of increment sequences.
* `endpointCorridorBridgeBlockEvent_subset_killedBridgeEvent` states that if
  $\varepsilon>0$, $x\in[s-3\varepsilon,s+3\varepsilon]$, and
  $x-s+i\varepsilon\in[0,\varepsilon]$, then the bridge event with
  allowed corridor $[\mathrm{lower},\mathrm{upper}]$ implies that the walk
  stays in this corridor and ends in $[t-3\varepsilon,t+3\varepsilon]$.

The seven integer shifts covering the return core supply the endpoint choice
in Lemma 3(d) of A. A. Mogul'skii; the full bibliographic reference follows.

The original bibliography is A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081. -/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand

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

/-- A same-center bridge is the endpoint-window return event with equal mesh
spacing and window half-width. -/
theorem endpointWindowReturnBlockEvent_eq_endpointCorridorBridgeBlockEvent
    (allowedLower allowedUpper epsilon sourceCenter : ℝ) (i : ℤ)
    (length : ℕ) :
    ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.endpointWindowReturnBlockEvent
        (allowedLower - sourceCenter) (allowedUpper - sourceCenter)
        epsilon epsilon i length =
      endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilon
        sourceCenter sourceCenter i length := by
  ext increment
  simp only [ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.endpointWindowReturnBlockEvent,
    endpointCorridorBridgeBlockEvent,
    endpointCorridorBlockEvent, Set.mem_ofPred_eq]
  rw [show allowedLower - sourceCenter + 3 * epsilon + epsilon =
      allowedLower + 4 * epsilon - sourceCenter by ring,
    show allowedUpper - sourceCenter - 3 * epsilon - epsilon =
      allowedUpper - 4 * epsilon - sourceCenter by ring,
    show (i : ℝ) * epsilon - epsilon =
      sourceCenter - sourceCenter + ((i : ℝ) - 1) * epsilon by ring,
    show (i : ℝ) * epsilon + epsilon =
      sourceCenter - sourceCenter + ((i : ℝ) + 1) * epsilon by ring]

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

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand
