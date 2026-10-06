/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Restart.Windows
public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.Path.Window

/-!
# Laws of restarted walk paths

The deterministic restarted event splits at its cutoff.  Under the canonical
IID increment law, the two resulting finite coordinate blocks are
independent, so their probabilities multiply.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk


/-- Probability of a restarted-window event under an increment-path law. -/
def restartedWindowProbability
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (n : ℕ) (initial : ℝ) : ENNReal :=
  incrementLaw {increment | InRestartedWindows cutoff window
    (history n initial increment)}

/-- Restarted-window membership and probability are invariant under
translation of the absolute initial position. -/
theorem restartedWindowProbability_eq_zeroInitial
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (n : ℕ) (initial : ℝ) :
    restartedWindowProbability incrementLaw cutoff window n initial =
      restartedWindowProbability incrementLaw cutoff window n 0 := by
  unfold restartedWindowProbability
  congr 1
  ext increment
  exact inRestartedWindows_history_iff cutoff window initial increment

/-- Under the canonical IID law, closed-interval events on two consecutive
finite increment blocks have product probability. -/
theorem iidSequenceLaw_measure_inClosedInterval_and_shift
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper : ℝ) (cutoff tail : ℕ) :
    iidSequenceLaw ν {increment |
        InClosedInterval lower upper cutoff 0 increment ∧
          InClosedInterval lower upper tail 0
            (fun k => increment (cutoff + k))} =
      iidSequenceLaw ν {increment |
          InClosedInterval lower upper cutoff 0 increment} *
        iidSequenceLaw ν {increment |
          InClosedInterval lower upper tail 0 increment} := by
  let prefixEvent : Set (Fin cutoff → ℝ) :=
    {increment | FiniteInClosedInterval lower upper 0 increment}
  let tailEvent : Set (Fin tail → ℝ) :=
    {increment | FiniteInClosedInterval lower upper 0 increment}
  have hprefix : MeasurableSet prefixEvent :=
    measurableSet_finiteInClosedInterval lower upper 0 cutoff
  have htail : MeasurableSet tailEvent :=
    measurableSet_finiteInClosedInterval lower upper 0 tail
  have hindep := indepFun_blockCoordinates_blockCoordinates
    (E := ℝ) ν 0 cutoff tail
  have hproduct := hindep.measure_inter_preimage_eq_mul
    prefixEvent tailEvent hprefix htail
  have hprefixPreimage :
      Combinatorics.Sequence.blockCoordinates (E := ℝ) 0 cutoff ⁻¹' prefixEvent =
        {increment | InClosedInterval lower upper cutoff 0 increment} := by
    ext increment
    change FiniteInClosedInterval lower upper 0
        (Combinatorics.Sequence.blockCoordinates 0 cutoff increment) ↔
      InClosedInterval lower upper cutoff 0 increment
    simpa using
      finiteInClosedInterval_blockCoordinates_iff
        lower upper 0 0 cutoff increment
  have htailPreimage :
      Combinatorics.Sequence.blockCoordinates (E := ℝ) cutoff tail ⁻¹' tailEvent =
        {increment | InClosedInterval lower upper tail 0
          (fun k => increment (cutoff + k))} := by
    ext increment
    change FiniteInClosedInterval lower upper 0
        (Combinatorics.Sequence.blockCoordinates cutoff tail increment) ↔
      InClosedInterval lower upper tail 0
        (fun k => increment (cutoff + k))
    exact finiteInClosedInterval_blockCoordinates_iff
      lower upper 0 cutoff tail increment
  rw [Nat.zero_add, hprefixPreimage, htailPreimage] at hproduct
  rw [show {increment : ℕ → ℝ |
        InClosedInterval lower upper cutoff 0 increment ∧
          InClosedInterval lower upper tail 0
            (fun k => increment (cutoff + k))} =
      {increment | InClosedInterval lower upper cutoff 0 increment} ∩
        {increment | InClosedInterval lower upper tail 0
          (fun k => increment (cutoff + k))} by ext; simp]
  rw [hproduct]
  congr 1
  let shift : (ℕ → ℝ) → (ℕ → ℝ) :=
    fun increment k => increment (cutoff + k)
  have hmap := iidSequenceLaw_map_natAdd ν cutoff
  have hevent := measurableSet_inClosedInterval lower upper tail 0
  have hshift : Measurable shift := measurable_natAdd cutoff
  rw [show iidSequenceLaw ν {increment |
        InClosedInterval lower upper tail 0
          (fun k => increment (cutoff + k))} =
      (iidSequenceLaw ν).map shift
        {increment | InClosedInterval lower upper tail 0 increment} by
    rw [Measure.map_apply hshift hevent]
    rfl]
  rw [hmap]

/-- For a constant closed interval under the canonical IID increment law, a
restarted-window probability is the product of the zero-started prefix and
tail probabilities. -/
theorem restartedWindowProbability_Icc_add_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower upper : ℝ) (cutoff tail : ℕ) (initial : ℝ) :
    restartedWindowProbability (iidSequenceLaw ν) cutoff
        (fun _ => Set.Icc lower upper) (cutoff + tail) initial =
      iidSequenceLaw ν {increment |
          InClosedInterval lower upper cutoff 0 increment} *
        iidSequenceLaw ν {increment |
          InClosedInterval lower upper tail 0 increment} := by
  rw [restartedWindowProbability_eq_zeroInitial]
  unfold restartedWindowProbability
  rw [show {increment : ℕ → ℝ |
        InRestartedWindows cutoff (fun _ => Set.Icc lower upper)
          (history (cutoff + tail) 0 increment)} =
      {increment |
        InClosedInterval lower upper cutoff 0 increment ∧
          InClosedInterval lower upper tail 0
            (fun k => increment (cutoff + k))} by
    ext increment
    exact inRestartedWindows_Icc_add_iff
      lower upper cutoff tail 0 increment]
  exact iidSequenceLaw_measure_inClosedInterval_and_shift
    ν lower upper cutoff tail

end ProbabilityTheory.RandomWalk
