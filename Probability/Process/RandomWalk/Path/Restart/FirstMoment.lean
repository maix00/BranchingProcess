/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Process.RandomWalk.Path.Restart.Basic
public import Probability.Process.RandomWalk.Path.Restart.Corridor
public import Probability.Process.Path.Restart.Basic
import Probability.Process.Path.Restart.Measurability
import Probability.Process.Path.Restart.Bounds

/-!
# First moments of restarted-window path events

These definitions concern a random walk's finite real-valued history and do
not depend on a branching realization. A restarted window compares each path
coordinate with the coordinate selected by a deterministic anchor schedule.

## Public declarations

- `ProbabilityTheory.RandomWalk.restartedWindowTest` and
  `restartedWindowTest_measurable`: define the real-valued finite-history
  event indicator and establish its measurability.
- `ProbabilityTheory.RandomWalk.restartedWindowFirstMoment`,
  `restartedWindowFirstMoment_le`, `HasRestartedWindowFirstMomentBound`,
  `hasRestartedWindowFirstMomentBound_of_probability`,
  `hasRestartedWindowFirstMomentBound_of_zero_probability`, and
  `hasRestartedWindowFirstMomentBound_horizontal`: define the associated
  first-moment event bound and derive it from probability and horizontal-window
  estimates.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory.Process.Path

/-- Indicator of the restarted path-window event, in the codomain used by
path-functional many-to-one identities. -/
noncomputable def restartedWindowTest {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set ℝ) : (Fin (n + 1) → ℝ) → ENNReal :=
  {history | InRestartedWindows cutoff window history}.indicator fun _ => 1

theorem restartedWindowTest_measurable {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k)) :
    Measurable (restartedWindowTest (n := n) cutoff window) :=
  measurable_const.indicator
    (measurableSet_inRestartedWindows cutoff window hwindow)

/-- A restarted-window path has a deterministic upper bound on its final
displacement.  Before the cutoff this is the current window bound; after the
cutoff it is the sum of the cutoff displacement bound and the bound relative
to the cutoff anchor. -/
private lemma displacement_le_of_inRestartedWindows {n : ℕ}
    (cutoff : ℕ) (window : ℕ → Set ℝ) (upper : ℕ → ℝ)
    (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (initial : ℝ) (increment : ℕ → ℝ)
    (hwindow : InRestartedWindows cutoff window
      (history n initial increment)) :
    AdditivePath.displacement n increment ≤
      if n ≤ cutoff then upper n else upper cutoff + upper n := by
  simpa [history_apply, history_zero, AdditivePath.displacement_zero] using
    endpoint_sub_start_le_of_inRestartedWindows cutoff window upper hupper
      (history n initial increment) hwindow

@[simp] theorem restartedWindowTest_eq_one_iff {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set ℝ) (history : Fin (n + 1) → ℝ) :
    restartedWindowTest cutoff window history = 1 ↔
      InRestartedWindows cutoff window history := by
  simp [restartedWindowTest]

@[simp] theorem restartedWindowTest_eq_zero_iff {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set ℝ) (history : Fin (n + 1) → ℝ) :
    restartedWindowTest cutoff window history = 0 ↔
      ¬InRestartedWindows cutoff window history := by
  simp [restartedWindowTest]

/-- The exponentially weighted first moment of a real increment path confined
to restarted windows. This is a one-dimensional object: it depends only on
the law of the increment path and contains no branching or root-index data.

For the tilted increment law it is exactly the analytic quantity left by the
path many-to-one formula. -/
noncomputable def restartedWindowFirstMoment
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (n : ℕ) (initial : ℝ) : ENNReal :=
  ∫⁻ increment,
    ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
      restartedWindowTest cutoff window
        (history n initial increment) ∂incrementLaw

/-- The exponential first moment in restarted windows is bounded by the
ordinary window probability times the deterministic maximal endpoint weight.
This is the bridge from Mogulskii probability estimates to the first-moment
interface used by the killed branching population. -/
theorem restartedWindowFirstMoment_le
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (n : ℕ) (initial : ℝ) :
    restartedWindowFirstMoment incrementLaw cutoff window n initial ≤
      ENNReal.ofReal (Real.exp
        (if n ≤ cutoff then upper n else upper cutoff + upper n)) *
        restartedWindowProbability incrementLaw cutoff window n initial := by
  let event : Set (ℕ → ℝ) :=
    {increment | InRestartedWindows cutoff window
      (history n initial increment)}
  have hevent : MeasurableSet event :=
    (measurableSet_inRestartedWindows cutoff window hwindow).preimage
      (history_measurable n initial)
  unfold restartedWindowFirstMoment restartedWindowProbability
  calc
    (∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          restartedWindowTest cutoff window
            (history n initial increment) ∂incrementLaw) ≤
        ∫⁻ increment in event,
          ENNReal.ofReal (Real.exp
            (if n ≤ cutoff then upper n else upper cutoff + upper n))
          ∂incrementLaw := by
      rw [show (fun increment =>
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            restartedWindowTest cutoff window
              (history n initial increment)) =
          event.indicator (fun increment =>
            ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment))) by
        funext increment
        by_cases hincrement : increment ∈ event
        · have hprop : InRestartedWindows cutoff window
              (history n initial increment) := by
            simpa [event] using hincrement
          have hcanonical : InRestartedWindows (n := n) cutoff window
              (fun k : Fin (n + 1) =>
                initial + AdditivePath.displacement k increment) := by
            simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hprop
          simp [restartedWindowTest, hcanonical, hincrement]
        · have hnot : ¬InRestartedWindows cutoff window
              (history n initial increment) := by
            simpa [event] using hincrement
          have hcanonical : ¬InRestartedWindows (n := n) cutoff window
              (fun k : Fin (n + 1) =>
                initial + AdditivePath.displacement k increment) := by
            simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hnot
          simp [restartedWindowTest, hcanonical, hincrement]]
      rw [MeasureTheory.lintegral_indicator hevent]
      apply MeasureTheory.setLIntegral_mono measurable_const
      intro increment hincrement
      have hsum := displacement_le_of_inRestartedWindows cutoff window upper
        hupper initial increment hincrement
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hsum)
    _ = _ := by
      rw [MeasureTheory.setLIntegral_const]

/-- A time-dependent bound for the restarted-window first moment, uniform
over the stated set of initial positions. This is the interface supplied by
a random-walk tube estimate. -/
def HasRestartedWindowFirstMomentBound
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (initial : Set ℝ)
    (bound : ℕ → ENNReal) : Prop :=
  ∀ n x, x ∈ initial →
    restartedWindowFirstMoment incrementLaw cutoff window n x ≤ bound n

/-- Any uniform probability estimate for the restarted windows supplies the
first-moment bound needed by the killed branching population, after inserting
the deterministic exponential endpoint factor. -/
theorem hasRestartedWindowFirstMomentBound_of_probability
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (initial : Set ℝ) (probabilityBound : ℕ → ENNReal)
    (hprobability : ∀ n x, x ∈ initial →
      restartedWindowProbability incrementLaw cutoff window n x ≤
        probabilityBound n) :
    HasRestartedWindowFirstMomentBound incrementLaw cutoff window initial
      (fun n => ENNReal.ofReal (Real.exp
          (if n ≤ cutoff then upper n else upper cutoff + upper n)) *
        probabilityBound n) := by
  intro n x hx
  calc
    restartedWindowFirstMoment incrementLaw cutoff window n x ≤
        ENNReal.ofReal (Real.exp
          (if n ≤ cutoff then upper n else upper cutoff + upper n)) *
          restartedWindowProbability incrementLaw cutoff window n x :=
      restartedWindowFirstMoment_le incrementLaw cutoff window hwindow
        upper hupper n x
    _ ≤ ENNReal.ofReal (Real.exp
          (if n ≤ cutoff then upper n else upper cutoff + upper n)) *
          probabilityBound n := by
      simpa [mul_comm] using mul_le_mul_left (hprobability n x hx)
        (ENNReal.ofReal (Real.exp
          (if n ≤ cutoff then upper n else upper cutoff + upper n)))

/-- It suffices to prove the restarted-window probability estimate for a
walk started at zero; translation invariance makes the resulting first-moment
bound uniform over every requested initial position. -/
theorem hasRestartedWindowFirstMomentBound_of_zero_probability
    (incrementLaw : Measure (ℕ → ℝ)) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (initial : Set ℝ) (probabilityBound : ℕ → ENNReal)
    (hprobability : ∀ n,
      restartedWindowProbability incrementLaw cutoff window n 0 ≤
        probabilityBound n) :
    HasRestartedWindowFirstMomentBound incrementLaw cutoff window initial
      (fun n => ENNReal.ofReal (Real.exp
          (if n ≤ cutoff then upper n else upper cutoff + upper n)) *
        probabilityBound n) := by
  apply hasRestartedWindowFirstMomentBound_of_probability incrementLaw
    cutoff window hwindow upper hupper initial probabilityBound
  intro n x _
  rw [restartedWindowProbability_eq_zeroInitial]
  exact hprobability n

/-- For canonical IID increments, the first moment in a constant restarted
horizontal tube is controlled entirely by the two ordinary horizontal-tube
probabilities.  This is the direct interface from a Mogulskii estimate to the
restarted killed-population argument. -/
theorem hasRestartedWindowFirstMomentBound_horizontal
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a width : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hwidth : 0 ≤ width)
    (cutoff : ℕ) (initial : Set ℝ) :
    HasRestartedWindowFirstMomentBound
      (iidSequenceLaw ν) cutoff
      (fun _ => Set.Icc (-a * width) ((1 - a) * width)) initial
      (fun n => ENNReal.ofReal (Real.exp
          (if n ≤ cutoff then (1 - a) * width
            else (1 - a) * width + (1 - a) * width)) *
        if n ≤ cutoff then
          horizontalTubeProbability
            (iidSequenceLaw ν) a width n
        else
          horizontalTubeProbability
              (iidSequenceLaw ν) a width cutoff *
          horizontalTubeProbability
              (iidSequenceLaw ν) a width
                (n - cutoff)) := by
  apply hasRestartedWindowFirstMomentBound_of_zero_probability
    (iidSequenceLaw ν) cutoff
    (fun _ => Set.Icc (-a * width) ((1 - a) * width))
    (fun _ => measurableSet_Icc)
    (fun _ => (1 - a) * width)
    (fun _ => Set.Icc_subset_Iic_self) initial
  intro n
  exact le_of_eq (restartedWindowProbability_horizontal_eq
    ν ha0 ha1 hwidth cutoff n 0)

end ProbabilityTheory.RandomWalk
