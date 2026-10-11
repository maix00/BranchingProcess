/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.CapacitySpine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Upper
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Scaling

/-!
# A killed population for the positive-initial-mass right-tail argument

The two tube stages in the proof of (4.15) are represented by one restarted
window schedule.  The recursively retained population is constructed from the
pre-sampled branching field.  Its capacity-failure probability is bounded by
actual tilted-walk corridor probabilities through the first-moment and
Markov interfaces.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- Drift of the second-stage tube in the positive-`a` proof of (4.15),
with `κ = π² σ² / 2`. -/
noncomputable def rightTailPositiveADrift
    (ell ellN : ℕ) (κ c : ℝ) (j : ℕ) : ℝ :=
  κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ ((-2 : ℝ) / 3)) * (j : ℝ)

/-- Restarted path windows for the killed population used in the proof of
(4.15). Up to `ell`, paths remain in `[-b log N, 0]`, with a narrower window
at `ell`. The next stage uses the tilted tube, with a narrower terminal
window at `ellN`. -/
noncomputable def rightTailPositiveARestartedWindow
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) : Set ℝ :=
  if k < ell then Set.Icc (-b * logN) 0
  else if k = ell then Set.Icc (-b * logN) ((-b + v) * logN)
  else if k < ellN then
    Set.Icc (rightTailPositiveADrift ell ellN κ c (k - ell))
      (rightTailPositiveADrift ell ellN κ c (k - ell) +
        c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
  else if k = ellN then
    Set.Icc (rightTailPositiveADrift ell ellN κ c (ellN - ell))
      (rightTailPositiveADrift ell ellN κ c (ellN - ell) +
        v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
  else ∅

/-- Deterministic upper endpoint for each stage window. -/
noncomputable def rightTailPositiveAWindowUpper
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) : ℝ :=
  if k < ell then 0
  else if k = ell then (-b + v) * logN
  else if k < ellN then
    rightTailPositiveADrift ell ellN κ c (k - ell) +
      c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  else if k = ellN then
    rightTailPositiveADrift ell ellN κ c (ellN - ell) +
      v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  else 0

/-- The second-stage tube as a path started at the restart time. Its terminal
window may be narrower than the interior window. -/
noncomputable def rightTailPositiveASecondStageWindow
    (ell ellN : ℕ) (κ c v : ℝ) (j : ℕ) : Set ℝ :=
  let D := ellN - ell
  let width := ((D : ℕ) : ℝ) ^ (3⁻¹ : ℝ)
  if j = 0 then Set.Icc 0 0
  else if j < D then
    Set.Icc (rightTailPositiveADrift ell ellN κ c j)
      (rightTailPositiveADrift ell ellN κ c j + c * width)
  else if j = D then
    Set.Icc (rightTailPositiveADrift ell ellN κ c j)
      (rightTailPositiveADrift ell ellN κ c j + v * width)
  else ∅

/-- Membership in the second-stage restarted tube, expressed on the shifted
increment path beginning at the restart time. -/
noncomputable def rightTailPositiveASecondStageTubeEvent
    (ell ellN : ℕ) (κ c v : ℝ) : Set (ℕ → ℝ) :=
  {increment | ∀ j : Fin (ellN - ell + 1),
    AdditivePath.displacement (j : ℕ) increment ∈
      rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)}

/-- A finite initial segment of the second-stage tube. This is the event
needed at an intermediate generation before the full second-stage horizon. -/
noncomputable def rightTailPositiveASecondStageTubePrefixEvent
    (ell ellN d : ℕ) (κ c v : ℝ) : Set (ℕ → ℝ) :=
  {increment | ∀ j : Fin (d + 1),
    AdditivePath.displacement (j : ℕ) increment ∈
      rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)}

/-- A path inside an increasing tube of fixed width has bounded drawdown;
its endpoint lies below the terminal upper endpoint of the tube. -/
theorem increasingTubePath_mem_noLargeDropEndpointBelowEvent
    (D : ℕ) (drift : ℕ → ℝ) (width : ℝ)
    (hmonotone : Monotone drift)
    (increment : ℕ → ℝ)
    (hpath : ∀ j : Fin (D + 1),
      AdditivePath.displacement (j : ℕ) increment ∈
        Set.Icc (drift (j : ℕ)) (drift (j : ℕ) + width)) :
    increment ∈
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        D width (drift D + width) := by
  constructor
  · intro i j hij hj
    have hi := hpath ⟨i, Nat.lt_succ_of_le (hij.trans hj)⟩
    have hj' := hpath ⟨j, Nat.lt_succ_of_le hj⟩
    linarith [hi.2, hj'.1, hmonotone hij]
  · have hend := hpath ⟨D, Nat.lt_succ_self D⟩
    exact hend.2

/-- The variable-width second-stage tube is contained in a fixed-width
increasing tube whenever the terminal window is no wider than the interior
window. -/
theorem rightTailPositiveASecondStageTubeEvent_subset_fixedTube
    (ell ellN : ℕ) (κ c v : ℝ)
    (hellN : ell < ellN) (hc : 0 ≤ c) (hvc : v ≤ c) :
    rightTailPositiveASecondStageTubeEvent ell ellN κ c v ⊆
      {increment : ℕ → ℝ | ∀ j : Fin (ellN - ell + 1),
        AdditivePath.displacement (j : ℕ) increment ∈
          Set.Icc (rightTailPositiveADrift ell ellN κ c (j : ℕ))
            (rightTailPositiveADrift ell ellN κ c (j : ℕ) +
              c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))} := by
  intro increment hpath j
  let D := ellN - ell
  let width : ℝ := (D : ℝ) ^ (3⁻¹ : ℝ)
  have hDpos : 0 < D := by dsimp [D]; exact Nat.sub_pos_of_lt hellN
  have hwidth : 0 ≤ width := by positivity
  have hterminal : v * width ≤ c * width :=
    mul_le_mul_of_nonneg_right hvc hwidth
  by_cases hjzero : (j : ℕ) = 0
  · have hj : j = 0 := Fin.ext hjzero
    subst j
    simp [rightTailPositiveADrift, D, width, mul_nonneg hc hwidth]
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hjzero
    by_cases hjlt : (j : ℕ) < D
    · have hmember := hpath j
      simpa [rightTailPositiveASecondStageWindow, D, width,
        hjzero, hjlt] using hmember
    · have hjEq : (j : ℕ) = D := by
        have hjle : (j : ℕ) ≤ D := Nat.le_of_lt_succ j.isLt
        omega
      have hmember := hpath j
      have hmember' : AdditivePath.displacement (j : ℕ) increment ∈
          Set.Icc (rightTailPositiveADrift ell ellN κ c (j : ℕ))
            (rightTailPositiveADrift ell ellN κ c (j : ℕ) + v * width) := by
        simpa [rightTailPositiveASecondStageWindow, D, width,
          hjzero, hjlt, hjEq, hDpos.ne'] using hmember
      have hupper :
          rightTailPositiveADrift ell ellN κ c (j : ℕ) + v * width ≤
            rightTailPositiveADrift ell ellN κ c (j : ℕ) + c * width := by
        linarith [hterminal]
      exact ⟨hmember'.1,
        hmember'.2.trans (by simpa [D, width] using hupper)⟩

/-- Every initial segment of the second-stage tube is contained in the
corresponding fixed-width increasing tube, including the narrower terminal
window when the segment reaches `ellN`. -/
theorem rightTailPositiveASecondStageTubePrefixEvent_subset_fixedTube
    (ell ellN d : ℕ) (κ c v : ℝ)
    (hellN : ell < ellN) (hd : d ≤ ellN - ell)
    (hc : 0 ≤ c) (hvc : v ≤ c) :
    rightTailPositiveASecondStageTubePrefixEvent ell ellN d κ c v ⊆
      {increment : ℕ → ℝ | ∀ j : Fin (d + 1),
        AdditivePath.displacement (j : ℕ) increment ∈
          Set.Icc (rightTailPositiveADrift ell ellN κ c (j : ℕ))
            (rightTailPositiveADrift ell ellN κ c (j : ℕ) +
              c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))} := by
  intro increment hpath j
  let D := ellN - ell
  let width : ℝ := (D : ℝ) ^ (3⁻¹ : ℝ)
  have hDpos : 0 < D := by dsimp [D]; exact Nat.sub_pos_of_lt hellN
  have hwidth : 0 ≤ width := by positivity
  have hterminal : v * width ≤ c * width :=
    mul_le_mul_of_nonneg_right hvc hwidth
  by_cases hjzero : (j : ℕ) = 0
  · have hj : j = 0 := Fin.ext hjzero
    subst j
    simp [rightTailPositiveADrift, D, width, mul_nonneg hc hwidth]
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hjzero
    have hjleD : (j : ℕ) ≤ D := by
      exact (Nat.le_of_lt_succ j.isLt).trans hd
    by_cases hjlt : (j : ℕ) < D
    · have hmember := hpath j
      simpa [rightTailPositiveASecondStageTubePrefixEvent,
        rightTailPositiveASecondStageWindow, D, width, hjzero, hjlt]
        using hmember
    · have hjEq : (j : ℕ) = D := by omega
      have hmember := hpath j
      have hmember' : AdditivePath.displacement (j : ℕ) increment ∈
          Set.Icc (rightTailPositiveADrift ell ellN κ c (j : ℕ))
            (rightTailPositiveADrift ell ellN κ c (j : ℕ) + v * width) := by
        simpa [rightTailPositiveASecondStageTubePrefixEvent,
          rightTailPositiveASecondStageWindow, D, width,
          hjzero, hjlt, hjEq, hDpos.ne'] using hmember
      have hupper :
          rightTailPositiveADrift ell ellN κ c (j : ℕ) + v * width ≤
            rightTailPositiveADrift ell ellN κ c (j : ℕ) + c * width := by
        linarith [hterminal]
      exact ⟨hmember'.1,
        hmember'.2.trans (by simpa [D, width] using hupper)⟩

/-- The whole second-stage tube event implies the drawdown event with the
same width as its interior corridor. The increasing linear drift is why a
path can gain height without increasing its drawdown allowance. -/
theorem rightTailPositiveASecondStageTubeEvent_subset_drawdownEvent
    (ell ellN : ℕ) (κ c v : ℝ)
    (hellN : ell < ellN) (hκ : 0 ≤ κ) (hc : 0 < c) (hvc : v ≤ c) :
    rightTailPositiveASecondStageTubeEvent ell ellN κ c v ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        (ellN - ell)
        (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
        (rightTailPositiveADrift ell ellN κ c (ellN - ell) +
          c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) := by
  let D := ellN - ell
  let drift : ℕ → ℝ := rightTailPositiveADrift ell ellN κ c
  let width : ℝ := c * (((D : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hDpos : 0 < D := by dsimp [D]; exact Nat.sub_pos_of_lt hellN
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hcoef : 0 ≤ κ / c ^ 2 * (D : ℝ) ^ ((-2 : ℝ) / 3) := by
    positivity
  have hmono : Monotone drift := by
    intro i j hij
    dsimp [drift, rightTailPositiveADrift]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hcoef
  have hwidth : 0 ≤ width := by
    dsimp [width]
    positivity
  have hcontained := rightTailPositiveASecondStageTubeEvent_subset_fixedTube
    ell ellN κ c v hellN hc.le hvc
  intro increment hpath
  have hpositions : ∀ j : Fin (D + 1),
      AdditivePath.displacement (j : ℕ) increment ∈
        Set.Icc (drift (j : ℕ)) (drift (j : ℕ) + width) := by
    simpa [D, drift, width] using hcontained hpath
  have hdrawdown := increasingTubePath_mem_noLargeDropEndpointBelowEvent
    D drift width hmono increment hpositions
  simpa [D, drift, width] using hdrawdown

/-- A second-stage prefix of length `d` is contained in a drawdown event at
that same horizon. The corridor scale still uses the full planned horizon
`ellN - ell`. -/
theorem rightTailPositiveASecondStageTubePrefixEvent_subset_drawdownEvent
    (ell ellN d : ℕ) (κ c v : ℝ)
    (hellN : ell < ellN) (hd : d ≤ ellN - ell)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvc : v ≤ c) :
    rightTailPositiveASecondStageTubePrefixEvent ell ellN d κ c v ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        d
        (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
        (rightTailPositiveADrift ell ellN κ c d +
          c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) := by
  let D := ellN - ell
  let drift : ℕ → ℝ := rightTailPositiveADrift ell ellN κ c
  let width : ℝ := c * (((D : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hDpos : 0 < D := by dsimp [D]; exact Nat.sub_pos_of_lt hellN
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hcoef : 0 ≤ κ / c ^ 2 * (D : ℝ) ^ ((-2 : ℝ) / 3) := by
    positivity
  have hmono : Monotone drift := by
    intro i j hij
    dsimp [drift, rightTailPositiveADrift]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hcoef
  have hcontained := rightTailPositiveASecondStageTubePrefixEvent_subset_fixedTube
    ell ellN d κ c v hellN hd hc.le hvc
  intro increment hpath
  have hpositions : ∀ j : Fin (d + 1),
      AdditivePath.displacement (j : ℕ) increment ∈
        Set.Icc (drift (j : ℕ)) (drift (j : ℕ) + width) := by
    simpa [D, drift, width] using hcontained hpath
  have hdrawdown := increasingTubePath_mem_noLargeDropEndpointBelowEvent
    d drift width hmono increment hpositions
  simpa [D, drift, width] using hdrawdown

/-- After the restart time, membership in the original window schedule
forces the corresponding shifted increments to stay in the second-stage
tube through the observed prefix. -/
theorem rightTailPositiveARestartedWindow_event_subset_shiftedSecondStageTubePrefix
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hk : ell < k) (hkN : k ≤ ellN) :
    {increment : ℕ → ℝ |
      InRestartedWindows ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (history k 0 increment)} ⊆
      {increment : ℕ → ℝ |
        (fun j => increment (ell + j)) ∈
          rightTailPositiveASecondStageTubePrefixEvent
            ell ellN (k - ell) κ c v} := by
  intro increment hwindow j
  change InRestartedWindows ell
    (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
    (history k 0 increment) at hwindow
  have hellN : ell < ellN := lt_of_lt_of_le hk hkN
  have hEllNe : ellN ≠ ell := Ne.symm hellN.ne
  have hDpos : 0 < ellN - ell := Nat.sub_pos_of_lt hellN
  have hDadd : ell + (ellN - ell) = ellN := by omega
  by_cases hjzero : (j : ℕ) = 0
  · have hj : j = 0 := Fin.ext hjzero
    subst j
    simp [rightTailPositiveASecondStageWindow, AdditivePath.displacement_zero]
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hjzero
    have hleftBound : ell < k + 1 := by omega
    have hrightBound : ell + (j : ℕ) < k + 1 := by
      have hjle : (j : ℕ) ≤ k - ell := Nat.le_of_lt_succ j.isLt
      omega
    have hpath := hwindow ⟨ell + (j : ℕ), hrightBound⟩
    have hanchor : restartAnchor ell (ell + (j : ℕ)) = ell :=
      restartAnchor_eq_cutoff (by omega)
    have hpath' :
        history k 0 increment ⟨ell + (j : ℕ), hrightBound⟩ -
          history k 0 increment ⟨ell, hleftBound⟩ ∈
          rightTailPositiveARestartedWindow ell ellN logN b v c κ
            (ell + (j : ℕ)) := by
      simpa only [hanchor] using hpath
    have hshift :
        history k 0 increment ⟨ell + (j : ℕ), hrightBound⟩ -
          history k 0 increment ⟨ell, hleftBound⟩ =
        AdditivePath.displacement (j : ℕ) (fun q => increment (ell + q)) := by
      calc
        _ = AdditivePath.displacement (ell + (j : ℕ)) increment -
            AdditivePath.displacement ell increment := by
          simp [history_eq_fromIncrements, AdditivePath.fromIncrements]
        _ = AdditivePath.displacement (j : ℕ)
            (fun q => increment (ell + q)) := by
          rw [AdditivePath.displacement_add]
          ring
    rw [hshift] at hpath'
    by_cases hjterminal : (j : ℕ) = ellN - ell
    · have habsolute : ell + (j : ℕ) = ellN := by omega
      simpa [rightTailPositiveARestartedWindow,
        rightTailPositiveASecondStageTubePrefixEvent,
        rightTailPositiveASecondStageWindow, hjpos.ne', hjterminal,
        habsolute, hDpos.ne', hDadd, Nat.add_sub_cancel_left,
        not_lt_of_ge hellN.le, hEllNe] using hpath'
    · have hjlt : (j : ℕ) < ellN - ell := by omega
      have habsolute : ell + (j : ℕ) < ellN := by omega
      simpa [rightTailPositiveARestartedWindow,
        rightTailPositiveASecondStageTubePrefixEvent,
        rightTailPositiveASecondStageWindow, hjpos.ne', hjterminal,
        hjlt, habsolute, hDpos.ne', hDadd, Nat.add_sub_cancel_left,
        not_lt_of_ge hellN.le, hEllNe] using hpath'

/-- Under an IID increment law, the restarted-window probability after the
cutoff is bounded by the drawdown probability of the shifted second-stage
prefix at its actual length. -/
theorem iidSequenceLaw_restartedWindowProbability_le_secondStageDrawdown
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hk : ell < k) (hkN : k ≤ ellN)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvc : v ≤ c) :
    RandomWalk.restartedWindowProbability (iidSequenceLaw ν) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ) k 0 ≤
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          (k - ell)
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift ell ellN κ c (k - ell) +
            c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) := by
  let d := k - ell
  let tubePrefix := rightTailPositiveASecondStageTubePrefixEvent ell ellN d κ c v
  let shift : (ℕ → ℝ) → (ℕ → ℝ) := fun increment j => increment (ell + j)
  have hd : d ≤ ellN - ell := by dsimp [d]; omega
  have hDpos : 0 < ellN - ell := by omega
  have hsubsetRestart :
      {increment : ℕ → ℝ |
        InRestartedWindows ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (history k 0 increment)} ⊆ shift ⁻¹' tubePrefix := by
    intro increment hmem
    change shift increment ∈ tubePrefix
    simpa [d, tubePrefix, shift] using
      (rightTailPositiveARestartedWindow_event_subset_shiftedSecondStageTubePrefix
        ell ellN k logN b v c κ hk hkN) hmem
  have hsubsetDrawdown : tubePrefix ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        d
        (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
        (rightTailPositiveADrift ell ellN κ c d +
          c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) :=
    rightTailPositiveASecondStageTubePrefixEvent_subset_drawdownEvent
      ell ellN d κ c v (lt_of_lt_of_le hk hkN) hd hκ hc hvc
  have hprefixMeas : MeasurableSet tubePrefix := by
    classical
    rw [show tubePrefix = ⋂ j : Fin (d + 1),
        {increment : ℕ → ℝ |
          AdditivePath.displacement (j : ℕ) increment ∈
            rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)} by
      ext increment
      simp [tubePrefix, rightTailPositiveASecondStageTubePrefixEvent]]
    apply MeasurableSet.iInter
    intro j
    have hwindow : MeasurableSet
        (rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)) := by
      dsimp [rightTailPositiveASecondStageWindow]
      split_ifs <;> simp [measurableSet_Icc]
    exact hwindow.preimage (displacement_measurable (j : ℕ))
  have hshiftMeas : Measurable shift := measurable_natAdd ell
  have hshiftLaw : (iidSequenceLaw ν).map shift = iidSequenceLaw ν := by
    simpa [shift] using iidSequenceLaw_map_natAdd ν ell
  unfold RandomWalk.restartedWindowProbability
  change (iidSequenceLaw ν)
      {increment : ℕ → ℝ |
        InRestartedWindows ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (history k 0 increment)} ≤ _
  calc
    _ ≤ (iidSequenceLaw ν) (shift ⁻¹' tubePrefix) := measure_mono hsubsetRestart
    _ = (iidSequenceLaw ν).map shift tubePrefix := by
      rw [Measure.map_apply hshiftMeas hprefixMeas]
    _ = (iidSequenceLaw ν) tubePrefix := by rw [hshiftLaw]
    _ ≤ (iidSequenceLaw ν)
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          d
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift ell ellN κ c d +
            c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) :=
      measure_mono hsubsetDrawdown

/-- The parameter inequalities in the positive-`a` construction are feasible
whenever the target threshold is strictly above the limiting trajectory.
Here `r` is the positive cube root of `t`; keeping `r^3 = t` explicit makes
the algebraic choice of `c` transparent. -/
theorem exists_rightTailPositiveAParameters
    (a t r sigmaSq zeta : ℝ)
    (ha : 0 < a) (ht : 0 < t) (hr : 0 < r) (hrcube : r ^ 3 = t)
    (hsigma : 0 ≤ sigmaSq)
    (hgap : -a + Real.pi ^ 2 / 2 * sigmaSq * t < zeta) :
    ∃ b v c : ℝ,
      0 < b ∧ b < a ∧ 0 < v ∧ v < b ∧ v ≤ c ∧ 0 < c ∧ c < r⁻¹ ∧
      c * r + (a - b) + v < 1 ∧
      -b + Real.pi ^ 2 / 2 * sigmaSq * (c⁻¹ ^ 2 * r) +
        2 * v * (1 + r) < zeta := by
  let C : ℝ := Real.pi ^ 2 / 2 * sigmaSq
  let gap : ℝ := zeta - (-a + C * t)
  let K : ℝ := 1 / 3 + 8 * C * t + 2 / 3 * (1 + r)
  let δ₀ : ℝ := min (min (1 / 2) a) (gap / (2 * K))
  let δ : ℝ := min δ₀ (1 / (4 * r))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hgapPos : 0 < gap := by
    dsimp [gap, C]
    linarith
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδHalf : δ ≤ 1 / 2 := by
    dsimp [δ, δ₀]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδA : δ ≤ a := by
    dsimp [δ, δ₀]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδGap : δ ≤ gap / (2 * K) := by
    dsimp [δ, δ₀]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hδSmall : δ ≤ 1 / (4 * r) := by
    dsimp [δ]
    exact min_le_right _ _
  have hden : 0 < 1 - δ := by linarith
  have hquadLeft : 0 ≤ 1 - 2 * δ := by linarith
  have hquadRight : 0 ≤ (11 : ℝ) / 2 - 4 * δ := by linarith
  have hquad : 0 ≤ 8 * δ ^ 2 - 15 * δ + 6 := by
    have hprod := mul_nonneg hquadLeft hquadRight
    nlinarith
  have hpolyProduct : 1 ≤ (1 + 8 * δ) * (1 - δ) ^ 2 := by
    have hprod := mul_nonneg hδ.le hquad
    nlinarith
  have hratio : 1 / (1 - δ) ^ 2 ≤ 1 + 8 * δ := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).2
    nlinarith [hpolyProduct]
  have hratioTerm : C * (t / (1 - δ) ^ 2) ≤ C * t * (1 + 8 * δ) := by
    calc
      C * (t / (1 - δ) ^ 2) = (C * t) * (1 / (1 - δ) ^ 2) := by ring
      _ ≤ (C * t) * (1 + 8 * δ) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg hC ht.le)
  let b : ℝ := a - δ / 3
  let v : ℝ := δ / 3
  let c : ℝ := (1 - δ) / r
  have hcInv : c⁻¹ = r / (1 - δ) := by
    dsimp [c]
    field_simp [hr.ne', hden.ne']
  have hcScale : c⁻¹ ^ 2 * r = t / (1 - δ) ^ 2 := by
    rw [hcInv]
    calc
      (r / (1 - δ)) ^ 2 * r = r ^ 3 / (1 - δ) ^ 2 := by
        field_simp [hden.ne']
      _ = t / (1 - δ) ^ 2 := by rw [hrcube]
  have hδK : δ * K ≤ gap / 2 := by
    calc
      δ * K ≤ (gap / (2 * K)) * K :=
        mul_le_mul_of_nonneg_right hδGap hK.le
      _ = gap / 2 := by field_simp [hK.ne']
  refine ⟨b, v, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [b]
    nlinarith [ha, hδA]
  · dsimp [b]
    linarith
  · dsimp [v]
    positivity
  · dsimp [b, v]
    nlinarith [ha, hδA]
  · dsimp [v, c]
    have hδr : δ * r ≤ 1 / 4 := by
      have hδr4 : δ * (4 * r) ≤ 1 :=
        (le_div_iff₀ (by positivity : 0 < 4 * r)).mp hδSmall
      nlinarith [hδr4]
    have hvrt : (δ / 3) * r ≤ 1 / 12 := by nlinarith [hδr]
    apply (le_div_iff₀ hr).2
    nlinarith [hvrt, hδHalf]
  · dsimp [c]
    exact div_pos (by linarith) hr
  · dsimp [c]
    rw [div_lt_iff₀ hr]
    rw [inv_mul_cancel₀ hr.ne']
    linarith
  · dsimp [b, v, c]
    field_simp [hr.ne']
    linarith
  · dsimp [b, v]
    rw [hcScale]
    change -(a - δ / 3) + C * (t / (1 - δ) ^ 2) +
      2 * (δ / 3) * (1 + r) < zeta
    have hmain : -(a - δ / 3) + C * (t / (1 - δ) ^ 2) +
        2 * (δ / 3) * (1 + r) ≤ -a + C * t + δ * K := by
      dsimp [K]
      nlinarith [hratioTerm]
    have hgapEq : -a + C * t + gap = zeta := by
      dsimp [gap]
      ring
    calc
      -(a - δ / 3) + C * (t / (1 - δ) ^ 2) +
          2 * (δ / 3) * (1 + r) ≤ -a + C * t + δ * K := hmain
      _ ≤ -a + C * t + gap / 2 := by linarith [hδK]
      _ < -a + C * t + gap := by linarith [hgapPos]
      _ = zeta := hgapEq

/-- The drift at any time in the second tube is bounded by its terminal
diffusive scale. -/
theorem rightTailPositiveADrift_le_span
    (ell ellN j : ℕ) (κ c : ℝ)
    (hell : ell < ellN) (hκ : 0 ≤ κ)
    (hj : j ≤ ellN - ell) :
    rightTailPositiveADrift ell ellN κ c j ≤
      κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
  let span : ℝ := ((ellN - ell : ℕ) : ℝ)
  have hspan : 0 < span := by
    dsimp [span]
    exact_mod_cast Nat.sub_pos_of_lt hell
  have hjReal : (j : ℝ) ≤ span := by
    dsimp [span]
    exact_mod_cast hj
  have hpow : span ^ ((-2 : ℝ) / 3) * span = span ^ (3⁻¹ : ℝ) := by
    calc
      span ^ ((-2 : ℝ) / 3) * span =
          span ^ ((-2 : ℝ) / 3) * span ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = span ^ (((-2 : ℝ) / 3) + 1) := by rw [← Real.rpow_add hspan]
      _ = span ^ (3⁻¹ : ℝ) := by congr 1; norm_num
  have hcoeff : 0 ≤ κ / c ^ 2 := div_nonneg hκ (sq_nonneg c)
  calc
    rightTailPositiveADrift ell ellN κ c j =
        κ / c ^ 2 * (span ^ ((-2 : ℝ) / 3) * (j : ℝ)) := by
          simp [rightTailPositiveADrift, span]
          ring
    _ ≤ κ / c ^ 2 * (span ^ ((-2 : ℝ) / 3) * span) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hjReal (Real.rpow_nonneg hspan.le _)) hcoeff
    _ = κ / c ^ 2 * span ^ (3⁻¹ : ℝ) := by rw [hpow]

/-- At every time strictly after the first cutoff and no later than the
terminal time, the window's upper endpoint is bounded by the terminal drift
plus the larger of its two widths. -/
theorem rightTailPositiveAWindowUpper_le_span
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hell : ell < ellN) (hκ : 0 ≤ κ)
    (hk : ell < k) (hkN : k ≤ ellN) :
    rightTailPositiveAWindowUpper ell ellN logN b v c κ k ≤
      (κ / c ^ 2 + max c v) *
        (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
  let span : ℝ := ((ellN - ell : ℕ) : ℝ)
  have hspan : 0 < span := by
    dsimp [span]
    exact_mod_cast Nat.sub_pos_of_lt hell
  have hspanNonneg :
      0 ≤ (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) :=
    Real.rpow_nonneg hspan.le _
  have hdrift := rightTailPositiveADrift_le_span ell ellN (k - ell) κ c
    hell hκ (Nat.sub_le_sub_right hkN ell)
  have hne : k ≠ ell := ne_of_gt hk
  by_cases hend : k = ellN
  · subst k
    have hnotlt : ¬ellN < ell := Nat.not_lt_of_ge hell.le
    have hne' : ellN ≠ ell := by omega
    simp [rightTailPositiveAWindowUpper, hnotlt, hne']
    calc
      rightTailPositiveADrift ell ellN κ c (ellN - ell) +
          v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) ≤
        κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
          max c v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
            exact add_le_add hdrift
              (mul_le_mul_of_nonneg_right (le_max_right c v) hspanNonneg)
      _ = (κ / c ^ 2 + max c v) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by ring
  · have hkltN : k < ellN := by omega
    have hnotlt : ¬k < ell := Nat.not_lt_of_ge hk.le
    simp [rightTailPositiveAWindowUpper, hnotlt, hne, hkltN]
    calc
      rightTailPositiveADrift ell ellN κ c (k - ell) +
          c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) ≤
        κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
          max c v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
            exact add_le_add hdrift
              (mul_le_mul_of_nonneg_right (le_max_left c v) hspanNonneg)
      _ = (κ / c ^ 2 + max c v) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by ring

/-- A single deterministic envelope controls every exponential weight in the
uniform killed-capacity estimate. The initial-stage endpoint is nonpositive
when `v ≤ b`, and all later upper endpoints are controlled by the terminal
diffusive scale. -/
theorem rightTailPositiveAEndpointEnvelope_le
    (ell ellN : ℕ) (logN b v c κ : ℝ)
    (hellN : ell < ellN)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvb : v ≤ b) (hlog : 0 ≤ logN) :
    ∀ k : Fin (ellN + 1),
      (if (k : ℕ) ≤ ell then
        rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)
      else
        rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)) ≤
        (κ / c ^ 2 + max c v) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
  intro k
  have hscaleNonneg :
      0 ≤ (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hcoeff : 0 ≤ κ / c ^ 2 + max c v := by positivity
  have hupperEllEq :
      rightTailPositiveAWindowUpper ell ellN logN b v c κ ell =
        (-b + v) * logN := by
    simp [rightTailPositiveAWindowUpper]
  have hupperEll : rightTailPositiveAWindowUpper ell ellN logN b v c κ ell ≤ 0 := by
    rw [hupperEllEq]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog
  by_cases hkle : (k : ℕ) ≤ ell
  · simp [hkle]
    by_cases hklt : (k : ℕ) < ell
    · have hkupper :
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ) = 0 := by
        simp [rightTailPositiveAWindowUpper, hklt]
      rw [hkupper]
      exact mul_nonneg hcoeff hscaleNonneg
    · have hkeq : (k : ℕ) = ell := by omega
      have hkeqFin : k = ⟨ell, by omega⟩ := Fin.ext hkeq
      rw [hkeqFin]
      exact hupperEll.trans (mul_nonneg hcoeff hscaleNonneg)
  · simp [hkle]
    have hklo : ell < (k : ℕ) := by omega
    have hkhi : (k : ℕ) ≤ ellN := by omega
    have hkupper := rightTailPositiveAWindowUpper_le_span ell ellN (k : ℕ)
      logN b v c κ hellN hκ hklo hkhi
    calc
      rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ) ≤
        0 + (κ / c ^ 2 + max c v) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) :=
          add_le_add hupperEll hkupper
      _ = (κ / c ^ 2 + max c v) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by simp

/-- The endpoint of the first tube is its prescribed narrow interval. -/
theorem rightTailPositiveAWindowUpper_at_cutoff
    (ell ellN : ℕ) (logN b v c κ : ℝ) :
    rightTailPositiveAWindowUpper ell ellN logN b v c κ ell =
      (-b + v) * logN := by
  simp [rightTailPositiveAWindowUpper]

/-- The first-stage endpoint envelope is nonpositive when the narrow terminal
window lies below zero. -/
theorem rightTailPositiveAFirstStageUpper_le_zero
    (ell ellN : ℕ) (logN b v c κ : ℝ)
    (hvb : v ≤ b) (hlog : 0 ≤ logN)
    (k : ℕ) (hk : k ≤ ell) :
    rightTailPositiveAWindowUpper ell ellN logN b v c κ k ≤ 0 := by
  by_cases hklt : k < ell
  · simp [rightTailPositiveAWindowUpper, hklt]
  · have hkeq : k = ell := by omega
    rw [hkeq, rightTailPositiveAWindowUpper_at_cutoff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog

/-- The second-stage exponential endpoint weight retains the negative
first-stage offset, while its later contribution is controlled by the
terminal diffusive scale. -/
theorem rightTailPositiveASecondStageEnvelope_le
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hellN : ell < ellN) (hκ : 0 ≤ κ)
    (hk : ell < k) (hkN : k ≤ ellN) :
    rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
      rightTailPositiveAWindowUpper ell ellN logN b v c κ k ≤
    (-b + v) * logN + (κ / c ^ 2 + max c v) *
      (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
  rw [rightTailPositiveAWindowUpper_at_cutoff]
  exact add_le_add_right
    (rightTailPositiveAWindowUpper_le_span ell ellN k logN b v c κ
      hellN hκ hk hkN) ((-b + v) * logN)

/-- Splitting the finite generation sum at `ell` gives the expected counts
of terms from the two stages. -/
theorem sum_fin_if_le_eq_add_mul (ell ellN : ℕ) (A B : ℝ≥0∞)
    (hell : ell ≤ ellN) :
    (∑ k : Fin (ellN + 1), if (k : ℕ) ≤ ell then A else B) =
      ((ell + 1 : ℕ) : ℝ≥0∞) * A +
        ((ellN - ell : ℕ) : ℝ≥0∞) * B := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≤ ell then A else B)]
  rw [← Finset.sum_range_add_sum_Ico
    (fun k : ℕ => if k ≤ ell then A else B)
    (show ell + 1 ≤ ellN + 1 by omega)]
  have hfirst :
      (∑ k ∈ Finset.range (ell + 1), if k ≤ ell then A else B) =
        ((ell + 1 : ℕ) : ℝ≥0∞) * A := by
    have hterm : ∀ k ∈ Finset.range (ell + 1), (if k ≤ ell then A else B) = A := by
      intro k hk
      have hk' : k < ell + 1 := Finset.mem_range.mp hk
      simp [Nat.lt_succ_iff.mp hk']
    rw [Finset.sum_congr rfl hterm]
    simp [Finset.sum_const]
  have hsecond :
      (∑ k ∈ Finset.Ico (ell + 1) (ellN + 1), if k ≤ ell then A else B) =
        ((ellN - ell : ℕ) : ℝ≥0∞) * B := by
    have hterm : ∀ k ∈ Finset.Ico (ell + 1) (ellN + 1),
        (if k ≤ ell then A else B) = B := by
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      simp [Nat.not_le_of_gt hk'.1]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlength : ellN + 1 - (ell + 1) = ellN - ell := by omega
    rw [hlength]
    simp [Finset.sum_const]
  rw [hfirst, hsecond]

theorem measurableSet_rightTailPositiveARestartedWindow
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) :
    MeasurableSet (rightTailPositiveARestartedWindow ell ellN logN b v c κ k) := by
  classical
  unfold rightTailPositiveARestartedWindow
  split_ifs <;> simp [measurableSet_Icc]

theorem rightTailPositiveARestartedWindow_zero_mem
    (ell ellN : ℕ) (logN b v c κ : ℝ)
    (hell : 0 < ell) (hb : 0 ≤ b) (hlog : 0 ≤ logN) :
    0 ∈ rightTailPositiveARestartedWindow ell ellN logN b v c κ 0 := by
  simp [rightTailPositiveARestartedWindow, hell, mul_nonneg hb hlog]

theorem rightTailPositiveARestartedWindow_subset_Iic_upper
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) :
    rightTailPositiveARestartedWindow ell ellN logN b v c κ k ⊆
      Set.Iic (rightTailPositiveAWindowUpper ell ellN logN b v c κ k) := by
  classical
  unfold rightTailPositiveARestartedWindow rightTailPositiveAWindowUpper
  split_ifs <;> simp [Set.Icc_subset_Iic_self]

/-- Every restarted-window event observed after the first cutoff already
forces the original path to stay in the first-stage corridor through `ell`.
This extracts a useful probability bound without estimating the second tube. -/
theorem rightTailPositiveARestartedWindow_event_subset_firstStage
    (ell ellN : ℕ) (logN b v c κ : ℝ) (n : ℕ)
    (hlog : 0 ≤ logN) (hvb : v ≤ b)
    (hn : ell ≤ n) :
    {increment : ℕ → ℝ |
      InRestartedWindows ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (history n 0 increment)} ⊆
      {increment : ℕ → ℝ |
        InClosedInterval (-b * logN) 0 ell 0 increment} := by
  intro increment hpath
  change ∀ j : Fin (ell + 1),
      history ell 0 increment j ∈ Set.Icc (-b * logN) 0
  intro j
  have hjle : (j : ℕ) ≤ ell := Nat.le_of_lt_succ j.isLt
  have hrestart := hpath ⟨j, by omega⟩
  have hwindow :
      history n 0 increment ⟨j, by omega⟩ ∈
        rightTailPositiveARestartedWindow ell ellN logN b v c κ j := by
    simpa [restartAnchor_eq_zero hjle] using hrestart
  have htop : (-b + v) * logN ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hlog
    linarith
  have hwindow_subset :
      rightTailPositiveARestartedWindow ell ellN logN b v c κ j ⊆
        Set.Icc (-b * logN) 0 := by
    by_cases hjlt : (j : ℕ) < ell
    · simp [rightTailPositiveARestartedWindow, hjlt]
    · have hjeq : (j : ℕ) = ell := by omega
      rw [hjeq]
      have hcutoff :
          rightTailPositiveARestartedWindow ell ellN logN b v c κ ell =
            Set.Icc (-b * logN) ((-b + v) * logN) := by
        simp [rightTailPositiveARestartedWindow]
      rw [hcutoff]
      intro x hx
      exact ⟨hx.1, hx.2.trans htop⟩
  have hfirst := hwindow_subset hwindow
  have hhistory :
      history n 0 increment ⟨j, by omega⟩ = history ell 0 increment j := by
    simp [history_eq_fromIncrements, AdditivePath.fromIncrements]
  rw [← hhistory]
  exact hfirst

/-- Markov bound for the capacity event of the actual causal killed tree with
the two stages of the positive-`a` construction. The right side is expressed
in terms of tilted random-walk corridor probabilities, so the Mogulskii input
can be supplied separately without assuming any killed-population expectation
bound. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (_hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro p hp
        rcases RootIndexed.mem_initialPopulation_iff.mp hp with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          ENNReal.ofReal (Real.exp
            (if (k : ℕ) ≤ ell then upper k else upper ell + upper k)) *
          RandomWalk.restartedWindowProbability
            (tiltedIncrementFieldLaw realPotential μ) ell window
            (k : ℕ) 0) / (N + 1 : ℕ) := by
  dsimp only
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  let bound : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Real.exp (if k ≤ ell then upper k else upper ell + upper k)) *
      RandomWalk.restartedWindowProbability ν ell window k 0
  have hwindow : ∀ k, MeasurableSet (window k) :=
    measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ
  have hzero : 0 ∈ window 0 :=
    rightTailPositiveARestartedWindow_zero_mem ell ellN logN b v c κ
      hell hb hlog
  have hupper : ∀ k, window k ⊆ Set.Iic (upper k) :=
    rightTailPositiveARestartedWindow_subset_Iic_upper ell ellN logN b v c κ
  have hbound : HasRestartedWindowFirstMomentBound ν ell window Set.univ bound :=
    hasRestartedWindowFirstMomentBound_of_zero_probability ν ell window
      hwindow upper hupper Set.univ
      (fun k => RandomWalk.restartedWindowProbability ν ell window k 0)
      (fun _ => le_rfl)
  simpa [window, upper, ν, RootIndexed.initialPopulation] using
    RootIndexed.CausalPopulation.measure_capacityEvent_compl_le_card_mul_sum_of_windowFirstMomentBound
      (roots := Finset.univ) (initialPosition := fun _ : Fin m => (0 : ℝ))
      (d := id) (hd := measurable_id) (μ := μ) hboundary ell window hwindow
      hzero upper hupper Set.univ bound
      (fun _ _ => Set.mem_univ _) hbound N ellN

/-- Uniform corridor estimates can be substituted directly into the
positive-`a` killed-capacity bound. The endpoint envelope controls the
exponential weight, while a single bound `p` controls every restarted-window
probability. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_uniform
    (m ell ellN N : ℕ) (logN b v c κ U : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (p : ℝ≥0∞)
    (hupper : ∀ k : Fin (ellN + 1),
      (if (k : ℕ) ≤ ell then
        rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)
      else
        rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)) ≤ U)
    (hpath : ∀ k : Fin (ellN + 1),
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ p) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro p hp
        rcases RootIndexed.mem_initialPopulation_iff.mp hp with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        ((ellN + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp U) * p) /
          (N + 1 : ℕ) := by
  dsimp only
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  have hbase := measure_rightTailPositiveAKilled_capacityEvent_compl_le
    m ell ellN N logN b v c κ hell hellN hb hlog μ hboundary
  have hsum :
      (∑ k : Fin (ellN + 1),
        ENNReal.ofReal (Real.exp
          (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
          RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0) ≤
        ∑ _k : Fin (ellN + 1), ENNReal.ofReal (Real.exp U) * p := by
    apply Finset.sum_le_sum
    intro k _hk
    have hweight : ENNReal.ofReal (Real.exp
        (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) ≤
        ENNReal.ofReal (Real.exp U) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hupper k))
    calc
      _ ≤ ENNReal.ofReal (Real.exp U) *
          RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0 :=
        mul_le_mul_of_nonneg_right hweight (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp U) * p :=
        mul_le_mul_of_nonneg_left (hpath k) (by positivity)
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        ((RootIndexed.CausalPopulation.ofRestartedRealPositionSets
          (fun _ : Fin m => (0 : ℝ)) id measurable_id
          (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
          (by
            intro p hp
            rcases RootIndexed.mem_initialPopulation_iff.mp hp with
              ⟨r, hr, rfl⟩
            simp) ell window
          (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)).capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          ENNReal.ofReal (Real.exp
            (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
            RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0) /
          (N + 1 : ℕ) := by
      simpa [window, upper, ν] using hbase
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1), ENNReal.ofReal (Real.exp U) * p) /
          (N + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (m : ℝ≥0∞) *
        ((ellN + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp U) * p) /
          (N + 1 : ℕ) := by
      simp [Finset.sum_const, mul_assoc]

/-- Capacity bound with the positive-`a` tube's deterministic endpoint
envelope already substituted. The remaining probabilistic input is the
uniform restarted-window bound `hpath`. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_enveloped
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvb : v ≤ b)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (p : ℝ≥0∞)
    (hpath : ∀ k : Fin (ellN + 1),
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ p) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) * ((ellN + 1 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp
          ((κ / c ^ 2 + max c v) *
            (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) * p) /
          (N + 1 : ℕ) := by
  let U : ℝ := (κ / c ^ 2 + max c v) *
    (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hupper : ∀ k : Fin (ellN + 1),
      (if (k : ℕ) ≤ ell then
        rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)
      else
        rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)) ≤ U := by
    intro k
    simpa [U] using rightTailPositiveAEndpointEnvelope_le
      ell ellN logN b v c κ hellN hκ hc hvb hlog k
  have hcapacity := measure_rightTailPositiveAKilled_capacityEvent_compl_le_uniform
    m ell ellN N logN b v c κ U hell hellN hb hlog μ hboundary p hupper hpath
  simpa [U] using hcapacity

/-- Two-stage form of the killed-capacity estimate. The first tube and the
long restarted tube may use different weighted probability bounds, matching
the separate corridor estimates in the proof of (4.15). -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhase
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (A B : ℝ≥0∞)
    (hfirst : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤ A)
    (hsecond : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤ B) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) * A +
          ((ellN - ell : ℕ) : ℝ≥0∞) * B) /
          (N + 1 : ℕ) := by
  dsimp only
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  let term : Fin (ellN + 1) → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Real.exp
      (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
      RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0
  have hbase := measure_rightTailPositiveAKilled_capacityEvent_compl_le
    m ell ellN N logN b v c κ hell hellN hb hlog μ hboundary
  have hsum :
      (∑ k : Fin (ellN + 1), term k) ≤
        ∑ k : Fin (ellN + 1), if (k : ℕ) ≤ ell then A else B := by
    apply Finset.sum_le_sum
    intro k _hk
    by_cases hkle : (k : ℕ) ≤ ell
    · simpa [term, hkle, window, upper, ν] using hfirst k hkle
    · simpa [term, hkle, window, upper, ν] using
        hsecond k (Nat.lt_of_not_ge hkle)
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        ((RootIndexed.CausalPopulation.ofRestartedRealPositionSets
          (fun _ : Fin m => (0 : ℝ)) id measurable_id
          (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
          (by
            intro q hq
            rcases RootIndexed.mem_initialPopulation_iff.mp hq with
              ⟨r, _hr, rfl⟩
            simp) ell window
          (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)).capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) * (∑ k : Fin (ellN + 1), term k) /
        (N + 1 : ℕ) := by
          simpa [term, window, upper, ν] using hbase
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1), if (k : ℕ) ≤ ell then A else B) /
          (N + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) * A +
          ((ellN - ell : ℕ) : ℝ≥0∞) * B) /
          (N + 1 : ℕ) := by
      rw [sum_fin_if_le_eq_add_mul ell ellN A B (Nat.le_of_lt hellN)]

/-- Corridor-probability inputs imply the two weighted phase bounds. The
first interval uses its nonpositive endpoint weight; the long tube keeps the
negative cutoff offset in its exponential factor. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfPathBounds
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (pFirst pSecond : ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst)
    (hsecondPath : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pSecond) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) * pFirst +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp
              ((-b + v) * logN + (κ / c ^ 2 + max c v) *
                (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) * pSecond)) /
          (N + 1 : ℕ) := by
  let U₂ : ℝ := (-b + v) * logN + (κ / c ^ 2 + max c v) *
    (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hfirst : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤ pFirst := by
    intro k hk
    have hupper := rightTailPositiveAFirstStageUpper_le_zero
      ell ellN logN b v c κ hvb hlog (k : ℕ) hk
    have hweight : ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) ≤ 1 := by
      calc
        ENNReal.ofReal (Real.exp
            (rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) ≤
          ENNReal.ofReal (Real.exp 0) :=
            ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hupper)
        _ = 1 := by simp
    calc
      _ ≤ 1 * RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 := mul_le_mul_of_nonneg_right hweight (by positivity)
      _ ≤ pFirst := by simpa using hfirstPath k hk
  have hsecond : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤ ENNReal.ofReal (Real.exp U₂) * pSecond := by
    intro k hk
    have hkhi : (k : ℕ) ≤ ellN := Nat.le_of_lt_succ k.isLt
    have hupper := rightTailPositiveASecondStageEnvelope_le
      ell ellN (k : ℕ) logN b v c κ hellN hκ hk hkhi
    have hweight : ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) ≤
        ENNReal.ofReal (Real.exp U₂) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_le_exp.mpr (by simpa [U₂] using hupper)
    calc
      _ ≤ ENNReal.ofReal (Real.exp U₂) *
          RandomWalk.restartedWindowProbability
            (tiltedIncrementFieldLaw realPotential μ) ell
            (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
            (k : ℕ) 0 := mul_le_mul_of_nonneg_right hweight (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp U₂) * pSecond :=
        mul_le_mul_of_nonneg_left (hsecondPath k hk) (by positivity)
  simpa [U₂] using measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhase
    m ell ellN N logN b v c κ hell hellN hb hlog μ hboundary pFirst
    (ENNReal.ofReal (Real.exp U₂) * pSecond) hfirst hsecond

/-- Generation-dependent bounds can be summed directly in the killed-capacity
estimate. This retains the shorter-prefix drawdown probabilities instead of
replacing all of them by the full-horizon probability. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfGenerationPathBounds
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (pFirst : ℝ≥0∞) (pSecond : ℕ → ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst)
    (hsecondPath : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pSecond (k : ℕ)) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then pFirst else
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN + (κ / c ^ 2 + max c v) *
                (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) *
              pSecond (k : ℕ)) /
          (N + 1 : ℕ) := by
  dsimp only
  let U₂ : ℝ := (-b + v) * logN + (κ / c ^ 2 + max c v) *
    (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  let term : Fin (ellN + 1) → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Real.exp
      (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
      RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0
  have hbase := measure_rightTailPositiveAKilled_capacityEvent_compl_le
    m ell ellN N logN b v c κ hell hellN hb hlog μ hboundary
  have hsum :
      (∑ k : Fin (ellN + 1), term k) ≤
        ∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then pFirst else
            ENNReal.ofReal (Real.exp U₂) * pSecond (k : ℕ) := by
    apply Finset.sum_le_sum
    intro k _hk
    by_cases hkle : (k : ℕ) ≤ ell
    · have hupper := rightTailPositiveAFirstStageUpper_le_zero
        ell ellN logN b v c κ hvb hlog (k : ℕ) hkle
      have hweight : ENNReal.ofReal (Real.exp (upper (k : ℕ))) ≤ 1 := by
        calc
          ENNReal.ofReal (Real.exp (upper (k : ℕ))) ≤ ENNReal.ofReal (Real.exp 0) :=
            ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hupper)
          _ = 1 := by simp
      have hpath := hfirstPath k hkle
      calc
        _ ≤ 1 * RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0 :=
          mul_le_mul_of_nonneg_right (by simpa [hkle] using hweight) (by positivity)
        _ ≤ pFirst := by simpa using hpath
        _ = (if (k : ℕ) ≤ ell then pFirst else
            ENNReal.ofReal (Real.exp U₂) * pSecond (k : ℕ)) := by simp [hkle]
    · have hkle : ell < (k : ℕ) := Nat.lt_of_not_ge hkle
      have hkhi : (k : ℕ) ≤ ellN := Nat.le_of_lt_succ k.isLt
      have hupper := rightTailPositiveASecondStageEnvelope_le
        ell ellN (k : ℕ) logN b v c κ hellN hκ hkle hkhi
      have hweight : ENNReal.ofReal (Real.exp
          (upper ell + upper (k : ℕ))) ≤ ENNReal.ofReal (Real.exp U₂) := by
        apply ENNReal.ofReal_le_ofReal
        exact Real.exp_le_exp.mpr (by simpa [U₂, upper] using hupper)
      have hpath := hsecondPath k hkle
      calc
        _ ≤ ENNReal.ofReal (Real.exp U₂) *
            RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0 :=
          mul_le_mul_of_nonneg_right
            (by simpa [Nat.not_le_of_gt hkle] using hweight)
            (by positivity)
        _ ≤ ENNReal.ofReal (Real.exp U₂) * pSecond (k : ℕ) :=
          mul_le_mul_of_nonneg_left hpath (by positivity)
        _ = (if (k : ℕ) ≤ ell then pFirst else
            ENNReal.ofReal (Real.exp U₂) * pSecond (k : ℕ)) := by
          simp [Nat.not_le_of_gt hkle]
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        ((RootIndexed.CausalPopulation.ofRestartedRealPositionSets
          (fun _ : Fin m => (0 : ℝ)) id measurable_id
          (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
          (by
            intro q hq
            rcases RootIndexed.mem_initialPopulation_iff.mp hq with
              ⟨r, _hr, rfl⟩
            simp) ell window
          (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)).capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) * (∑ k : Fin (ellN + 1), term k) /
        (N + 1 : ℕ) := by
          simpa [term, window, upper, ν] using hbase
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then pFirst else
            ENNReal.ofReal (Real.exp U₂) * pSecond (k : ℕ)) /
          (N + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by simp [U₂]

/-- The generation-dependent capacity bound accepts per-prefix random-walk
drawdown estimates directly. The endpoint threshold and the corridor width
are kept at the full planned scale, while the drawdown horizon is the actual
observed prefix length. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (hc : 0 < c) (hvc : v ≤ c)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    (pFirst : ℝ≥0∞) (pSecond : ℕ → ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst)
    (hdrawdown : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          ((k : ℕ) - ell)
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) +
            c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) ≤ pSecond (k : ℕ)) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then pFirst else
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN + (κ / c ^ 2 + max c v) *
                (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) *
              pSecond (k : ℕ)) /
          (N + 1 : ℕ) := by
  have hsecondPath : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pSecond (k : ℕ) := by
    intro k hk
    rw [show tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν by
      rw [hν]
      rfl]
    exact (iidSequenceLaw_restartedWindowProbability_le_secondStageDrawdown
      ν ell ellN (k : ℕ) logN b v c κ hk (by omega) hκ hc hvc)
      |>.trans (hdrawdown k hk)
  exact measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfGenerationPathBounds
    m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb μ hboundary
    pFirst pSecond hfirstPath hsecondPath

/-- A bound on the first-stage horizontal corridor controls every later
restarted-window probability, since those events retain the first-stage
prefix. The initial-stage terms use only that the tilted path law is a
probability measure. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfFirstStageBound
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (pSecond : ℝ≥0∞)
    (hfirstStage : (tiltedIncrementFieldLaw realPotential μ)
      {increment : ℕ → ℝ |
        InClosedInterval (-b * logN) 0 ell 0 increment} ≤ pSecond) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp
              ((-b + v) * logN + (κ / c ^ 2 + max c v) *
                (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) * pSecond)) /
          (N + 1 : ℕ) := by
  let htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  have hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ 1 := by
    intro k hk
    calc
      _ ≤ (tiltedIncrementFieldLaw realPotential μ) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := htilted.measure_univ
  have hsecondPath : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pSecond := by
    intro k hk
    have hsubset := rightTailPositiveARestartedWindow_event_subset_firstStage
      ell ellN logN b v c κ (k : ℕ) hlog hvb (Nat.le_of_lt hk)
    have hprob :
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤
        (tiltedIncrementFieldLaw realPotential μ)
          {increment : ℕ → ℝ |
            InClosedInterval (-b * logN) 0 ell 0 increment} := by
      unfold RandomWalk.restartedWindowProbability
      exact measure_mono hsubset
    exact hprob.trans hfirstStage
  simpa using
    (measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfPathBounds
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb μ hboundary
      1 pSecond hfirstPath hsecondPath)

/-- The first-stage corridor probability is controlled by any horizontal
tube whose lower boundary matches the corridor and whose upper boundary is
nonnegative. The parameterization below makes those inclusions explicit. -/
theorem rightTailPositiveA_firstStage_probability_le_horizontalTubeProbability
    (ell : ℕ) (logN b a : ℝ) (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (incrementLaw : Measure (ℕ → ℝ)) :
    incrementLaw {increment : ℕ → ℝ |
      InClosedInterval (-b * logN) 0 ell 0 increment} ≤
      horizontalTubeProbability incrementLaw a (b * logN / a) ell := by
  have hwidth : 0 ≤ b * logN / a :=
    div_nonneg (mul_nonneg hb hlog) ha.le
  have hupper : 0 ≤ (1 - a) * (b * logN / a) :=
    mul_nonneg (by linarith) hwidth
  have hlower : -a * (b * logN / a) = -b * logN := by
    field_simp [ha.ne']
  have hsubset :
      {increment : ℕ → ℝ |
        InClosedInterval (-b * logN) 0 ell 0 increment} ⊆
      {increment : ℕ → ℝ |
        InHorizontalTube a (b * logN / a) ell increment} := by
    intro increment hprefix k
    have hposition := hprefix ⟨(k : ℕ) + 1, by omega⟩
    have hposition' :
        AdditivePath.displacement ((k : ℕ) + 1) increment ∈
          Set.Icc (-b * logN) 0 := by
      simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using
        hposition
    rw [hlower]
    exact ⟨hposition'.1, hposition'.2.trans hupper⟩
  unfold horizontalTubeProbability
  exact measure_mono hsubset

/-- Staying in the first-stage interval forces every earlier position to be
at most one corridor width above every later position, and leaves the
endpoint at or below zero. Thus the first-stage event is contained in the
drawdown event already estimated by `RawRate`. -/
theorem rightTailPositiveA_firstStage_event_subset_noLargeDropEndpointBelowEvent
    (ell : ℕ) (logN b : ℝ) :
    {increment : ℕ → ℝ |
      InClosedInterval (-b * logN) 0 ell 0 increment} ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        ell (b * logN) 0 := by
  intro increment hprefix
  constructor
  · intro i j hij hj
    have hleft := hprefix ⟨i, by omega⟩
    have hright := hprefix ⟨j, by omega⟩
    have hleft' : AdditivePath.displacement i increment ∈
        Set.Icc (-b * logN) 0 := by
      simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hleft
    have hright' : AdditivePath.displacement j increment ∈
        Set.Icc (-b * logN) 0 := by
      simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hright
    linarith [hleft'.2, hright'.1]
  · have hend := hprefix ⟨ell, Nat.lt_succ_self ell⟩
    simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hend.2

/-- The first-stage probability inherits any drawdown-and-endpoint bound,
ready for direct use with the raw finite-variance rate theorem. -/
theorem rightTailPositiveA_firstStage_probability_le_of_drawdownBound
    (ell : ℕ) (logN b : ℝ) (incrementLaw : Measure (ℕ → ℝ))
    (p : ℝ≥0∞)
    (hdrawdown : incrementLaw
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        ell (b * logN) 0) ≤ p) :
    incrementLaw {increment : ℕ → ℝ |
      InClosedInterval (-b * logN) 0 ell 0 increment} ≤ p :=
  (measure_mono
    (rightTailPositiveA_firstStage_event_subset_noLargeDropEndpointBelowEvent
      ell logN b)).trans hdrawdown

/-- A horizontal interval corridor has the same uniform finite-variance
exponential bound as the corresponding drawdown event. This is the first
stage of the positive-`a` construction in (4.15). -/
theorem exists_uniform_iidSequenceLaw_firstStageCorridor_le_ah
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (endpointRatio target blockTarget p : ℝ)
    (hEndpointRatio : 0 < endpointRatio)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ horizon : ℕ, ∀ width : ℝ, 0 < width → delta0 ≤ width →
        width ^ (2 + p) ≤ (horizon : ℝ) →
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            InClosedInterval (-width) 0 horizon 0 increment} ≤
          ENNReal.ofReal (Real.exp
            (-target * sigma ^ 2 * (horizon : ℝ) / width ^ 2)) := by
  obtain ⟨delta0, hdelta0, hdrawdown⟩ :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment
      ν hν hsigma hB hcontinuous hmeasurable endpointRatio target blockTarget p
      hEndpointRatio htarget htargetBlock hblockTarget hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro horizon width hwidth hscale hlength
  have hinterval :=
    rightTailPositiveA_firstStage_event_subset_noLargeDropEndpointBelowEvent
      horizon width 1
  have hinterval' :
      {increment : ℕ → ℝ |
        InClosedInterval (-width) 0 horizon 0 increment} ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        horizon width 0 := by
    simpa using hinterval
  have hthreshold : 0 ≤ width / endpointRatio :=
    div_nonneg hwidth.le hEndpointRatio.le
  have hcutoff :
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        horizon width 0 ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        horizon width (width / endpointRatio) := by
    intro increment h
    exact ⟨h.1, le_trans h.2 hthreshold⟩
  have hbound := hdrawdown width hscale horizon hlength
  exact (measure_mono (hinterval'.trans hcutoff)).trans hbound

/-- The affine second-stage corridor in the positive-`a` proof is controlled
by the uniform finite-variance Aïdékon--Hu drawdown estimate on every prefix
whose length is at least a superdiffusive power of the planned tube width.
The endpoint ceiling is reduced to the fixed ratio required by that estimate
using the monotone drift envelope. -/
theorem iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_ah
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (κ c target blockTarget p : ℝ)
    (hκ : 0 ≤ κ) (hc : 0 < c)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ ell ellN d : ℕ, ell < ellN → d ≤ ellN - ell →
      delta0 ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
      (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤ (d : ℝ) →
      iidSequenceLaw ν
          (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
            d
            (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
            (rightTailPositiveADrift ell ellN κ c d +
              c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) ≤
        ENNReal.ofReal (Real.exp
          (-target * sigma ^ 2 * (d : ℝ) /
            (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)) := by
  let endpointRatio : ℝ := c / (κ / c ^ 2 + c)
  have hden : 0 < κ / c ^ 2 + c := by
    positivity
  have hratio : 0 < endpointRatio := by
    dsimp [endpointRatio]
    exact div_pos hc hden
  obtain ⟨delta0, hdelta0, hbound⟩ :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment
      ν hν hsigma hB hcontinuous hmeasurable endpointRatio target blockTarget p
      hratio htarget htargetBlock hblockTarget hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro ell ellN d hellN hd hwidthLarge hlengthLarge
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hwidthPos : 0 < width := by
    dsimp [width]
    have hspan : 0 < (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
      have hspanNat : 0 < ellN - ell := Nat.sub_pos_of_lt hellN
      have hspanReal : 0 < ((ellN - ell : ℕ) : ℝ) := by exact_mod_cast hspanNat
      exact Real.rpow_pos_of_pos hspanReal _
    exact mul_pos hc hspan
  have hspan := rightTailPositiveADrift_le_span ell ellN d κ c hellN hκ hd
  have hratioEq : c / endpointRatio = κ / c ^ 2 + c := by
    dsimp [endpointRatio]
    field_simp [hc.ne', hden.ne']
  have hendpoint :
      rightTailPositiveADrift ell ellN κ c d + width ≤ width / endpointRatio := by
    calc
      rightTailPositiveADrift ell ellN κ c d + width ≤
          κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) + width :=
        by simpa [add_comm] using add_le_add_right hspan width
      _ = (κ / c ^ 2 + c) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
        dsimp [width]
        ring
      _ = (c / endpointRatio) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by rw [hratioEq]
      _ = width / endpointRatio := by
        dsimp [width]
        ring
  have hbound' := hbound width hwidthLarge d hlengthLarge
  apply le_trans (measure_mono ?_) hbound'
  intro increment hdrop
  exact ⟨hdrop.1, hdrop.2.trans hendpoint⟩

/-- Insert the uniform Aïdékon--Hu estimate into the two-stage capacity
bound. Long second-stage prefixes use the exponential drawdown estimate;
short prefixes use only that their probability is at most one. This is the
finite-parameter form of the second-stage estimate in the proof of (4.15). -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (hc : 0 < c) (hvc : v ≤ c)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (target blockTarget p : ℝ)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p)
    (pFirst : ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      (delta0 ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then pFirst else
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN + (κ / c ^ 2 + max c v) *
                (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) *
              (if (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤
                  (((k : ℕ) - ell : ℕ) : ℝ) then
                ENNReal.ofReal (Real.exp
                  (-target * sigma ^ 2 * (((k : ℕ) - ell : ℕ) : ℝ) /
                    (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2))
              else 1)) / (N + 1 : ℕ)) := by
  obtain ⟨delta0', hdelta0', hAH⟩ :=
    iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_ah
      ν hspine hsigma hB hcontinuous hmeasurable κ c target blockTarget p
      hκ hc htarget htargetBlock hblockTarget hp
  refine ⟨delta0', hdelta0', ?_⟩
  intro hscale
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hwidthLarge : delta0' ≤ width := by simpa [width] using hscale
  let pSecond : ℕ → ℝ≥0∞ := fun k =>
    if width ^ (2 + p) ≤ ((k - ell : ℕ) : ℝ) then
      ENNReal.ofReal (Real.exp
        (-target * sigma ^ 2 * ((k - ell : ℕ) : ℝ) / width ^ 2))
    else 1
  have hdrawdown : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          ((k : ℕ) - ell) width
          (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) + width)) ≤
        pSecond (k : ℕ) := by
    intro k hk
    have hkN : (k : ℕ) ≤ ellN := by omega
    have hd : (k : ℕ) - ell ≤ ellN - ell := by omega
    by_cases hlong : width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ)
    · have hbound := hAH ell ellN ((k : ℕ) - ell) hellN hd hwidthLarge hlong
      simpa [pSecond, width, hlong] using hbound
    · have hprob : iidSequenceLaw ν
          (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
            ((k : ℕ) - ell) width
            (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) + width)) ≤ 1 := by
        calc
          _ ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      simpa [pSecond, width, hlong] using hprob
  have hcap :=
    measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb hc hvc μ hboundary
      ν hν pFirst pSecond hfirstPath hdrawdown
  simpa [pSecond, width] using hcap

/-- The two-stage capacity estimate now accepts a one-stage horizontal-tube
bound as its remaining random-walk input. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfHorizontalTubeBound
    (m ell ellN N : ℕ) (logN b v c κ a : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (pSecond : ℝ≥0∞)
    (hhorizontal : horizontalTubeProbability
      (tiltedIncrementFieldLaw realPotential μ) a (b * logN / a) ell ≤ pSecond) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp
              ((-b + v) * logN + (κ / c ^ 2 + max c v) *
                (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) * pSecond)) /
          (N + 1 : ℕ) := by
  have hprefix :
      (tiltedIncrementFieldLaw realPotential μ)
        {increment : ℕ → ℝ |
          InClosedInterval (-b * logN) 0 ell 0 increment} ≤ pSecond :=
    (rightTailPositiveA_firstStage_probability_le_horizontalTubeProbability
      ell logN b a hb hlog ha ha1 (tiltedIncrementFieldLaw realPotential μ)).trans
        hhorizontal
  exact measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfFirstStageBound
    m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb μ hboundary
    pSecond hprefix

end ProbabilityTheory.BranchingRandomWalk.Selection.Tail
