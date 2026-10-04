/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher
public import Probability.Process.RandomWalk.Path.Window
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.KilledTransition

/-!
# Path interpretation of killed Rademacher transitions

The finite-state killed transition survives exactly when every partial sum of
the corresponding Rademacher increment path remains at an interior lattice
site.  This file is the path-level bridge between the spectral kernel and the
random-walk formulation.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- Real coordinate represented by an interior finite-interval state. -/
def intervalSite {interiorCount : ℕ} (i : Fin interiorCount) : ℝ :=
  i.val + 1

theorem intervalLeftNeighbor_eq_some_iff
    {interiorCount : ℕ} (i j : Fin interiorCount) :
    intervalLeftNeighbor i = some j ↔ intervalSite j = intervalSite i - 1 := by
  unfold intervalLeftNeighbor
  split_ifs with hi
  · simp only [Option.some.injEq]
    constructor
    · intro h
      subst j
      simp only [intervalSite]
      rw [Nat.cast_sub (by omega : 1 ≤ i.val)]
      ring
    · intro h
      apply Fin.ext
      change i.val - 1 = j.val
      have h' : (j.val : ℝ) + 1 = i.val := by
        simpa [intervalSite] using h
      have hn : j.val + 1 = i.val := by exact_mod_cast h'
      omega
  · constructor
    · simp
    · intro h
      have hiz : i.val = 0 := Nat.eq_zero_of_not_pos hi
      have h' : (j.val : ℝ) + 1 = 0 := by
        simpa [intervalSite, hiz] using h
      have hpos : (0 : ℝ) < (j.val : ℝ) + 1 := by positivity
      linarith

theorem intervalRightNeighbor_eq_some_iff
    {interiorCount : ℕ} (i j : Fin interiorCount) :
    intervalRightNeighbor i = some j ↔ intervalSite j = intervalSite i + 1 := by
  unfold intervalRightNeighbor
  split_ifs with hi
  · simp only [Option.some.injEq]
    constructor
    · intro h
      subst j
      simp [intervalSite]
    · intro h
      apply Fin.ext
      change i.val + 1 = j.val
      have h' : (j.val : ℝ) = i.val + 1 := by
        simpa [intervalSite] using h
      have hn : j.val = i.val + 1 := by exact_mod_cast h'
      omega
  · constructor
    · simp
    · intro h
      have h' : j.val = i.val + 1 := by
        exact_mod_cast (show (j.val : ℝ) = i.val + 1 by
          simpa [intervalSite] using h)
      omega

theorem intervalRademacherStep_eq_some_iff
    {interiorCount : ℕ} (i : Fin interiorCount) (step : Bool) (j : Fin interiorCount) :
    intervalRademacherStep i step = some j ↔
      intervalSite j = intervalSite i + rademacherOfBool step := by
  cases step <;>
    (simp [intervalRademacherStep, intervalLeftNeighbor_eq_some_iff,
      intervalRightNeighbor_eq_some_iff, rademacherOfBool] <;> ring_nf)

/-- A one-step Rademacher move survives precisely when its new real
coordinate is one of the interior sites `1, ..., interiorCount`. -/
theorem intervalRademacherStep_isSome_iff
    {interiorCount : ℕ} (i : Fin interiorCount) (step : Bool) :
    (intervalRademacherStep i step).isSome ↔
      1 ≤ intervalSite i + rademacherOfBool step ∧
        intervalSite i + rademacherOfBool step ≤ interiorCount := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    have hsite := (intervalRademacherStep_eq_some_iff i step j).mp hj
    rw [← hsite]
    constructor
    · simp [intervalSite]
    · have hle : j.val + 1 ≤ interiorCount := by omega
      simpa [intervalSite] using (show (j.val : ℝ) + 1 ≤ interiorCount by
        exact_mod_cast hle)
  · intro h
    cases step with
    | false =>
        simp only [rademacherOfBool, Bool.false_eq_true, ↓reduceIte] at h
        have hi : 0 < i.val := by
          have : (0 : ℝ) < i.val := by
            have hone : (1 : ℝ) ≤ i.val := by
              simpa [intervalSite] using h.1
            linarith
          exact_mod_cast this
        simp [intervalRademacherStep, intervalLeftNeighbor, hi]
    | true =>
        simp only [rademacherOfBool, ↓reduceIte] at h
        have hi : i.val + 1 < interiorCount := by
          have hle : i.val + 2 ≤ interiorCount := by
            have hreal : (i.val : ℝ) + 2 ≤ interiorCount := by
              have := h.2
              simp only [intervalSite] at this
              linarith
            exact_mod_cast hreal
          omega
        simp [intervalRademacherStep, intervalRightNeighbor, hi]

/-- Recursive path event that every one of the next `n` Rademacher positions
lies at an interior site.  It is defined on an infinite increment path so it
can be used directly under the canonical IID sequence law. -/
def rademacherStaysInInterval (interiorCount : ℕ) :
    ℕ → ℝ → (ℕ → Bool) → Prop
  | 0, _, _ => True
  | n + 1, x, branch =>
      let next := x + rademacherOfBool (branch 0)
      1 ≤ next ∧ next ≤ interiorCount ∧
        rademacherStaysInInterval interiorCount n next (fun k => branch (k + 1))

/-- The recursive formulation is the usual finite-path window event.  The
assumption at time zero is explicit because `rademacherStaysInInterval`
records only the next `n` positions, whereas `history` also contains its
initial coordinate. -/
theorem rademacherStaysInInterval_iff_inWindows
    (interiorCount n : ℕ) (initial : ℝ) (branch : ℕ → Bool)
    (hinitial : initial ∈ Set.Icc (1 : ℝ) interiorCount) :
    rademacherStaysInInterval interiorCount n initial branch ↔
      InWindows (fun _ : Fin (n + 1) => Set.Icc (1 : ℝ) interiorCount)
        (history n initial (rademacherIncrementPath branch)) := by
  induction n generalizing initial branch with
  | zero =>
      simp only [rademacherStaysInInterval, InWindows]
      constructor
      · intro _ k
        exact Fin.eq_zero k ▸ (by simpa [history] using hinitial)
      · intro _
        trivial
  | succ n ih =>
      rw [history_succ]
      simp only [rademacherIncrementPath]
      change
        (1 ≤ initial + rademacherOfBool (branch 0) ∧
          initial + rademacherOfBool (branch 0) ≤ interiorCount ∧
          rademacherStaysInInterval interiorCount n
            (initial + rademacherOfBool (branch 0))
            (fun k => branch (k + 1))) ↔ _
      constructor
      · rintro ⟨hlower, hupper, htail⟩ k
        refine Fin.cases ?_ (fun j => ?_) k
        · simpa [prependHistory] using hinitial
        · have hnext : initial + rademacherOfBool (branch 0) ∈
              Set.Icc (1 : ℝ) interiorCount := ⟨hlower, hupper⟩
          have hwindow := (ih _ _ hnext).mp htail
          exact hwindow j
      · intro hwindow
        have hnext : initial + rademacherOfBool (branch 0) ∈
            Set.Icc (1 : ℝ) interiorCount := by
          have hw := hwindow ((0 : Fin (n + 1)).succ)
          change history n (initial + rademacherOfBool (branch 0))
            (incrementTail (rademacherIncrementPath branch)) 0 ∈
              Set.Icc (1 : ℝ) interiorCount at hw
          simpa [history] using hw
        exact ⟨hnext.1, hnext.2,
          (ih _ _ hnext).mpr (fun j => hwindow (Fin.succ j))⟩

/-- For a genuine finite-interval state, the time-zero condition needed by
the path formulation is automatic. -/
theorem intervalSite_mem_Icc {interiorCount : ℕ}
    (i : Fin interiorCount) :
    intervalSite i ∈ Set.Icc (1 : ℝ) interiorCount := by
  constructor
  · simp [intervalSite]
  · have hle : i.val + 1 ≤ interiorCount := by omega
    simpa [intervalSite] using (show (i.val : ℝ) + 1 ≤ interiorCount by
      exact_mod_cast hle)

theorem rademacherStaysInInterval_iff_inClosedInterval
    {interiorCount : ℕ} (n : ℕ) (start : Fin interiorCount)
    (branch : ℕ → Bool) :
    rademacherStaysInInterval interiorCount n (intervalSite start) branch ↔
      InClosedInterval 1 interiorCount n (intervalSite start)
        (rademacherIncrementPath branch) := by
  exact rademacherStaysInInterval_iff_inWindows interiorCount n
    (intervalSite start) branch (intervalSite_mem_Icc start)

/-- The killed finite-state transition survives a Boolean history exactly
when the corresponding Rademacher path stays inside the interval. -/
theorem runPartialSteps_isSome_iff_staysInInterval
    {interiorCount : ℕ} (n : ℕ) (i : Fin interiorCount) (branch : ℕ → Bool) :
    (Kernel.runPartialSteps intervalRademacherStep n i
        (Kernel.sequencePrefix n branch)).isSome ↔
      rademacherStaysInInterval interiorCount n (intervalSite i) branch := by
  induction n generalizing i branch with
  | zero => simp [Kernel.runPartialSteps, rademacherStaysInInterval]
  | succ n ih =>
      simp only [Kernel.runPartialSteps, Kernel.sequencePrefix,
        rademacherStaysInInterval]
      cases hnext : intervalRademacherStep i (branch 0) with
      | none =>
          have hkilled : ¬ (1 ≤ intervalSite i + rademacherOfBool (branch 0) ∧
              intervalSite i + rademacherOfBool (branch 0) ≤ interiorCount) := by
            rw [← intervalRademacherStep_isSome_iff i (branch 0)]
            simp [hnext]
          have hnext' : intervalRademacherStep i (branch (↑(0 : Fin (n + 1)))) = none :=
            hnext
          rw [hnext']
          simp only [Option.bind_none, Option.isSome_none, Bool.false_eq]
          tauto
      | some j =>
          have hsite : intervalSite j =
              intervalSite i + rademacherOfBool (branch 0) :=
            (intervalRademacherStep_eq_some_iff i (branch 0) j).mp hnext
          have hinside : 1 ≤ intervalSite i + rademacherOfBool (branch 0) ∧
              intervalSite i + rademacherOfBool (branch 0) ≤ interiorCount :=
            (intervalRademacherStep_isSome_iff i (branch 0)).mp (by simp [hnext])
          have htail : Fin.tail (Kernel.sequencePrefix (n + 1) branch) =
              Kernel.sequencePrefix n (fun k => branch (k + 1)) := by
            funext k
            rfl
          have hnext' : intervalRademacherStep i (branch (↑(0 : Fin (n + 1)))) = some j :=
            hnext
          rw [hnext']
          simp only [Option.bind_some, htail, ih]
          rw [hsite]
          tauto

/-- The finite-history survival cylinder is exactly the small-deviation event
of the canonical Boolean realization of the Rademacher walk. -/
theorem survivingHistories_preimage_eq_staysInInterval
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (Kernel.sequencePrefix (ξ := Bool) n) ⁻¹'
        (Kernel.survivingPartialStepHistories intervalRademacherStep
          n start : Set (Fin n → Bool)) =
      {branch | rademacherStaysInInterval interiorCount n
        (intervalSite start) branch} := by
  ext branch
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    Kernel.survivingPartialStepHistories, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact runPartialSteps_isSome_iff_staysInInterval n start branch

/-- The total mass of the killed interval kernel is the probability of the
corresponding canonical Rademacher small-deviation event. -/
theorem intervalRademacherKernel_pow_apply_univ_eq_pathSurvival
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (intervalRademacherKernel interiorCount ^ n) start Set.univ =
      iidSequenceLaw fairBoolMeasure
        {branch | rademacherStaysInInterval interiorCount n
          (intervalSite start) branch} := by
  rw [intervalRademacherKernel_pow_apply_univ_eq_iid]
  rw [survivingHistories_preimage_eq_staysInInterval]

/-- The same mass, now stated under the real-valued increment law used by the
project's Rademacher `RandomWalk`, rather than its Boolean realization. -/
theorem intervalRademacherKernel_pow_apply_univ_eq_randomWalkInterval
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (intervalRademacherKernel interiorCount ^ n) start Set.univ =
      independentIncrementLaw rademacherMeasure
        {increment | InClosedInterval 1 interiorCount n
          (intervalSite start) increment} := by
  rw [intervalRademacherKernel_pow_apply_univ_eq_pathSurvival]
  have hevent :
      {branch | rademacherStaysInInterval interiorCount n
        (intervalSite start) branch} =
      rademacherIncrementPath ⁻¹'
        {increment | InClosedInterval 1 interiorCount n
          (intervalSite start) increment} := by
    ext branch
    exact rademacherStaysInInterval_iff_inClosedInterval n start branch
  rw [hevent, ← Measure.map_apply measurable_rademacherIncrementPath
    (measurableSet_inClosedInterval 1 interiorCount n (intervalSite start)),
    map_iidSequenceLaw_rademacherIncrementPath]

/-- For an odd interval started at its center, spectral survival is exactly
the symmetric horizontal-tube probability used by the public small-deviation
API. -/
theorem centeredIntervalRademacherKernel_pow_apply_univ_eq_horizontalTubeProbability
    (radius n : ℕ) :
    (intervalRademacherKernel (2 * radius + 1) ^ n)
        (⟨radius, by omega⟩ : Fin (2 * radius + 1)) Set.univ =
      horizontalTubeProbability (independentIncrementLaw rademacherMeasure)
        (1 / 2) (2 * radius) n := by
  rw [intervalRademacherKernel_pow_apply_univ_eq_randomWalkInterval]
  unfold horizontalTubeProbability
  congr 1
  ext increment
  simpa [intervalSite] using
    (inClosedInterval_centered_iff_inHorizontalTube radius n increment)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
