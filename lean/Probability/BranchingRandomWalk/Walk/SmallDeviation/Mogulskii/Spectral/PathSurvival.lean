import Probability.BranchingRandomWalk.Walk.Rademacher
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.KilledTransition

/-!
# Path interpretation of killed Rademacher transitions

The finite-state killed transition survives exactly when every partial sum of
the corresponding Rademacher increment path remains at an interior lattice
site.  This file is the path-level bridge between the spectral kernel and the
random-walk formulation.
-/

open MeasureTheory Set

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii

/-- Real coordinate represented by an interior finite-interval state. -/
def intervalSite {interiorCount : ℕ} (i : Fin interiorCount) : ℝ :=
  i.val + 1

/-- One Boolean Rademacher transition, killed when it leaves the finite
interior interval. -/
def intervalRademacherNext {interiorCount : ℕ}
    (i : Fin interiorCount) (step : Bool) : Option (Fin interiorCount) :=
  if step then intervalRightNeighbor i else intervalLeftNeighbor i

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

theorem intervalRademacherNext_eq_some_iff
    {interiorCount : ℕ} (i : Fin interiorCount) (step : Bool) (j : Fin interiorCount) :
    intervalRademacherNext i step = some j ↔
      intervalSite j = intervalSite i + rademacherOfBool step := by
  cases step <;>
    (simp [intervalRademacherNext, intervalLeftNeighbor_eq_some_iff,
      intervalRightNeighbor_eq_some_iff, rademacherOfBool] <;> ring_nf)

/-- A one-step Rademacher move survives precisely when its new real
coordinate is one of the interior sites `1, ..., interiorCount`. -/
theorem intervalRademacherNext_isSome_iff
    {interiorCount : ℕ} (i : Fin interiorCount) (step : Bool) :
    (intervalRademacherNext i step).isSome ↔
      1 ≤ intervalSite i + rademacherOfBool step ∧
        intervalSite i + rademacherOfBool step ≤ interiorCount := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    have hsite := (intervalRademacherNext_eq_some_iff i step j).mp hj
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
        simp [intervalRademacherNext, intervalLeftNeighbor, hi]
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
        simp [intervalRademacherNext, intervalRightNeighbor, hi]

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

/-- The killed finite-state transition survives a Boolean history exactly
when the corresponding Rademacher path stays inside the interval. -/
theorem runPartialTransitions_isSome_iff_staysInInterval
    {interiorCount : ℕ} (n : ℕ) (i : Fin interiorCount) (branch : ℕ → Bool) :
    (Kernel.runPartialTransitions intervalRademacherNext n i
        (Kernel.sequencePrefix n branch)).isSome ↔
      rademacherStaysInInterval interiorCount n (intervalSite i) branch := by
  induction n generalizing i branch with
  | zero => simp [Kernel.runPartialTransitions, rademacherStaysInInterval]
  | succ n ih =>
      simp only [Kernel.runPartialTransitions, Kernel.sequencePrefix,
        rademacherStaysInInterval]
      cases hnext : intervalRademacherNext i (branch 0) with
      | none =>
          have hkilled : ¬ (1 ≤ intervalSite i + rademacherOfBool (branch 0) ∧
              intervalSite i + rademacherOfBool (branch 0) ≤ interiorCount) := by
            rw [← intervalRademacherNext_isSome_iff i (branch 0)]
            simp [hnext]
          have hnext' : intervalRademacherNext i (branch (↑(0 : Fin (n + 1)))) = none :=
            hnext
          rw [hnext']
          simp only [Option.bind_none, Option.isSome_none, Bool.false_eq]
          tauto
      | some j =>
          have hsite : intervalSite j =
              intervalSite i + rademacherOfBool (branch 0) :=
            (intervalRademacherNext_eq_some_iff i (branch 0) j).mp hnext
          have hinside : 1 ≤ intervalSite i + rademacherOfBool (branch 0) ∧
              intervalSite i + rademacherOfBool (branch 0) ≤ interiorCount :=
            (intervalRademacherNext_isSome_iff i (branch 0)).mp (by simp [hnext])
          have htail : Fin.tail (Kernel.sequencePrefix (n + 1) branch) =
              Kernel.sequencePrefix n (fun k => branch (k + 1)) := by
            funext k
            rfl
          have hnext' : intervalRademacherNext i (branch (↑(0 : Fin (n + 1)))) = some j :=
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
        (Kernel.survivingPartialTransitionHistories intervalRademacherNext
          n start : Set (Fin n → Bool)) =
      {branch | rademacherStaysInInterval interiorCount n
        (intervalSite start) branch} := by
  ext branch
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    Kernel.survivingPartialTransitionHistories, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact runPartialTransitions_isSome_iff_staysInInterval n start branch

/-- The total mass of the killed interval kernel is the probability of the
corresponding canonical Rademacher small-deviation event. -/
theorem intervalRademacherKernel_pow_apply_univ_eq_pathSurvival
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (intervalRademacherKernel interiorCount ^ n) start Set.univ =
      iidSequenceLaw fairBoolMeasure
        {branch | rademacherStaysInInterval interiorCount n
          (intervalSite start) branch} := by
  rw [intervalRademacherKernel_pow_apply_univ_eq_iid]
  change iidSequenceLaw fairBoolMeasure
      ((Kernel.sequencePrefix (ξ := Bool) n) ⁻¹'
        (Kernel.survivingPartialTransitionHistories intervalRademacherNext
          n start : Set (Fin n → Bool))) = _
  rw [survivingHistories_preimage_eq_staysInInterval]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii
