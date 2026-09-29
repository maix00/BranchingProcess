import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.PathSurvival
import Probability.Kernel.FiniteState.Matrix
import Probability.Kernel.Step.Endpoint

/-!
# Path interpretation of finite spectral target masses

A target mass of the killed interval matrix is exactly the Rademacher
probability of staying in the finite interval and ending in the target.
This is the bridge needed before applying the closed-event Portmanteau
inequality to spectral lower bounds.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProbabilityTheory.RandomWalk.Mogulskii

open Combinatorics.Branching.Walk

private theorem intervalRademacher_runPartialSteps_eq_some_iff
    {interiorCount n : ℕ} (start finish : Fin interiorCount)
    (branch : ℕ → Bool) :
    Kernel.runPartialSteps intervalRademacherStep n start
        (Kernel.sequencePrefix n branch) = some finish ↔
      rademacherStaysInInterval interiorCount n (intervalSite start) branch ∧
        intervalSite finish = intervalSite start +
          partialSum n (rademacherIncrementPath branch) := by
  induction n generalizing start finish branch with
  | zero =>
      simp only [Kernel.runPartialSteps,
        Option.some.injEq, rademacherStaysInInterval,
        partialSum_zero, add_zero]
      constructor
      · intro h
        subst finish
        simp [intervalSite]
      · intro h
        apply Fin.ext
        have h' := h
        simp [intervalSite] at h'
        exact_mod_cast h'.symm
  | succ n ih =>
      change
        (intervalRademacherStep start (branch 0)).bind
          (fun next => Kernel.runPartialSteps intervalRademacherStep n next
            (Kernel.sequencePrefix n (fun k => branch (k + 1)))) =
          some finish ↔ _
      cases hstep : intervalRademacherStep start (branch 0) with
      | none =>
          have hkill : ¬ (1 ≤ intervalSite start + rademacherOfBool (branch 0) ∧
              intervalSite start + rademacherOfBool (branch 0) ≤ interiorCount) := by
            rw [← intervalRademacherStep_isSome_iff]
            simp [hstep]
          simp only [Option.bind_none, rademacherStaysInInterval]
          constructor
          · intro h
            simp at h
          · intro h
            have hvalid' :
                1 ≤ intervalSite start + rademacherOfBool (branch 0) ∧
                  intervalSite start + rademacherOfBool (branch 0) ≤ interiorCount :=
              ⟨h.1.1, h.1.2.1⟩
            exact False.elim (hkill hvalid')
      | some next =>
          have hsite : intervalSite next =
              intervalSite start + rademacherOfBool (branch 0) :=
            (intervalRademacherStep_eq_some_iff start (branch 0) next).mp hstep
          have hvalid :
              1 ≤ intervalSite start + rademacherOfBool (branch 0) ∧
                intervalSite start + rademacherOfBool (branch 0) ≤ interiorCount :=
            (intervalRademacherStep_isSome_iff start (branch 0)).mp (by simp [hstep])
          simp only [Option.bind_some]
          rw [ih next finish (fun k => branch (k + 1))]
          have hsum : partialSum (n + 1) (rademacherIncrementPath branch) =
              rademacherOfBool (branch 0) +
                partialSum n (fun k => rademacherOfBool (branch (k + 1))) := by
            rw [partialSum_succ_eq_head_add_tail]
            change rademacherIncrementPath branch 0 +
                partialSum n (incrementTail (rademacherIncrementPath branch)) = _
            congr 1
          have htailSum :
              partialSum n (rademacherIncrementPath (fun k => branch (k + 1))) =
                partialSum n (fun k => rademacherOfBool (branch (k + 1))) := by
            rfl
          constructor
          · rintro ⟨hstay, hend⟩
            refine ⟨⟨hvalid.1, hvalid.2, ?_⟩, ?_⟩
            · simpa [hsite] using hstay
            · calc
                intervalSite finish = intervalSite next +
                    partialSum n (rademacherIncrementPath fun k => branch (k + 1)) := hend
                _ = intervalSite start +
                    (rademacherOfBool (branch 0) +
                      partialSum n (rademacherIncrementPath fun k => branch (k + 1))) := by
                  rw [hsite]
                  ring
                _ = intervalSite start +
                    partialSum (n + 1) (rademacherIncrementPath branch) := by
                  rw [htailSum, hsum]
          · rintro ⟨⟨hlo, hhi, hstay⟩, hend⟩
            refine ⟨?_, ?_⟩
            · simpa [hsite] using hstay
            · calc
                intervalSite finish = intervalSite start +
                    partialSum (n + 1) (rademacherIncrementPath branch) := hend
                _ = intervalSite start +
                    (rademacherOfBool (branch 0) +
                      partialSum n (rademacherIncrementPath fun k => branch (k + 1))) := by
                  rw [hsum, htailSum]
                _ = intervalSite next +
                    partialSum n (rademacherIncrementPath fun k => branch (k + 1)) := by
                  rw [← add_assoc, hsite]

private theorem runPartialSteps_endsIn_iff_exists_eq
    {α ξ : Type*} (step : α → ξ → Option α)
    {target : Set α} {n : ℕ} {start : α} {history : Fin n → ξ} :
    Kernel.EndsIn step target n start history ↔
      ∃ finish, finish ∈ target ∧
    Kernel.runPartialSteps step n start history = some finish := by
  simp only [Kernel.EndsIn, Set.mem_image]
  constructor
  · rintro ⟨finish, hfinish, hEq⟩
    exact ⟨finish, hfinish, hEq.symm⟩
  · rintro ⟨finish, hfinish, hEq⟩
    exact ⟨finish, hfinish, hEq.symm⟩

/-- The endpoint set of a finite killed Rademacher history is exactly the
set of sums of its surviving increments whose terminal state is selected. -/
theorem intervalRademacher_endsInPrefix_iff_pathEvent
    {interiorCount n : ℕ} (start : Fin interiorCount)
    (target : Finset (Fin interiorCount)) (branch : ℕ → Bool) :
    Kernel.EndsInPrefix intervalRademacherStep (target : Set (Fin interiorCount))
        n start branch ↔
      rademacherStaysInInterval interiorCount n (intervalSite start) branch ∧
        intervalSite start + partialSum n (rademacherIncrementPath branch) ∈
          intervalSite '' (target : Set (Fin interiorCount)) := by
  rw [Kernel.EndsInPrefix, runPartialSteps_endsIn_iff_exists_eq]
  constructor
  · rintro ⟨finish, hfinish, hrun⟩
    have hpath := (intervalRademacher_runPartialSteps_eq_some_iff
      start finish branch).mp hrun
    refine ⟨hpath.1, ?_⟩
    rw [← hpath.2]
    exact ⟨finish, hfinish, rfl⟩
  · rintro ⟨hstay, ⟨finish, hfinish, hend⟩⟩
    refine ⟨finish, hfinish, ?_⟩
    exact (intervalRademacher_runPartialSteps_eq_some_iff
      start finish branch).mpr ⟨hstay, hend⟩

private theorem measurableSet_intervalRademacherPathTarget
    {interiorCount n : ℕ} (start : Fin interiorCount)
    (target : Finset (Fin interiorCount)) :
    MeasurableSet {increment : ℕ → ℝ |
      InClosedInterval 1 interiorCount n (intervalSite start) increment ∧
        intervalSite start + partialSum n increment ∈
          intervalSite '' (target : Set (Fin interiorCount))} := by
  apply (measurableSet_inClosedInterval 1 interiorCount n
    (intervalSite start)).inter
  have hfinite : (intervalSite '' (target : Set (Fin interiorCount))).Finite :=
    target.finite_toSet.image intervalSite
  exact hfinite.measurableSet.preimage
    (measurable_const.add (partialSum_measurable n))

/-- Target mass of the killed Rademacher kernel equals the IID increment
probability of staying in the interval and ending in a chosen finite set. -/
theorem intervalRademacherKernel_pow_apply_finset_eq_iidPathEvent
    (interiorCount n : ℕ) (start : Fin interiorCount)
    (target : Finset (Fin interiorCount)) :
    (intervalRademacherKernel interiorCount ^ n) start (target : Set (Fin interiorCount)) =
      independentIncrementLaw rademacherMeasure
        {increment : ℕ → ℝ |
          InClosedInterval 1 interiorCount n (intervalSite start) increment ∧
            intervalSite start + partialSum n increment ∈
              intervalSite '' (target : Set (Fin interiorCount))} := by
  rw [intervalRademacherKernel_eq_ofPartialStep]
  rw [Kernel.pow_apply_ofPartialStep_eq_iidSequenceLaw
    (ν := fairBoolMeasure) (step := intervalRademacherStep)
    (hstep := measurable_of_countable _)
    (target := (target : Set (Fin interiorCount)))
    (htarget := target.finite_toSet.measurableSet) n start]
  rw [← ProbabilityTheory.RandomWalk.map_iidSequenceLaw_rademacherIncrementPath]
  rw [Measure.map_apply measurable_rademacherIncrementPath
    (measurableSet_intervalRademacherPathTarget start target)]
  congr 1
  ext branch
  change Kernel.EndsInPrefix intervalRademacherStep
      (target : Set (Fin interiorCount)) n start branch ↔
    InClosedInterval 1 interiorCount n (intervalSite start)
        (rademacherIncrementPath branch) ∧
      intervalSite start +
          partialSum n (rademacherIncrementPath branch) ∈
        intervalSite '' (target : Set (Fin interiorCount))
  rw [intervalRademacher_endsInPrefix_iff_pathEvent]
  rw [rademacherStaysInInterval_iff_inClosedInterval n start branch]

/-- The matrix-power sum over a finite target set has the same path
interpretation as its measure-valued killed-kernel target mass. -/
theorem ofReal_intervalKernel_pow_apply_finset_eq_iidPathEvent
    (interiorCount n : ℕ) (start : Fin interiorCount)
    (target : Finset (Fin interiorCount)) :
    ENNReal.ofReal
        (∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish) =
      independentIncrementLaw rademacherMeasure
        {increment : ℕ → ℝ |
          InClosedInterval 1 interiorCount n (intervalSite start) increment ∧
            intervalSite start + partialSum n increment ∈
              intervalSite '' (target : Set (Fin interiorCount))} := by
  rw [← Kernel.ofRealMatrix_pow_apply_finset
      (intervalKernel_nonneg interiorCount) n start target]
  rw [← intervalRademacherKernel_eq_ofRealMatrix]
  exact intervalRademacherKernel_pow_apply_finset_eq_iidPathEvent
    interiorCount n start target
