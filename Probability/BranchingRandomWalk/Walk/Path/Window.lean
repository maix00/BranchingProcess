import Combinatorics.BranchingWalk.Walk.Path.Window
import Probability.BranchingRandomWalk.Walk.Basic

/-!
# Measurable windows for finite random-walk paths
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching
open Combinatorics.Branching.Walk

theorem measurableSet_inWindows {E : Type*} [MeasurableSpace E] {n : ℕ}
    (window : Fin (n + 1) → Set E)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    MeasurableSet {path : Fin (n + 1) → E | InWindows window path} := by
  rw [show {path : Fin (n + 1) → E | InWindows window path} =
      ⋂ k, {path | path k ∈ window k} by
    ext path
    simp [InWindows]]
  exact MeasurableSet.iInter fun k =>
    (hwindow k).preimage (measurable_pi_apply k)

theorem measurableSet_inClosedInterval
    (lower upper : ℝ) (n : ℕ) (initial : ℝ) :
    MeasurableSet {increment : ℕ → ℝ |
      InClosedInterval lower upper n initial increment} := by
  exact (measurableSet_inWindows
    (fun _ : Fin (n + 1) => Set.Icc lower upper)
    (fun _ => measurableSet_Icc)).preimage (history_measurable n initial)

theorem measurableSet_finiteInClosedInterval
    (lower upper initial : ℝ) (n : ℕ) :
    MeasurableSet {increment : Fin n → ℝ |
      FiniteInClosedInterval lower upper initial increment} := by
  rw [show {increment : Fin n → ℝ |
        FiniteInClosedInterval lower upper initial increment} =
      ⋂ k : Fin (n + 1), {increment | initial +
        ∑ j : Fin k, increment
          ⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩ ∈
            Set.Icc lower upper} by
    ext increment
    simp [FiniteInClosedInterval]]
  exact MeasurableSet.iInter fun k => measurableSet_Icc.preimage
    (measurable_const.add <| Finset.measurable_sum Finset.univ fun j _ =>
      measurable_pi_apply
        (⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩ : Fin n))

/-- A possibly killed `RandomWalk` remains alive and in a closed interval at
every time through `n`.  The `Option` process makes death explicit. -/
def ProcessInClosedInterval {Mark : Type*} [MeasurableSpace Mark]
    (d : Mark → ℝ) (lower upper : ℝ) (n : ℕ)
    (walk : Walk Mark ℝ) : Prop :=
  ∀ k : Fin (n + 1),
    process d k walk ∈ some '' Set.Icc lower upper

theorem measurableSet_processInClosedInterval
    {Mark : Type*} [MeasurableSpace Mark]
    (d : Mark → ℝ) (hd : Measurable d)
    (lower upper : ℝ) (n : ℕ) :
    MeasurableSet {walk : Walk Mark ℝ |
      ProcessInClosedInterval d lower upper n walk} := by
  rw [show {walk : Walk Mark ℝ |
      ProcessInClosedInterval d lower upper n walk} =
      ⋂ k : Fin (n + 1),
        process d k ⁻¹' (some '' Set.Icc lower upper) by
    ext walk
    simp [ProcessInClosedInterval]]
  exact MeasurableSet.iInter fun k =>
    (measurableSet_option_some_image measurableSet_Icc).preimage
      (process_measurable d hd k)

theorem processInClosedInterval_ofIncrements_iff
    (lower upper : ℝ) (n : ℕ) (initial : ℝ)
    (increment : ℕ → ℝ) :
    ProcessInClosedInterval id lower upper n
        (Walk.ofIncrements initial increment) ↔
      InClosedInterval lower upper n initial increment := by
  simp only [ProcessInClosedInterval, process_ofIncrements,
    Set.mem_image, Option.some.injEq, InClosedInterval,
    InWindows, history, positionProcess]
  constructor
  · intro h k
    obtain ⟨x, hx, rfl⟩ := h k
    simpa [partialSum] using hx
  · intro h k
    refine ⟨initial + ∑ j ∈ Finset.range (k : ℕ), increment j, ?_, rfl⟩
    simpa [partialSum] using h k

/-- Indicator of a finite path-window event. -/
noncomputable def windowTest {E : Type*} {n : ℕ}
    (window : Fin (n + 1) → Set E) :
    (Fin (n + 1) → E) → ENNReal :=
  {path | InWindows window path}.indicator fun _ => 1

theorem windowTest_measurable {E : Type*} [MeasurableSpace E] {n : ℕ}
    (window : Fin (n + 1) → Set E)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    Measurable (windowTest window) :=
  measurable_const.indicator (measurableSet_inWindows window hwindow)

@[simp] theorem windowTest_eq_one_iff {E : Type*} {n : ℕ}
    (window : Fin (n + 1) → Set E) (path : Fin (n + 1) → E) :
    windowTest window path = 1 ↔ InWindows window path := by
  simp [windowTest]

@[simp] theorem windowTest_eq_zero_iff {E : Type*} {n : ℕ}
    (window : Fin (n + 1) → Set E) (path : Fin (n + 1) → E) :
    windowTest window path = 0 ↔ ¬InWindows window path := by
  simp [windowTest]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
