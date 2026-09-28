import Probability.BranchingRandomWalk.Walk.Path

/-!
# Measurable windows for finite random-walk paths
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching

/-- A finite path remains in the prescribed window at every coordinate. -/
def InWindows {n : ℕ} (window : Fin (n + 1) → Set ℝ)
    (path : Fin (n + 1) → ℝ) : Prop :=
  ∀ k, path k ∈ window k

theorem measurableSet_inWindows {n : ℕ}
    (window : Fin (n + 1) → Set ℝ)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    MeasurableSet {path : Fin (n + 1) → ℝ | InWindows window path} := by
  rw [show {path : Fin (n + 1) → ℝ | InWindows window path} =
      ⋂ k, {path | path k ∈ window k} by
    ext path
    simp [InWindows]]
  exact MeasurableSet.iInter fun k =>
    (hwindow k).preimage (measurable_pi_apply k)

/-- A random-walk increment path, including its time-zero position, remains
in a fixed closed interval through time `n`. -/
def InClosedInterval (lower upper : ℝ) (n : ℕ) (initial : ℝ)
    (increment : ℕ → ℝ) : Prop :=
  InWindows (fun _ : Fin (n + 1) => Set.Icc lower upper)
    (history n initial increment)

theorem measurableSet_inClosedInterval
    (lower upper : ℝ) (n : ℕ) (initial : ℝ) :
    MeasurableSet {increment : ℕ → ℝ |
      InClosedInterval lower upper n initial increment} := by
  exact (measurableSet_inWindows
    (fun _ : Fin (n + 1) => Set.Icc lower upper)
    (fun _ => measurableSet_Icc)).preimage (history_measurable n initial)

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
    InWindows, history, id_eq]
  constructor
  · intro h k
    obtain ⟨x, hx, rfl⟩ := h k
    simpa [partialSum] using hx
  · intro h k
    refine ⟨initial + ∑ j ∈ Finset.range (k : ℕ), increment j, ?_, rfl⟩
    simpa [partialSum] using h k

/-- Indicator of a finite path-window event. -/
noncomputable def windowTest {n : ℕ}
    (window : Fin (n + 1) → Set ℝ) :
    (Fin (n + 1) → ℝ) → ENNReal :=
  {path | InWindows window path}.indicator fun _ => 1

theorem windowTest_measurable {n : ℕ}
    (window : Fin (n + 1) → Set ℝ)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    Measurable (windowTest window) :=
  measurable_const.indicator (measurableSet_inWindows window hwindow)

@[simp] theorem windowTest_eq_one_iff {n : ℕ}
    (window : Fin (n + 1) → Set ℝ) (path : Fin (n + 1) → ℝ) :
    windowTest window path = 1 ↔ InWindows window path := by
  simp [windowTest]

@[simp] theorem windowTest_eq_zero_iff {n : ℕ}
    (window : Fin (n + 1) → Set ℝ) (path : Fin (n + 1) → ℝ) :
    windowTest window path = 0 ↔ ¬InWindows window path := by
  simp [windowTest]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
