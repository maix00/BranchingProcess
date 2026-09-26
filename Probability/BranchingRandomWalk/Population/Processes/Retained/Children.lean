import Probability.BranchingRandomWalk.Population.Growth.AtMostTwo
import MeasureTheory.BranchingWalk.Step.Child
import Probability.BranchingRandomWalk.Tree.Filtration
import Probability.BranchingRandomWalk.Timing.Frontier

/-!
# Children retained from the current frontier

Every retained parent supplies its first child only when it exists, and its
second child only when the current child mark passes the bounded retention
test. The update is measurable and grows the population by at most a factor
of two.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory


instance : MeasurableSpace (Finset 𝕍) := ⊤

/-- The children retained from one parent, using only its current mark. -/
noncomputable def retainedChildren (M : ℝ) (frontier : Mark ℕ NatRealStep)
    (u : 𝕍) : Finset 𝕍 := by
  classical
  exact (if frontier u ∈ childPresent 0 then {u ++ [0]} else ∅) ∪
    (if frontier u ∈ keepSecond M then {u ++ [1]} else ∅)

/-- The next finite genealogical population. -/
noncomputable def growRetained (M : ℝ) (s : Finset 𝕍)
    (frontier : Mark ℕ NatRealStep) : Finset 𝕍 := by
  classical
  exact s.biUnion (retainedChildren M frontier)

theorem retainedChildren_measurable (M : ℝ) (u : 𝕍) :
    Measurable (fun frontier : Mark ℕ NatRealStep =>
      retainedChildren M frontier u) := by
  classical
  have htest : MeasurableSet
      {frontier : Mark ℕ NatRealStep | frontier u ∈ childPresent 0} :=
    (measurable_pi_apply u) (childPresent_measurable 0)
  have hsecond : MeasurableSet
      {frontier : Mark ℕ NatRealStep | frontier u ∈ keepSecond M} :=
    (measurable_pi_apply u) (keepSecond_measurable M measurableSet_Iic)
  unfold retainedChildren
  have hunion : Measurable
      (fun p : Finset 𝕍 × Finset 𝕍 => p.1 ∪ p.2) :=
    measurable_of_countable _
  exact hunion.comp
    ((measurable_const.ite htest measurable_const).prodMk
      (measurable_const.ite hsecond measurable_const))

theorem growRetained_fixed_measurable (M : ℝ) (s : Finset 𝕍) :
    Measurable (fun frontier : Mark ℕ NatRealStep =>
      growRetained M s frontier) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [growRetained]
  | @insert u s hu ih =>
      have hunion : Measurable
          (fun p : Finset 𝕍 × Finset 𝕍 => p.1 ∪ p.2) :=
        measurable_of_countable _
      have h : Measurable (fun frontier : Mark ℕ NatRealStep =>
          retainedChildren M frontier u ∪
            s.biUnion (retainedChildren M frontier)) :=
        hunion.comp ((retainedChildren_measurable M u).prodMk ih)
      simpa only [growRetained, Finset.biUnion_insert] using h

/-- The update is measurable jointly in the current finite population and
the newly revealed frontier. -/
theorem growRetained_measurable (M : ℝ) :
    Measurable (fun p : Finset 𝕍 × Mark ℕ NatRealStep =>
      growRetained M p.1 p.2) :=
  measurable_from_prod_countable_right
    (growRetained_fixed_measurable M)

theorem retainedChildren_first_mem (M : ℝ)
    (frontier : Mark ℕ NatRealStep) (u : 𝕍) :
    u ++ [0] ∈ retainedChildren M frontier u ↔
      frontier u ∈ childPresent 0 := by
  classical
  unfold retainedChildren
  by_cases hfirst : frontier u ∈ childPresent 0 <;>
    by_cases hsecond : frontier u ∈ keepSecond M <;>
      simp [hfirst, hsecond]

theorem growRetained_first_mem (M : ℝ) (s : Finset 𝕍)
    (frontier : Mark ℕ NatRealStep) (u : 𝕍) (hu : u ∈ s)
    (hfirst : frontier u ∈ childPresent 0) :
    u ++ [0] ∈ growRetained M s frontier := by
  classical
  exact Finset.mem_biUnion.mpr ⟨u, hu,
    (retainedChildren_first_mem M frontier u).2 hfirst⟩

theorem retainedChildren_card_le_two (M : ℝ)
    (frontier : Mark ℕ NatRealStep) (u : 𝕍) :
    (retainedChildren M frontier u).card ≤ 2 := by
  classical
  unfold retainedChildren
  split_ifs <;> simp

theorem growRetained_card_le_two_mul (M : ℝ) (s : Finset 𝕍)
    (frontier : Mark ℕ NatRealStep) :
    (growRetained M s frontier).card ≤ 2 * s.card := by
  classical
  calc
    (growRetained M s frontier).card ≤
        ∑ u ∈ s, (retainedChildren M frontier u).card := by
      simpa [growRetained] using
        (Finset.card_biUnion_le (s := s) (t := retainedChildren M frontier))
    _ ≤ ∑ _u ∈ s, 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact retainedChildren_card_le_two M frontier u
    _ = 2 * s.card := by simp [mul_comm]

end ProbabilityTheory.BranchingRandomWalk
