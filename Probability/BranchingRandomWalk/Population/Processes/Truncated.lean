import Probability.BranchingRandomWalk.Population.Processes.Retained.Properties
import Combinatorics.BranchingStep.Slot.Basic

/-!
# The possibly extinct at-most-two-child truncated process

This file models `Ξ⁽ᴹ⁾`: both of the first two ordered children are kept only
when their displacement is at most `M`. Hence a parent may have zero, one, or
two retained children. This differs from the backbone law `Ξ⁽ᴹ⁾ᵇ` in
`Retained.lean`, whose first child is not truncated.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



noncomputable def truncatedChildren (M : ℝ)
    (frontier : Mark ℕ NatRealStep) (u : 𝕍) :
    Finset 𝕍 := by
  classical
  exact (if frontier u ∈ keepFirst M then {u ++ [0]} else ∅) ∪
    (if frontier u ∈ keepSecond M then {u ++ [1]} else ∅)

noncomputable def growTruncated (M : ℝ) (s : Finset 𝕍)
    (frontier : Mark ℕ NatRealStep) : Finset 𝕍 := by
  classical
  exact s.biUnion (truncatedChildren M frontier)

theorem truncatedChildren_measurable (M : ℝ) (u : 𝕍) :
    Measurable (fun frontier : Mark ℕ NatRealStep =>
      truncatedChildren M frontier u) := by
  classical
  have hfirst : MeasurableSet
      {frontier : Mark ℕ NatRealStep | frontier u ∈ keepFirst M} :=
    (measurable_pi_apply u) (keepFirst_measurable M)
  have hsecond : MeasurableSet
      {frontier : Mark ℕ NatRealStep | frontier u ∈ keepSecond M} :=
    (measurable_pi_apply u) (keepSecond_measurable M)
  have hunion : Measurable
      (fun p : Finset 𝕍 × Finset 𝕍 => p.1 ∪ p.2) :=
    measurable_of_countable _
  unfold truncatedChildren
  exact hunion.comp
    ((measurable_const.ite hfirst measurable_const).prodMk
      (measurable_const.ite hsecond measurable_const))

theorem growTruncated_fixed_measurable (M : ℝ) (s : Finset 𝕍) :
    Measurable (fun frontier : Mark ℕ NatRealStep =>
      growTruncated M s frontier) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [growTruncated]
  | @insert u s hu ih =>
      have hunion : Measurable
          (fun p : Finset 𝕍 × Finset 𝕍 => p.1 ∪ p.2) :=
        measurable_of_countable _
      have h : Measurable (fun frontier : Mark ℕ NatRealStep =>
          truncatedChildren M frontier u ∪
            s.biUnion (truncatedChildren M frontier)) :=
        hunion.comp ((truncatedChildren_measurable M u).prodMk ih)
      simpa only [growTruncated, Finset.biUnion_insert] using h

theorem growTruncated_measurable (M : ℝ) :
    Measurable (fun p : Finset 𝕍 × Mark ℕ NatRealStep =>
      growTruncated M p.1 p.2) :=
  measurable_from_prod_countable_right
    (growTruncated_fixed_measurable M)

theorem truncatedChildren_card_le_two (M : ℝ)
    (frontier : Mark ℕ NatRealStep) (u : 𝕍) :
    (truncatedChildren M frontier u).card ≤ 2 := by
  classical
  unfold truncatedChildren
  split_ifs <;> simp

theorem growTruncated_card_le_two_mul (M : ℝ) (s : Finset 𝕍)
    (frontier : Mark ℕ NatRealStep) :
    (growTruncated M s frontier).card ≤ 2 * s.card := by
  classical
  calc
    (growTruncated M s frontier).card ≤
        ∑ u ∈ s, (truncatedChildren M frontier u).card := by
      simpa [growTruncated] using
        (Finset.card_biUnion_le (s := s)
          (t := truncatedChildren M frontier))
    _ ≤ ∑ _u ∈ s, 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact truncatedChildren_card_le_two M frontier u
    _ = 2 * s.card := by simp [mul_comm]

noncomputable def truncatedPopulation (M : ℝ) :
    ℕ → Mark ℕ NatRealStep → Finset 𝕍
  | 0, _ => {[]}
  | n + 1, ω =>
      growTruncated M (truncatedPopulation M n ω) (frontierMarks n ω)

theorem truncatedPopulation_adapted (M : ℝ) :
    ∀ n, Measurable[generationFiltration (M := NatRealStep) n]
      (truncatedPopulation M n) := by
  apply frontier_causal_state_adapted
    (truncatedPopulation M)
    (fun p => growTruncated M p.1 p.2)
    (growTruncated_measurable M)
  · exact measurable_const
  · intro n ω
    rfl

/-- The fully truncated process may be empty; only its binary upper bound is
unconditional. -/
theorem truncatedPopulation_card_le (M : ℝ)
    (ω : Mark ℕ NatRealStep) :
    ∀ n, (truncatedPopulation M n ω).card ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp [truncatedPopulation]
  | succ n ih =>
      have hupper := growTruncated_card_le_two_mul M
        (truncatedPopulation M n ω) (frontierMarks n ω)
      simpa [truncatedPopulation, pow_succ, mul_comm] using
        (hupper.trans (Nat.mul_le_mul_left 2 ih))

end ProbabilityTheory.BranchingRandomWalk
