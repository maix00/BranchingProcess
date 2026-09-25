import Probability.BranchingRandomWalk.Population.Processes.Retained.Children

/-!
# The causal genealogical population

Starting at the root, every later choice is made from the current frontier,
before future marks are read. The population is therefore adapted to the
generation filtration, and its cardinality is adapted as well.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory


/-- Start at the root and make all later choices from the current frontier. -/
noncomputable def retainedPopulation (M : ℝ) :
    ℕ → Mark ℕ NatRealStep → Finset 𝕍
  | 0, _ => {[]}
  | n + 1, ω =>
      growRetained M (retainedPopulation M n ω) (frontierMarks n ω)

/-- The full set of retained genealogical identities is adapted to the
generation filtration. In particular its cardinality is adapted. -/
theorem retainedPopulation_adapted (M : ℝ) :
    ∀ n, Measurable[generationFiltration (M := NatRealStep) n]
      (retainedPopulation M n) := by
  apply frontier_causal_state_adapted
    (retainedPopulation M)
    (fun p => growRetained M p.1 p.2)
    (growRetained_measurable M)
  · exact measurable_const
  · intro n ω
    rfl

theorem retainedPopulation_card_adapted (M : ℝ) (n : ℕ) :
    Measurable[generationFiltration (M := NatRealStep) n]
      (fun ω => (retainedPopulation M n ω).card) := by
  exact (measurable_of_countable (fun s : Finset 𝕍 => s.card)).comp
    (retainedPopulation_adapted M n)

/-- The causal process may die out, but it never grows faster than binary. -/
theorem retainedPopulation_card_le (M : ℝ)
    (ω : Mark ℕ NatRealStep) :
    ∀ n, (retainedPopulation M n ω).card ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp [retainedPopulation]
  | succ n ih =>
      have hupper := growRetained_card_le_two_mul M
        (retainedPopulation M n ω) (frontierMarks n ω)
      simpa [retainedPopulation, pow_succ, mul_comm] using
        (hupper.trans (Nat.mul_le_mul_left 2 ih))

end ProbabilityTheory.BranchingRandomWalk
