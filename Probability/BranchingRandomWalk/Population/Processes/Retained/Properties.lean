import Probability.BranchingRandomWalk.Population.Processes.Retained.Process

/-!
# Depth, extinction, and membership events

Every retained particle has the generation's depth, extinction can only
happen when some mark lacks a first child, and membership of a labelled
particle is an event of the current generation.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory


theorem retainedPopulation_depth (M : ℝ)
    (ω : Mark ℕ NatRealStep) (n : ℕ)
    (u : 𝕍) (hu : u ∈ retainedPopulation M n ω) :
    u.length = n := by
  induction n generalizing u with
  | zero => simpa [retainedPopulation] using hu
  | succ n ih =>
      simp only [retainedPopulation, growRetained,
        Finset.mem_biUnion] at hu
      obtain ⟨p, hp, hup⟩ := hu
      have hpdepth := ih p hp
      unfold retainedChildren at hup
      split_ifs at hup <;>
        simp only [Finset.mem_union, Finset.mem_singleton,
          Finset.notMem_empty, or_false, false_or] at hup <;>
        rcases hup with rfl | rfl <;> simp [hpdepth]

/-- If every mark on the pre-sampled tree has a first child, the retained
process cannot become empty. This hypothesis applies to the original ordered
child law under the thesis's at-least-one-child assumption, but generally
fails for the truncated at-most-binary comparison law. -/
theorem retainedPopulation_nonempty_of_first_child (M : ℝ)
    (ω : Mark ℕ NatRealStep)
    (hfirst : ∀ u, present (ω u) 0) :
    ∀ n, (retainedPopulation M n ω).Nonempty := by
  intro n
  induction n with
  | zero => simp [retainedPopulation]
  | succ n ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨u ++ [0], ?_⟩
      apply growRetained_first_mem M _ _ u hu
      simpa [frontierMarks, retainedPopulation_depth M ω n u hu]
        using hfirst u

/-- Membership of a specified labelled particle is an event in the current
generation's information. This is the genealogical selection event needed
for the adapted killed-process comparison. -/
theorem retainedPopulation_mem_measurable (M : ℝ) (n : ℕ)
    (u : 𝕍) :
    MeasurableSet[generationFiltration (M := NatRealStep) n]
      {ω : Mark ℕ NatRealStep | u ∈ retainedPopulation M n ω} := by
  have hmem : Measurable (fun s : Finset 𝕍 => u ∈ s) :=
    measurable_of_countable _
  simpa using (hmem.comp (retainedPopulation_adapted M n))
    (measurableSet_singleton True)

/-- At a parent of depth `n`, the rule for retaining its second child is
decided by generation `n + 1`, together with that parent's selected status. -/
theorem retainedSecond_decision_measurable (M : ℝ) (n : ℕ)
    (u : 𝕍) (hu : u.length = n) :
    MeasurableSet[generationFiltration (M := NatRealStep) (n + 1)]
      {ω : Mark ℕ NatRealStep |
        u ∈ retainedPopulation M n ω ∧ ω u ∈ keepSecond M} := by
  have hmember :
      MeasurableSet[generationFiltration (M := NatRealStep) (n + 1)]
        {ω : Mark ℕ NatRealStep | u ∈ retainedPopulation M n ω} :=
    (generationFiltration (M := NatRealStep) |>.mono (Nat.le_succ n))
      _ (retainedPopulation_mem_measurable M n u)
  have hmark := (mark_measurable_of_depth_lt u (n + 1)
    (by rw [hu]; exact Nat.lt_succ_self n)) (keepSecond_measurable M measurableSet_Iic)
  exact hmember.inter hmark

end ProbabilityTheory.BranchingRandomWalk
