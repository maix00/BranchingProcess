import ThesisSpeed.Probability.Population.Growth.AtMostTwo
import ThesisSpeed.Probability.PointProcess.Legacy.WeightedSlot
import ThesisSpeed.Probability.Genealogy.Tree.Filtration

/-!
# A causal genealogical population

The retained population is a finite set of Ulam--Harris addresses. Every
retained parent supplies its first child only when it exists; it supplies its
second child only when the current offspring mark passes the bounded retention test. The
selection is made from the current frontier, before future marks are read.
-/

open MeasureTheory

namespace ThesisSpeed

instance : MeasurableSpace (Finset 𝕍) := ⊤

/-- The children retained from one parent, using only its current mark. -/
noncomputable def retainedChildren (M : ℝ) (frontier : Mark ℕ WeightedBranchingStep)
    (u : 𝕍) : Finset 𝕍 := by
  classical
  exact (if frontier u ∈ childPresent 0 then {u ++ [0]} else ∅) ∪
    (if frontier u ∈ keepSecond M then {u ++ [1]} else ∅)

/-- The next finite genealogical population. -/
noncomputable def growRetained (M : ℝ) (s : Finset 𝕍)
    (frontier : Mark ℕ WeightedBranchingStep) : Finset 𝕍 := by
  classical
  exact s.biUnion (retainedChildren M frontier)

theorem retainedChildren_measurable (M : ℝ) (u : 𝕍) :
    Measurable (fun frontier : Mark ℕ WeightedBranchingStep =>
      retainedChildren M frontier u) := by
  classical
  have htest : MeasurableSet
      {frontier : Mark ℕ WeightedBranchingStep | frontier u ∈ childPresent 0} :=
    (measurable_pi_apply u) (childPresent_measurable 0)
  have hsecond : MeasurableSet
      {frontier : Mark ℕ WeightedBranchingStep | frontier u ∈ keepSecond M} :=
    (measurable_pi_apply u) (keepSecond_measurable M)
  unfold retainedChildren
  have hunion : Measurable
      (fun p : Finset 𝕍 × Finset 𝕍 => p.1 ∪ p.2) :=
    measurable_of_countable _
  exact hunion.comp
    ((measurable_const.ite htest measurable_const).prodMk
      (measurable_const.ite hsecond measurable_const))

theorem growRetained_fixed_measurable (M : ℝ) (s : Finset 𝕍) :
    Measurable (fun frontier : Mark ℕ WeightedBranchingStep =>
      growRetained M s frontier) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [growRetained]
  | @insert u s hu ih =>
      have hunion : Measurable
          (fun p : Finset 𝕍 × Finset 𝕍 => p.1 ∪ p.2) :=
        measurable_of_countable _
      have h : Measurable (fun frontier : Mark ℕ WeightedBranchingStep =>
          retainedChildren M frontier u ∪
            s.biUnion (retainedChildren M frontier)) :=
        hunion.comp ((retainedChildren_measurable M u).prodMk ih)
      simpa only [growRetained, Finset.biUnion_insert] using h

/-- The update is measurable jointly in the current finite population and
the newly revealed frontier. -/
theorem growRetained_measurable (M : ℝ) :
    Measurable (fun p : Finset 𝕍 × Mark ℕ WeightedBranchingStep =>
      growRetained M p.1 p.2) :=
  measurable_from_prod_countable_right
    (growRetained_fixed_measurable M)

theorem retainedChildren_first_mem (M : ℝ)
    (frontier : Mark ℕ WeightedBranchingStep) (u : 𝕍) :
    u ++ [0] ∈ retainedChildren M frontier u ↔
      frontier u ∈ childPresent 0 := by
  classical
  unfold retainedChildren
  by_cases hfirst : frontier u ∈ childPresent 0 <;>
    by_cases hsecond : frontier u ∈ keepSecond M <;>
      simp [hfirst, hsecond]

theorem growRetained_first_mem (M : ℝ) (s : Finset 𝕍)
    (frontier : Mark ℕ WeightedBranchingStep) (u : 𝕍) (hu : u ∈ s)
    (hfirst : frontier u ∈ childPresent 0) :
    u ++ [0] ∈ growRetained M s frontier := by
  classical
  exact Finset.mem_biUnion.mpr ⟨u, hu,
    (retainedChildren_first_mem M frontier u).2 hfirst⟩

theorem retainedChildren_card_le_two (M : ℝ)
    (frontier : Mark ℕ WeightedBranchingStep) (u : 𝕍) :
    (retainedChildren M frontier u).card ≤ 2 := by
  classical
  unfold retainedChildren
  split_ifs <;> simp

theorem growRetained_card_le_two_mul (M : ℝ) (s : Finset 𝕍)
    (frontier : Mark ℕ WeightedBranchingStep) :
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

/-- Start at the root and make all later choices from the current frontier. -/
noncomputable def retainedPopulation (M : ℝ) :
    ℕ → Mark ℕ WeightedBranchingStep → Finset 𝕍
  | 0, _ => {[]}
  | n + 1, ω =>
      growRetained M (retainedPopulation M n ω) (frontierMarks n ω)

/-- The full set of retained genealogical identities is adapted to the
generation filtration. In particular its cardinality is adapted. -/
theorem retainedPopulation_adapted (M : ℝ) :
    ∀ n, Measurable[generationFiltration (M := WeightedBranchingStep) n]
      (retainedPopulation M n) := by
  apply frontier_causal_state_adapted
    (retainedPopulation M)
    (fun p => growRetained M p.1 p.2)
    (growRetained_measurable M)
  · exact measurable_const
  · intro n ω
    rfl

theorem retainedPopulation_card_adapted (M : ℝ) (n : ℕ) :
    Measurable[generationFiltration (M := WeightedBranchingStep) n]
      (fun ω => (retainedPopulation M n ω).card) := by
  exact (measurable_of_countable (fun s : Finset 𝕍 => s.card)).comp
    (retainedPopulation_adapted M n)

/-- The causal process may die out, but it never grows faster than binary. -/
theorem retainedPopulation_card_le (M : ℝ)
    (ω : Mark ℕ WeightedBranchingStep) :
    ∀ n, (retainedPopulation M n ω).card ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp [retainedPopulation]
  | succ n ih =>
      have hupper := growRetained_card_le_two_mul M
        (retainedPopulation M n ω) (frontierMarks n ω)
      simpa [retainedPopulation, pow_succ, mul_comm] using
        (hupper.trans (Nat.mul_le_mul_left 2 ih))

theorem retainedPopulation_depth (M : ℝ)
    (ω : Mark ℕ WeightedBranchingStep) (n : ℕ)
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
offspring law under the thesis's at-least-one-child assumption, but generally
fails for the truncated at-most-binary comparison law. -/
theorem retainedPopulation_nonempty_of_first_child (M : ℝ)
    (ω : Mark ℕ WeightedBranchingStep)
    (hfirst : ∀ u, ω u ∈ childPresent 0) :
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
    MeasurableSet[generationFiltration (M := WeightedBranchingStep) n]
      {ω : Mark ℕ WeightedBranchingStep | u ∈ retainedPopulation M n ω} := by
  have hmem : Measurable (fun s : Finset 𝕍 => u ∈ s) :=
    measurable_of_countable _
  simpa using (hmem.comp (retainedPopulation_adapted M n))
    (measurableSet_singleton True)

/-- At a parent of depth `n`, the rule for retaining its second child is
decided by generation `n + 1`, together with that parent's selected status. -/
theorem retainedSecond_decision_measurable (M : ℝ) (n : ℕ)
    (u : 𝕍) (hu : u.length = n) :
    MeasurableSet[generationFiltration (M := WeightedBranchingStep) (n + 1)]
      {ω : Mark ℕ WeightedBranchingStep |
        u ∈ retainedPopulation M n ω ∧ ω u ∈ keepSecond M} := by
  have hmember :
      MeasurableSet[generationFiltration (M := WeightedBranchingStep) (n + 1)]
        {ω : Mark ℕ WeightedBranchingStep | u ∈ retainedPopulation M n ω} :=
    (generationFiltration (M := WeightedBranchingStep) |>.mono (Nat.le_succ n))
      _ (retainedPopulation_mem_measurable M n u)
  have hmark := (mark_measurable_of_depth_lt u (n + 1)
    (by rw [hu]; exact Nat.lt_succ_self n)) (keepSecond_measurable M)
  exact hmember.inter hmark

end ThesisSpeed
