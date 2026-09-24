import ThesisSpeed.Probability.Population.OneOrTwoGrowth

/-!
# A causal genealogical population

The retained population is a finite set of Ulam--Harris addresses. Every
retained parent supplies its first child; it supplies its second child only
when the current offspring mark passes the bounded retention test. The
selection is made from the current frontier, before future marks are read.
-/

open MeasureTheory

namespace ThesisSpeed

instance : MeasurableSpace (Finset TreeNode) := ⊤

/-- The children retained from one parent, using only its current mark. -/
noncomputable def retainedChildren (M : ℝ) (frontier : MarkedTree OffspringMark)
    (u : TreeNode) : Finset TreeNode := by
  classical
  exact if frontier u ∈ keepSecond M then {u ++ [0], u ++ [1]}
    else {u ++ [0]}

/-- The next finite genealogical population. -/
noncomputable def growRetained (M : ℝ) (s : Finset TreeNode)
    (frontier : MarkedTree OffspringMark) : Finset TreeNode := by
  classical
  exact s.biUnion (retainedChildren M frontier)

theorem retainedChildren_measurable (M : ℝ) (u : TreeNode) :
    Measurable (fun frontier : MarkedTree OffspringMark =>
      retainedChildren M frontier u) := by
  classical
  have htest : MeasurableSet
      {frontier : MarkedTree OffspringMark | frontier u ∈ keepSecond M} :=
    (measurable_pi_apply u) (keepSecond_measurable M)
  unfold retainedChildren
  exact measurable_const.ite htest measurable_const

theorem growRetained_fixed_measurable (M : ℝ) (s : Finset TreeNode) :
    Measurable (fun frontier : MarkedTree OffspringMark =>
      growRetained M s frontier) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [growRetained]
  | @insert u s hu ih =>
      have hunion : Measurable
          (fun p : Finset TreeNode × Finset TreeNode => p.1 ∪ p.2) :=
        measurable_of_countable _
      have h : Measurable (fun frontier : MarkedTree OffspringMark =>
          retainedChildren M frontier u ∪
            s.biUnion (retainedChildren M frontier)) :=
        hunion.comp ((retainedChildren_measurable M u).prodMk ih)
      simpa only [growRetained, Finset.biUnion_insert] using h

/-- The update is measurable jointly in the current finite population and
the newly revealed frontier. -/
theorem growRetained_measurable (M : ℝ) :
    Measurable (fun p : Finset TreeNode × MarkedTree OffspringMark =>
      growRetained M p.1 p.2) :=
  measurable_from_prod_countable_right
    (growRetained_fixed_measurable M)

theorem retainedChildren_first_mem (M : ℝ)
    (frontier : MarkedTree OffspringMark) (u : TreeNode) :
    u ++ [0] ∈ retainedChildren M frontier u := by
  classical
  unfold retainedChildren
  split_ifs <;> simp

theorem growRetained_first_mem (M : ℝ) (s : Finset TreeNode)
    (frontier : MarkedTree OffspringMark) (u : TreeNode) (hu : u ∈ s) :
    u ++ [0] ∈ growRetained M s frontier := by
  classical
  exact Finset.mem_biUnion.mpr ⟨u, hu,
    retainedChildren_first_mem M frontier u⟩

theorem retainedChildren_card_le_two (M : ℝ)
    (frontier : MarkedTree OffspringMark) (u : TreeNode) :
    (retainedChildren M frontier u).card ≤ 2 := by
  classical
  unfold retainedChildren
  split_ifs <;> simp

theorem growRetained_card_le_two_mul (M : ℝ) (s : Finset TreeNode)
    (frontier : MarkedTree OffspringMark) :
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
    ℕ → MarkedTree OffspringMark → Finset TreeNode
  | 0, _ => {[]}
  | n + 1, ω =>
      growRetained M (retainedPopulation M n ω) (frontierMarks n ω)

/-- The full set of retained genealogical identities is adapted to the
generation filtration. In particular its cardinality is adapted. -/
theorem retainedPopulation_adapted (M : ℝ) :
    ∀ n, Measurable[generationFiltration (Mark := OffspringMark) n]
      (retainedPopulation M n) := by
  apply frontier_causal_state_adapted
    (retainedPopulation M)
    (fun p => growRetained M p.1 p.2)
    (growRetained_measurable M)
  · exact measurable_const
  · intro n ω
    rfl

theorem retainedPopulation_card_adapted (M : ℝ) (n : ℕ) :
    Measurable[generationFiltration (Mark := OffspringMark) n]
      (fun ω => (retainedPopulation M n ω).card) := by
  exact (measurable_of_countable (fun s : Finset TreeNode => s.card)).comp
    (retainedPopulation_adapted M n)

/-- The causal process neither dies out nor grows faster than binary.
This estimate uses no branching probability or moment assumption. -/
theorem retainedPopulation_card_bounds (M : ℝ)
    (ω : MarkedTree OffspringMark) :
    ∀ n, 1 ≤ (retainedPopulation M n ω).card ∧
      (retainedPopulation M n ω).card ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp [retainedPopulation]
  | succ n ih =>
      have hnonempty : (retainedPopulation M n ω).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨u, hu⟩ := hnonempty
      have hfirst : u ++ [0] ∈ retainedPopulation M (n + 1) ω :=
        growRetained_first_mem M _ _ u hu
      have hupper := growRetained_card_le_two_mul M
        (retainedPopulation M n ω) (frontierMarks n ω)
      constructor
      · exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨u ++ [0], hfirst⟩)
      · simpa [retainedPopulation, pow_succ, mul_comm] using
          (hupper.trans (Nat.mul_le_mul_left 2 ih.2))

/-- Membership of a specified labelled particle is an event in the current
generation's information. This is the genealogical selection event needed
for the adapted killed-process comparison. -/
theorem retainedPopulation_mem_measurable (M : ℝ) (n : ℕ)
    (u : TreeNode) :
    MeasurableSet[generationFiltration (Mark := OffspringMark) n]
      {ω : MarkedTree OffspringMark | u ∈ retainedPopulation M n ω} := by
  have hmem : Measurable (fun s : Finset TreeNode => u ∈ s) :=
    measurable_of_countable _
  simpa using (hmem.comp (retainedPopulation_adapted M n))
    (measurableSet_singleton True)

/-- At a parent of depth `n`, the rule for retaining its second child is
decided by generation `n + 1`, together with that parent's selected status. -/
theorem retainedSecond_decision_measurable (M : ℝ) (n : ℕ)
    (u : TreeNode) (hu : u.length = n) :
    MeasurableSet[generationFiltration (Mark := OffspringMark) (n + 1)]
      {ω : MarkedTree OffspringMark |
        u ∈ retainedPopulation M n ω ∧ ω u ∈ keepSecond M} := by
  have hmember :
      MeasurableSet[generationFiltration (Mark := OffspringMark) (n + 1)]
        {ω : MarkedTree OffspringMark | u ∈ retainedPopulation M n ω} :=
    (generationFiltration (Mark := OffspringMark) |>.mono (Nat.le_succ n))
      _ (retainedPopulation_mem_measurable M n u)
  have hmark := (mark_measurable_of_depth_lt u (n + 1)
    (by rw [hu]; exact Nat.lt_succ_self n)) (keepSecond_measurable M)
  exact hmember.inter hmark

end ThesisSpeed
