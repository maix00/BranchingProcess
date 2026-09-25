import ThesisSpeed.Probability.Genealogy.MultiRootAbstract

open MeasureTheory

namespace ThesisSpeed

@[instance_reducible] def multiRootStepGenerationSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (MultiRootStepField m X) :=
  MeasurableSpace.generateFrom
    {s | ∃ i : Fin m, ∃ u : TreeNode, u.length < n ∧
      ∃ t : Set (BranchingStep ℕ X), MeasurableSet t ∧
        s = {ω : MultiRootStepField m X | ω i u ∈ t}}

def multiRootStepFiltration
    {m : ℕ} {X : Type*} [MeasurableSpace X] :
    Filtration ℕ (inferInstance : MeasurableSpace (MultiRootStepField m X)) where
  seq := multiRootStepGenerationSpace
  mono' := by
    intro n k hnk
    apply MeasurableSpace.generateFrom_mono
    rintro s ⟨i, u, hu, t, ht, rfl⟩
    exact ⟨i, u, lt_of_lt_of_le hu hnk, t, ht, rfl⟩
  le' := by
    intro n
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨i, u, hu, t, ht, rfl⟩
    exact ((measurable_pi_apply u).comp (measurable_pi_apply i)) ht

theorem multiRootStepGenerationSpace_zero
    {m : ℕ} {X : Type*} [MeasurableSpace X] :
    multiRootStepGenerationSpace (m := m) (X := X) 0 = ⊥ := by
  unfold multiRootStepGenerationSpace
  have hgen :
      {s : Set (MultiRootStepField m X) |
        ∃ i : Fin m, ∃ u : TreeNode, u.length < 0 ∧
          ∃ t : Set (BranchingStep ℕ X), MeasurableSet t ∧
            s = {ω : MultiRootStepField m X | ω i u ∈ t}} = ∅ := by
    ext s
    simp
  rw [hgen, MeasurableSpace.generateFrom_empty]

theorem multiRootStep_measurable
    {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m) (u : TreeNode) (hu : u.length < n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : MultiRootStepField m X => ω i u) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, u, hu, t, ht, rfl⟩

theorem multiRootSelectedStep_measurable
    {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m)
    (chosen : MultiRootStepField m X → TreeNode)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length < n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : MultiRootStepField m X => ω i (chosen ω)) := by
  intro t ht
  have hset :
      {ω : MultiRootStepField m X | ω i (chosen ω) ∈ t} =
        ⋃ u : TreeNode,
          {ω : MultiRootStepField m X | chosen ω = u} ∩
            {ω : MultiRootStepField m X | ω i u ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hmark⟩
      simpa [hu] using hmark
  change MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
    {ω : MultiRootStepField m X | ω i (chosen ω) ∈ t}
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length < n
  · exact (hchosen (measurableSet_singleton u)).inter
      ((multiRootStep_measurable (X := X) i u hu) ht)
  · have hempty :
        {ω : MultiRootStepField m X | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

theorem multiRootRealizedNode_measurableSet
    {m : ℕ} (i : Fin m) (u : TreeNode) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) u.length]
      {ω : MultiRootStepField m ℝ | multiRootRealizedNode ω i u} := by
  have hset : {ω : MultiRootStepField m ℝ |
      multiRootRealizedNode ω i u} =
      ⋂ j ∈ Finset.range u.length,
        {ω : MultiRootStepField m ℝ |
          branchingStepPresent (ω i (u.take j)) (u[j]!)} := by
    ext ω
    simp [multiRootRealizedNode, branchingRealizedNode]
  rw [hset]
  apply Finset.measurableSet_biInter
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjlt), hjlt]
  exact (multiRootStep_measurable (X := ℝ) i (u.take j) hprefix)
    (branchingStepPresent_measurableSet (X := ℝ) (u[j]!))

theorem multiRootAbsolutePosition_real_measurable
    {m : ℕ} (initial : Fin m → ℝ) (i : Fin m) (u : TreeNode) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) u.length]
      (fun ω : MultiRootStepField m ℝ =>
        multiRootAbsolutePosition initial ω i u) := by
  unfold multiRootAbsolutePosition multiRootNodePosition branchingTreePathSum
  apply measurable_const.add
  apply Finset.measurable_fun_sum
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjlt), hjlt]
  exact (branchingStepIncrement_measurable (X := ℝ) (u[j]!)).comp
    (multiRootStep_measurable (X := ℝ) i (u.take j) hprefix)

end ThesisSpeed
