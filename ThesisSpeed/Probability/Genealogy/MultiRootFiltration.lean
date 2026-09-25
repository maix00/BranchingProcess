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

end ThesisSpeed
