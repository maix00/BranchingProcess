import ThesisSpeed.Probability.Genealogy.MultiRoot.Law

/-!
# The multi-root generation filtration

Information from all initial ancestors through generation `n`, the filtration
it generates, and the measurability of fixed marks and of marks at a
generation-measurably selected address.
-/

open MeasureTheory

namespace ThesisSpeed

/-- Information from all initial ancestors through generation `n`. -/
@[instance_reducible] def multiRootGenerationSpace (m n : ℕ) :
    MeasurableSpace (MultiRootMark m) :=
  MeasurableSpace.generateFrom
    {s | ∃ i : Fin m, ∃ u : 𝕍, u.length < n ∧
      ∃ t : Set NatRealBranchingStep, MeasurableSet t ∧
        s = {ω : MultiRootMark m | ω i u ∈ t}}

def multiRootFiltration (m : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (MultiRootMark m)) where
  seq := multiRootGenerationSpace m
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

theorem multiRootGenerationSpace_zero (m : ℕ) :
    multiRootGenerationSpace m 0 = ⊥ := by
  unfold multiRootGenerationSpace
  have hgen :
      {s : Set (MultiRootMark m) |
        ∃ i : Fin m, ∃ u : 𝕍, u.length < 0 ∧
          ∃ t : Set NatRealBranchingStep, MeasurableSet t ∧
            s = {ω : MultiRootMark m | ω i u ∈ t}} = ∅ := by
    ext s
    simp
  rw [hgen, MeasurableSpace.generateFrom_empty]

theorem multiRootMark_measurable (m n : ℕ) (i : Fin m)
    (u : 𝕍) (hu : u.length < n) :
    Measurable[multiRootFiltration m n]
      (fun ω : MultiRootMark m => ω i u) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, u, hu, t, ht, rfl⟩

/-- A generation-measurably selected address within a fixed labelled root
has an observable mark whenever its depth has already been revealed. -/
theorem multiRootSelectedMark_measurable {m n : ℕ} (i : Fin m)
    (chosen : MultiRootMark m → 𝕍)
    (hchosen : Measurable[multiRootFiltration m n] chosen)
    (hdepth : ∀ ω, (chosen ω).length < n) :
    Measurable[multiRootFiltration m n]
      (fun ω : MultiRootMark m => ω i (chosen ω)) := by
  intro t ht
  have hset :
      {ω : MultiRootMark m | ω i (chosen ω) ∈ t} =
        ⋃ u : 𝕍,
          {ω : MultiRootMark m | chosen ω = u} ∩
            {ω : MultiRootMark m | ω i u ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hmark⟩
      simpa [hu] using hmark
  change MeasurableSet[multiRootFiltration m n]
    {ω : MultiRootMark m | ω i (chosen ω) ∈ t}
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length < n
  · exact (hchosen (measurableSet_singleton u)).inter
      ((multiRootMark_measurable m n i u hu) ht)
  · have hempty : {ω : MultiRootMark m | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

end ThesisSpeed
