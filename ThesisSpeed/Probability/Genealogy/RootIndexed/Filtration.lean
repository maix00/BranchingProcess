import ThesisSpeed.Probability.Genealogy.RootIndexed.Positions

open MeasureTheory

namespace ThesisSpeed

@[instance_reducible] def multiRootStepGenerationSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (FiniteRootBranchingStepField m X) :=
  MeasurableSpace.generateFrom
    {s | ∃ i : Fin m, ∃ u : 𝕍, u.length < n ∧
      ∃ t : Set (BranchingStep ℕ X), MeasurableSet t ∧
        s = {ω : FiniteRootBranchingStepField m X | ω i u ∈ t}}

def multiRootStepFiltration
    {m : ℕ} {X : Type*} [MeasurableSpace X] :
    Filtration ℕ (inferInstance : MeasurableSpace (FiniteRootBranchingStepField m X)) where
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
      {s : Set (FiniteRootBranchingStepField m X) |
        ∃ i : Fin m, ∃ u : 𝕍, u.length < 0 ∧
          ∃ t : Set (BranchingStep ℕ X), MeasurableSet t ∧
            s = {ω : FiniteRootBranchingStepField m X | ω i u ∈ t}} = ∅ := by
    ext s
    simp
  rw [hgen, MeasurableSpace.generateFrom_empty]

theorem multiRootStep_measurable
    {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m) (u : 𝕍) (hu : u.length < n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootBranchingStepField m X => ω i u) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, u, hu, t, ht, rfl⟩

theorem multiRootSelectedStep_measurable
    {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m)
    (chosen : FiniteRootBranchingStepField m X → 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length < n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootBranchingStepField m X => ω i (chosen ω)) := by
  intro t ht
  have hset :
      {ω : FiniteRootBranchingStepField m X | ω i (chosen ω) ∈ t} =
        ⋃ u : 𝕍,
          {ω : FiniteRootBranchingStepField m X | chosen ω = u} ∩
            {ω : FiniteRootBranchingStepField m X | ω i u ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hmark⟩
      simpa [hu] using hmark
  change MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
    {ω : FiniteRootBranchingStepField m X | ω i (chosen ω) ∈ t}
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length < n
  · exact (hchosen (measurableSet_singleton u)).inter
      ((multiRootStep_measurable (X := X) i u hu) ht)
  · have hempty :
        {ω : FiniteRootBranchingStepField m X | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

/-- Realization along a remaining path, root by root. Same induction as in the
single-root case; the address is carried along so each step only needs the
step at one fixed address of one fixed root. -/
theorem rootIndexedStepPresentAlong_measurableSet {m : ℕ} (i : Fin m)
    (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
      {ω : FiniteRootBranchingStepField m ℝ |
        branchingStepPresentAlong (ω i) v p} := by
  induction p generalizing v with
  | nil =>
      have hset : {ω : FiniteRootBranchingStepField m ℝ |
          branchingStepPresentAlong (ω i) v []} = Set.univ := by
        ext ω
        simp
      rw [hset]
      exact MeasurableSet.univ
  | cons j p ih =>
      have hlen : (v ++ [j]).length = v.length + 1 := by simp
      have hlen' : (j :: p).length = p.length + 1 := by simp
      have hset : {ω : FiniteRootBranchingStepField m ℝ |
          branchingStepPresentAlong (ω i) v (j :: p)} =
          {ω : FiniteRootBranchingStepField m ℝ |
            branchingStepPresent (ω i v) j} ∩
            {ω : FiniteRootBranchingStepField m ℝ |
              branchingStepPresentAlong (ω i) (v ++ [j]) p} := by
        ext ω
        simp [branchingStepPresentAlong]
      rw [hset]
      refine MeasurableSet.inter ?_ ?_
      · exact (multiRootStep_measurable (X := ℝ) i v (by omega))
          (branchingStepPresent_measurableSet (X := ℝ) j)
      · exact ih (v := v ++ [j]) (by omega)

theorem rootIndexedRealizedNode_measurableSet
    {m : ℕ} (i : Fin m) (u : 𝕍) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) u.length]
      {ω : FiniteRootBranchingStepField m ℝ | rootIndexedRealizedNode ω i u} := by
  change MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) u.length]
    {ω : FiniteRootBranchingStepField m ℝ |
      branchingStepPresentAlong (ω i) [] u}
  exact rootIndexedStepPresentAlong_measurableSet i [] u u.length (by simp)

/-- The accumulated mark of one root is observable at the generation reached
by its address. -/
theorem rootIndexedBranchingStepAccumulatedMark_real_measurable
    {m : ℕ} (i : Fin m) (v p : 𝕍) (n : ℕ) (hn : v.length + p.length ≤ n) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
      (fun ω : FiniteRootBranchingStepField m ℝ =>
        branchingStepAccumulatedMarkFrom (ω i) v p) := by
  induction p generalizing v with
  | nil => exact measurable_const
  | cons j p ih =>
      have hlen : (v ++ [j]).length = v.length + 1 := by simp
      have hlen' : (j :: p).length = p.length + 1 := by simp
      have hstep : Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
          (fun ω : FiniteRootBranchingStepField m ℝ =>
            branchingStepIncrement (ω i v) j) :=
        (branchingStepIncrement_measurable (X := ℝ) j).comp
          (multiRootStep_measurable (X := ℝ) i v (by omega))
      have hrec : Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
          (fun ω : FiniteRootBranchingStepField m ℝ =>
            branchingStepAccumulatedMarkFrom (ω i) (v ++ [j]) p) :=
        ih (v := v ++ [j]) (by omega)
      change Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
        ((fun ω : FiniteRootBranchingStepField m ℝ =>
            branchingStepIncrement (ω i v) j) +
          fun ω => branchingStepAccumulatedMarkFrom (ω i) (v ++ [j]) p)
      exact hstep.add hrec

theorem rootIndexedBranchingStepPosition_real_measurable
    {m : ℕ} (initial : Fin m → ℝ) (i : Fin m) (u : 𝕍) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) u.length]
      (fun ω : FiniteRootBranchingStepField m ℝ =>
        rootIndexedBranchingStepPosition initial ω i u) := by
  change Measurable[multiRootStepFiltration (m := m) (X := ℝ) u.length]
    ((fun _ : FiniteRootBranchingStepField m ℝ => initial i) +
      fun ω => branchingStepAccumulatedMarkFrom (ω i) [] u)
  exact (measurable_const : Measurable[
      multiRootStepFiltration (m := m) (X := ℝ) u.length]
      (fun _ : FiniteRootBranchingStepField m ℝ => initial i)).add
    (rootIndexedBranchingStepAccumulatedMark_real_measurable i [] u u.length (by simp))

def multiRootPositionAtGeneration
    {m : ℕ} (initial : Fin m → ℝ) (n : ℕ)
    (i : Fin m) (u : 𝕍) (ω : FiniteRootBranchingStepField m ℝ) : ℝ :=
  if u.length = n then rootIndexedBranchingStepPosition initial ω i u else 0

theorem multiRootPositionAtGeneration_measurable
    {m : ℕ} (initial : Fin m → ℝ) (n : ℕ)
    (i : Fin m) (u : 𝕍) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
      (multiRootPositionAtGeneration initial n i u) := by
  change Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
    (fun ω => if u.length = n then
      rootIndexedBranchingStepPosition initial ω i u else 0)
  by_cases hu : u.length = n
  · subst n
    simpa using rootIndexedBranchingStepPosition_real_measurable initial i u
  · simp only [hu, ite_false]
    exact measurable_const

set_option linter.style.haveILetI false in
theorem selectedMultiRootAbsolutePosition_real_measurable
    {m : ℕ} (initial : Fin m → ℝ) (n : ℕ) (i : Fin m)
    (chosen : FiniteRootBranchingStepField m ℝ → 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := ℝ) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
      (fun ω => rootIndexedBranchingStepPosition initial ω i (chosen ω)) := by
  letI : MeasurableSpace (FiniteRootBranchingStepField m ℝ) :=
    multiRootStepFiltration (m := m) (X := ℝ) n
  have hjoint : Measurable
      (fun p : 𝕍 × FiniteRootBranchingStepField m ℝ =>
        multiRootPositionAtGeneration initial n i p.1 p.2) :=
    measurable_from_prod_countable_right
      (multiRootPositionAtGeneration_measurable initial n i)
  have h := hjoint.comp (hchosen.prodMk measurable_id)
  convert h using 1
  funext ω
  simp [multiRootPositionAtGeneration, hdepth ω]

theorem selectedMultiRootRealizedNode_measurableSet
    {m : ℕ} (n : ℕ) (i : Fin m)
    (chosen : FiniteRootBranchingStepField m ℝ → 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := ℝ) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length = n) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
      {ω | rootIndexedRealizedNode ω i (chosen ω)} := by
  have hset : {ω : FiniteRootBranchingStepField m ℝ |
      rootIndexedRealizedNode ω i (chosen ω)} =
      ⋃ u : 𝕍,
        {ω : FiniteRootBranchingStepField m ℝ | chosen ω = u} ∩
          {ω | rootIndexedRealizedNode ω i u} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hreal⟩
      simpa [hu] using hreal
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length = n
  · subst n
    exact (hchosen (measurableSet_singleton u)).inter
      (rootIndexedRealizedNode_measurableSet i u)
  · have hempty :
        {ω : FiniteRootBranchingStepField m ℝ | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

end ThesisSpeed
