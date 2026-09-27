import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field
import Probability.BranchingRandomWalk.Tree.Filtration

/-!
# Generation filtrations on root-indexed step fields

The primary definitions allow arbitrary root and child-slot types.  The
finite-root names are specializations retained for finite-population results.
No finiteness or countability assumption is needed to generate the domain
flow or to observe a fixed coordinate.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



@[instance_reducible] def RootIndexed.stepGenerationSpace
    {Root α X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (RootIndexed.StepField Root α X) :=
  MeasurableSpace.generateFrom
    {s | ∃ r : Root, ∃ u : TreeNode α, u.length < n ∧
      ∃ t : Set (Step α X), MeasurableSet t ∧
        s = {ω : RootIndexed.StepField Root α X | ω r u ∈ t}}

def RootIndexed.stepFiltration
    {Root α X : Type*} [MeasurableSpace X] :
    Filtration ℕ
      (inferInstance : MeasurableSpace (RootIndexed.StepField Root α X)) where
  seq := RootIndexed.stepGenerationSpace
  mono' := by
    intro n k hnk
    apply MeasurableSpace.generateFrom_mono
    rintro s ⟨r, u, hu, t, ht, rfl⟩
    exact ⟨r, u, lt_of_lt_of_le hu hnk, t, ht, rfl⟩
  le' := by
    intro n
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨r, u, hu, t, ht, rfl⟩
    exact ((measurable_pi_apply u).comp (measurable_pi_apply r)) ht

theorem RootIndexed.stepGenerationSpace_zero
    {Root α X : Type*} [MeasurableSpace X] :
    RootIndexed.stepGenerationSpace (Root := Root) (α := α) (X := X) 0 = ⊥ := by
  unfold RootIndexed.stepGenerationSpace
  have hgen :
      {s : Set (RootIndexed.StepField Root α X) |
        ∃ r : Root, ∃ u : TreeNode α, u.length < 0 ∧
          ∃ t : Set (Step α X), MeasurableSet t ∧
            s = {ω : RootIndexed.StepField Root α X | ω r u ∈ t}} = ∅ := by
    ext s
    simp
  rw [hgen, MeasurableSpace.generateFrom_empty]

theorem RootIndexed.step_measurable
    {Root α X : Type*} {n : ℕ} [MeasurableSpace X]
    (r : Root) (u : TreeNode α) (hu : u.length < n) :
    Measurable[RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
      (fun ω : RootIndexed.StepField Root α X => ω r u) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨r, u, hu, t, ht, rfl⟩

/-- Restricting a root-indexed field to one fixed root preserves the
generation domain flow.  This needs no countability assumption on either the
root labels or the child slots: every generator in the target observes one
fixed coordinate. -/
theorem RootIndexed.field_measurable
    {Root α X : Type*} [MeasurableSpace X] (r : Root) (n : ℕ) :
    @Measurable
      (RootIndexed.StepField Root α X) (Mark α (Step α X))
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n)
      (generationFiltration (α := α) (M := Step α X) n)
      (fun ω => ω r) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n
  apply measurable_generateFrom
  intro s hs
  obtain ⟨u, hu, t, ht, rfl⟩ := hs
  exact (RootIndexed.step_measurable (X := X) r u hu) ht

/-- Reindexing roots is measurable between generation domains.  No
injectivity, finiteness, or countability assumption on either root type is
needed. -/
theorem RootIndexed.StepField.reindex_filtration_measurable
    {Root NewRoot α X : Type*} [MeasurableSpace X]
    (f : NewRoot → Root) (n : ℕ) :
    @Measurable
      (RootIndexed.StepField Root α X)
      (RootIndexed.StepField NewRoot α X)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n)
      (RootIndexed.stepFiltration
        (Root := NewRoot) (α := α) (X := X) n)
      (RootIndexed.StepField.reindex f) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
    RootIndexed.stepFiltration n
  let _ : MeasurableSpace (RootIndexed.StepField NewRoot α X) :=
    RootIndexed.stepFiltration n
  change Measurable (RootIndexed.StepField.reindex f)
  apply measurable_generateFrom
  intro s hs
  obtain ⟨r, u, hu, t, ht, rfl⟩ := hs
  exact (RootIndexed.step_measurable (X := X) (f r) u hu) ht

/-- A random root/address coordinate can be read from the generation domain
flow when its choice is domain-measurable, lies below the generation, and has
countable range.  The field, root type, and offspring-slot type themselves may
all be uncountable; countability is localized to the actually selected labels
needed for the measurable union. -/
theorem RootIndexed.selectedStep_measurable
    {Root α X : Type*} {n : ℕ} [MeasurableSpace X]
    (chosen : RootIndexed.StepField Root α X → Root × TreeNode α)
    (hfiber : ∀ p, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n]
        {ω | chosen ω = p})
    (hdepth : ∀ ω, (chosen ω).2.length < n)
    (hcount : (Set.range chosen).Countable) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω : RootIndexed.StepField Root α X =>
        ω (chosen ω).1 (chosen ω).2) := by
  let S : Set (Root × TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  intro t ht
  have hset :
      {ω : RootIndexed.StepField Root α X |
        ω (chosen ω).1 (chosen ω).2 ∈ t} =
        ⋃ p : S,
          {ω | chosen ω = p.1} ∩ {ω | ω p.1.1 p.1.2 ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨p, hp, hmark⟩
      simpa [hp] using hmark
  change MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
    {ω : RootIndexed.StepField Root α X |
      ω (chosen ω).1 (chosen ω).2 ∈ t}
  rw [hset]
  apply MeasurableSet.iUnion
  intro p
  have hpdepth : p.1.2.length < n := by
    obtain ⟨ω, hω⟩ := p.2
    simpa [← hω] using hdepth ω
  exact (hfiber p.1).inter
    ((RootIndexed.step_measurable (X := X) p.1.1 p.1.2 hpdepth) ht)


@[instance_reducible] def multiRootStepGenerationSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (FiniteRootStepField m ℕ X) :=
  MeasurableSpace.generateFrom
    {s | ∃ i : Fin m, ∃ u : 𝕍, u.length < n ∧
      ∃ t : Set (Step ℕ X), MeasurableSet t ∧
        s = {ω : FiniteRootStepField m ℕ X | ω i u ∈ t}}

def multiRootStepFiltration
    {m : ℕ} {X : Type*} [MeasurableSpace X] :
    Filtration ℕ (inferInstance : MeasurableSpace (FiniteRootStepField m ℕ X)) where
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
      {s : Set (FiniteRootStepField m ℕ X) |
        ∃ i : Fin m, ∃ u : 𝕍, u.length < 0 ∧
          ∃ t : Set (Step ℕ X), MeasurableSet t ∧
            s = {ω : FiniteRootStepField m ℕ X | ω i u ∈ t}} = ∅ := by
    ext s
    simp
  rw [hgen, MeasurableSpace.generateFrom_empty]

theorem multiRootStep_measurable
    {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m) (u : 𝕍) (hu : u.length < n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m ℕ X => ω i u) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, u, hu, t, ht, rfl⟩

theorem multiRootSelectedStep_measurable
    {m n : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m)
    (chosen : FiniteRootStepField m ℕ X → 𝕍)
    (hchosen : Measurable[
      multiRootStepFiltration (m := m) (X := X) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length < n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m ℕ X => ω i (chosen ω)) := by
  intro t ht
  have hset :
      {ω : FiniteRootStepField m ℕ X | ω i (chosen ω) ∈ t} =
        ⋃ u : 𝕍,
          {ω : FiniteRootStepField m ℕ X | chosen ω = u} ∩
            {ω : FiniteRootStepField m ℕ X | ω i u ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hmark⟩
      simpa [hu] using hmark
  change MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
    {ω : FiniteRootStepField m ℕ X | ω i (chosen ω) ∈ t}
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length < n
  · exact (hchosen (measurableSet_singleton u)).inter
      ((multiRootStep_measurable (X := X) i u hu) ht)
  · have hempty :
        {ω : FiniteRootStepField m ℕ X | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

end ProbabilityTheory.BranchingRandomWalk
