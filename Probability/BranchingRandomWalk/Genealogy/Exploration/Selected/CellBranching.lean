import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.Descendants

/-!
# Branching on a cell of the selected population

A finite labelled population admits a duplicate-free vector enumeration, and
the event that the selected population equals that listing is observable at
the selected generation. On that cell the descendants of the listed particles
have the product marked-tree law, with the initial offsets shifted by the root
positions.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-- Every finite labelled population admits a duplicate-free vector
enumeration.  This uses mathlib's finite-type equivalence with `Fin`. -/
theorem finiteRootAddress_enumeration {m : ℕ}
    (s : Finset (RootAddress m)) :
    ∃ roots : Fin s.card → RootAddress m,
      s = Finset.univ.image roots ∧ Function.Injective roots := by
  classical
  let e : {p : RootAddress m // p ∈ s} ≃ Fin s.card :=
    Fintype.equivFinOfCardEq (by simp)
  let roots : Fin s.card → RootAddress m := fun j => (e.symm j).1
  refine ⟨roots, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      apply Finset.mem_image.mpr
      refine ⟨e ⟨p, hp⟩, Finset.mem_univ _, ?_⟩
      simp [roots]
    · intro hp
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
      exact (e.symm j).2
  · intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij

/-- Current positions of a fixed vector of generation-`n` particles are
observable before their descendant marks are exposed. -/
theorem multiRootPositionVector_measurable {m k n : ℕ}
    (x : Fin m → ℝ) (roots : Fin k → RootAddress m)
    (hlen : ∀ j, (roots j).2.length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) n]
      (fun ω : FiniteRootStepField m ℝ =>
        fun j : Fin k => rootIndexedStepPosition x ω (roots j).1 (roots j).2) := by
  apply (@measurable_pi_iff (FiniteRootStepField m ℝ) (Fin k)
    (fun _ => ℝ) (multiRootStepFiltration (m := m) (X := ℝ) n)
    (fun _ => inferInstance) _).2
  intro j
  have hj := rootIndexedStepPosition_measurable x (roots j).1 (roots j).2
  rw [hlen j] at hj
  exact hj

/-- The event that the actual selected population is a prescribed labelled
set belongs to the generation domain sigma algebra. -/
theorem selectedPopulation_cell_measurable {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (A : Set (FiniteRootStepField m ℝ))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
    (s : Finset (RootAddress m)) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
      (A ∩ {ω | selectedPopulation N x n ω = s}) :=
  hA.inter ((selectedPopulation_adapted N x n)
    (measurableSet_singleton s))

/-- Joint branching for the actual selected population, conditional on a
specified finite population cell.  `roots` is merely an enumeration of the
prescribed set; the spatial selection already took place in `A` and the
cell event. -/
theorem selectedPopulation_cell_factorization
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m k : ℕ} (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (A : Set (FiniteRootStepField m ℝ))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
    (s : Finset (RootAddress m))
    (roots : Fin k → RootAddress m)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (B : Set (Fin k → (𝕍 → Step ℕ ℝ)))
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
      ((A ∩ {ω | selectedPopulation N x n ω = s}) ∩
        multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootStepFieldLaw μ m
        (A ∩ {ω | selectedPopulation N x n ω = s}) *
        (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
  by_cases hcell : ∃ ω, ω ∈ A ∧ selectedPopulation N x n ω = s
  · obtain ⟨ω, _, hω⟩ := hcell
    have hlen : ∀ j, (roots j).2.length = n := by
      intro j
      apply selectedPopulation_depth N x n ω
      rw [hω, hcover]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    exact fixed_multiRootSubtreeStepFieldVector_event_factorization μ roots hlen
      hinj _ B (selectedPopulation_cell_measurable N x n A hA s) hB
  · have hempty : A ∩ {ω | selectedPopulation N x n ω = s} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => hcell ⟨ω, h.1, h.2⟩
    simp [hempty]

/-- The actual selected population has a product descendant law on **each**
of its (possibly different-cardinality) generation-`n` cells.  The finite
index type is chosen separately for each cell. -/
theorem selectedPopulation_each_cell_branches
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (s : Finset (RootAddress m)) :
    ∃ roots : Fin s.card → RootAddress m,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootStepField m ℝ))
        (_ : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
        (B : Set (Fin s.card → (𝕍 → Step ℕ ℝ)))
        (_ : MeasurableSet B),
        finiteRootStepFieldLaw μ m
          ((A ∩ {ω | selectedPopulation N x n ω = s}) ∩
            multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootStepFieldLaw μ m
            (A ∩ {ω | selectedPopulation N x n ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => stepFieldLaw μ)) B := by
  obtain ⟨roots, hcover, hinj⟩ := finiteRootAddress_enumeration s
  exact ⟨roots, hcover, fun A hA B hB =>
    selectedPopulation_cell_factorization μ N x n A hA s roots hcover hinj B hB⟩

/-- The cellwise branching formula still holds after testing the current
spatial configuration.  This is the measurable input for later spatially
translated descendant processes. -/
theorem selectedPopulation_cell_position_factorization
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m k : ℕ} (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (A : Set (FiniteRootStepField m ℝ))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
    (s : Finset (RootAddress m))
    (roots : Fin k → RootAddress m)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (D : Set (Fin k → ℝ)) (hD : MeasurableSet D)
    (B : Set (Fin k → (𝕍 → Step ℕ ℝ)))
    (hB : MeasurableSet B) :
    let positions := fun ω : FiniteRootStepField m ℝ =>
      fun j : Fin k => rootIndexedStepPosition x ω (roots j).1 (roots j).2
    finiteRootStepFieldLaw μ m
      (((A ∩ positions ⁻¹' D) ∩
          {ω | selectedPopulation N x n ω = s}) ∩
        multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootStepFieldLaw μ m
        ((A ∩ positions ⁻¹' D) ∩
          {ω | selectedPopulation N x n ω = s}) *
        (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
  dsimp
  by_cases hcell : ∃ ω, ω ∈ A ∧ selectedPopulation N x n ω = s
  · obtain ⟨ω, _, hω⟩ := hcell
    have hlen : ∀ j, (roots j).2.length = n := by
      intro j
      apply selectedPopulation_depth N x n ω
      rw [hω, hcover]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    apply selectedPopulation_cell_factorization μ N x n
      (A ∩ (fun ω : FiniteRootStepField m ℝ =>
        fun j : Fin k => rootIndexedStepPosition x ω (roots j).1 (roots j).2) ⁻¹' D)
      (hA.inter ((multiRootPositionVector_measurable x roots hlen) hD))
      s roots hcover hinj B hB
  · have hempty : A ∩ {ω | selectedPopulation N x n ω = s} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => hcell ⟨ω, h.1, h.2⟩
    have hempty' :
        (A ∩ (fun ω : FiniteRootStepField m ℝ =>
          fun j : Fin k => rootIndexedStepPosition x ω (roots j).1 (roots j).2) ⁻¹' D) ∩
          {ω | selectedPopulation N x n ω = s} = ∅ := by
      ext ω
      constructor
      · intro h
        have h' : ω ∈ A ∩ {ω | selectedPopulation N x n ω = s} :=
          ⟨h.1.1, h.2⟩
        rw [hempty] at h'
        exact h'
      · intro h
        exact h.elim
    simp [hempty']

theorem selectedPopulation_cell_descendant_law
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {m k : ℕ} (N : ℕ) (x : Fin m → ℝ) (n : ℕ)
    (A : Set (FiniteRootStepField m ℝ))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] A)
    (s : Finset (RootAddress m))
    (roots : Fin k → RootAddress m)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots) :
    ∀ B : Set (Fin k → 𝕍 → Step ℕ ℝ), MeasurableSet B →
      finiteRootStepFieldLaw μ m
        ((A ∩ {ω | selectedPopulation N x n ω = s}) ∩
          (fun ω => (FiniteDescendantPopulation.fromRoots roots hinj ω).field) ⁻¹' B) =
      finiteRootStepFieldLaw μ m
        (A ∩ {ω | selectedPopulation N x n ω = s}) *
        Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ) B := by
  intro B hB
  exact selectedPopulation_cell_factorization μ N x n A hA s roots hcover hinj B hB

end ProbabilityTheory.BranchingRandomWalk
