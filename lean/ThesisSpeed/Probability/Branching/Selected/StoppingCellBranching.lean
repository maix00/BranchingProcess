import ThesisSpeed.Probability.Branching.Selected.StoppingPopulation

/-!
# Branching on a stopped cell

On a prescribed value `s` of a finite population selected at a finite
stopping time, the descendant trees of all particles in `s` have the
independent product law, measurability being required only for the population
as a map out of the stopped domain σ-algebra. The last theorem removes the
fixed-cardinality restriction from the branching statement.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-- On a prescribed value `s` of a finite population selected at a finite
stopping time, the descendant trees of all particles in `s` have the
independent product law.  Measurability is required only for the population
as a map out of the stopped domain sigma algebra. -/
theorem multiRoot_stoppedPopulation_cell_factorization
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    {m k : ℕ}
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (population : FiniteRootBranchingStepField m ℝ → Finset (RootAddress m))
    (hpopulation : ∀ s : Finset (RootAddress m),
      MeasurableSet[hτ.measurableSpace] {ω | population ω = s})
    (hdepth : ∀ ω (u : RootAddress m), u ∈ population ω →
      ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n)
    (A : Set (FiniteRootBranchingStepField m ℝ))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (s : Finset (RootAddress m))
    (roots : Fin k → RootAddress m)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (B : Set (Fin k → (𝕍 → BranchingStep ℕ ℝ)))
    (hB : MeasurableSet B) :
    finiteRootBranchingStepFieldLaw μ m
        ((A ∩ {ω | population ω = s}) ∩
          multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootBranchingStepFieldLaw μ m (A ∩ {ω | population ω = s}) *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  let P := finiteRootBranchingStepFieldLaw μ m
  let Q := Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)
  let E : Set (FiniteRootBranchingStepField m ℝ) := A ∩ {ω | population ω = s}
  let C : ℕ → Set (FiniteRootBranchingStepField m ℝ) :=
    fun n => E ∩ {ω | τ ω = (n : WithTop ℕ)}
  let D : ℕ → Set (FiniteRootBranchingStepField m ℝ) :=
    fun n => C n ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B
  have hE : MeasurableSet[hτ.measurableSpace] E :=
    hA.inter (hpopulation s)
  have hCgen n : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n] (C n) :=
    multiRoot_stoppedCell_measurable τ hτ E hE n
  have hCmeas n : MeasurableSet (C n) :=
    (multiRootStepFiltration (m := m) (X := ℝ) |>.le n) _ (hCgen n)
  have hDmeas n : MeasurableSet (D n) :=
    (hCmeas n).inter ((multiRootSubtreeStepFieldVector_measurable roots) hB)
  have hcell n : P (D n) = P (C n) * Q B := by
    by_cases hlen : ∀ j, (roots j).2.length = n
    · exact fixed_multiRootSubtreeStepFieldVector_event_factorization μ roots hlen hinj
        (C n) B (hCgen n) hB
    · have hempty : C n = ∅ := by
        ext ω
        simp only [C, E, Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hpop⟩, htime⟩
        apply hlen
        intro j
        apply hdepth ω (roots j)
        · rw [hpop, hcover]
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · exact htime
      simp [D, hempty]
  have hCpair : Pairwise (fun n l => Disjoint (C n) (C l)) := by
    intro n l hne
    apply Set.disjoint_left.mpr
    intro ω hn hl
    apply hne
    exact WithTop.coe_injective (hn.2.symm.trans hl.2)
  have hDpair : Pairwise (fun n l => Disjoint (D n) (D l)) := by
    intro n l hne
    exact (hCpair hne).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ n, C n) = E := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, C, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨n, hEω, _⟩
      exact hEω
    · intro hEω
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n => exact Set.mem_iUnion.mpr ⟨n, hEω, htime⟩
  have hDunion : (⋃ n, D n) =
      E ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, D, C, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_preimage]
      rintro ⟨n, ⟨⟨hEω, _⟩, hBω⟩⟩
      exact ⟨hEω, hBω⟩
    · rintro ⟨hEω, hBω⟩
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n => exact Set.mem_iUnion.mpr ⟨n, ⟨⟨hEω, htime⟩, hBω⟩⟩
  have hCsum : (∑' n, P (C n)) = P E := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (E ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B) = P (⋃ n, D n) := by
      rw [hDunion]
    _ = ∑' n, P (D n) := measure_iUnion hDpair hDmeas
    _ = ∑' n, P (C n) * Q B := tsum_congr hcell
    _ = (∑' n, P (C n)) * Q B := ENNReal.tsum_mul_right
    _ = P E * Q B := by rw [hCsum]

/-- Every cell of a stopped finite population admits an enumeration whose
descendant vector branches with the appropriate (cell-dependent) finite
product law. -/
theorem multiRoot_stoppedPopulation_each_cell_branches
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ}
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (population : FiniteRootBranchingStepField m ℝ → Finset (RootAddress m))
    (hpopulation : ∀ s : Finset (RootAddress m),
      MeasurableSet[hτ.measurableSpace] {ω | population ω = s})
    (hdepth : ∀ ω (u : RootAddress m), u ∈ population ω →
      ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n)
    (s : Finset (RootAddress m)) :
    ∃ roots : Fin s.card → RootAddress m,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootBranchingStepField m ℝ))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → (𝕍 → BranchingStep ℕ ℝ)))
        (_ : MeasurableSet B),
        finiteRootBranchingStepFieldLaw μ m
            ((A ∩ {ω | population ω = s}) ∩
              multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootBranchingStepFieldLaw μ m (A ∩ {ω | population ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => branchingStepFieldLaw μ)) B := by
  obtain ⟨roots, hcover, hinj⟩ := finiteRootAddress_enumeration s
  exact ⟨roots, hcover, fun A hA B hB =>
    multiRoot_stoppedPopulation_cell_factorization μ τ hτ hfinite
      population hpopulation hdepth A hA s roots hcover hinj B hB⟩

/-- The stopped selected population of the thesis satisfies the abstract
cellwise branching theorem.  This is the concrete interface used by later
coupling arguments. -/
theorem selectedPopulation_stopped_cell_branches
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (s : Finset (RootAddress m)) :
    ∃ roots : Fin s.card → RootAddress m,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootBranchingStepField m ℝ))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → (𝕍 → BranchingStep ℕ ℝ)))
        (_ : MeasurableSet B),
        finiteRootBranchingStepFieldLaw μ m
            ((A ∩ {ω | selectedPopulationAt N x τ ω = s}) ∩
              multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootBranchingStepFieldLaw μ m
            (A ∩ {ω | selectedPopulationAt N x τ ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => branchingStepFieldLaw μ)) B := by
  apply multiRoot_stoppedPopulation_each_cell_branches μ τ hτ hfinite
    (selectedPopulationAt N x τ)
    (fun t => selectedPopulationAt_cell_measurable N x τ hτ hfinite t)
    (selectedPopulationAt_depth N x τ)

/-- Unified random-cardinality interface for the selected population: every
finite cell has a duplicate-free multi-root enumeration with the product
descendant law, and all cells form the countable probability partition. -/
theorem selectedPopulation_random_size_branching
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤) :
    (∀ s : Finset (RootAddress m),
      ∃ roots : Fin s.card → RootAddress m,
        s = Finset.univ.image roots ∧
        ∀ (A : Set (FiniteRootBranchingStepField m ℝ))
          (_ : MeasurableSet[hτ.measurableSpace] A)
          (B : Set (Fin s.card → (𝕍 → BranchingStep ℕ ℝ)))
          (_ : MeasurableSet B),
          finiteRootBranchingStepFieldLaw μ m
              ((A ∩ {ω | selectedPopulationAt N x τ ω = s}) ∩
                multiRootSubtreeStepFieldVector roots ⁻¹' B) =
            finiteRootBranchingStepFieldLaw μ m
              (A ∩ {ω | selectedPopulationAt N x τ ω = s}) *
              (Measure.infinitePi
                (fun _ : Fin s.card => branchingStepFieldLaw μ)) B) ∧
    (∀ A : Set (FiniteRootBranchingStepField m ℝ),
      MeasurableSet[hτ.measurableSpace] A →
      (∑' s : Finset (RootAddress m),
        finiteRootBranchingStepFieldLaw μ m
          (A ∩ {ω | selectedPopulationAt N x τ ω = s})) =
        finiteRootBranchingStepFieldLaw μ m A) := by
  constructor
  · intro s
    exact selectedPopulation_stopped_cell_branches μ N x τ hτ hfinite s
  · intro A hA
    exact multiRoot_stoppedPopulation_cells_measure_sum μ τ hτ
      (selectedPopulationAt N x τ)
      (fun s => selectedPopulationAt_cell_measurable N x τ hτ hfinite s)
      A hA

end ThesisSpeed
