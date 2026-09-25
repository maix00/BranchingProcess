import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppedPopulation.Cells

/-!
# Branching on each population cell

On a cell of constant population and stopping generation, the descendant step
fields of the population are independent of the stopped past with the finite
product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingStep MeasureTheory


theorem abstractStoppedPopulation_cell_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : FiniteRootStepField m X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤)
    (population : FiniteRootStepField m X → Finset (Fin m × 𝕍))
    (hpopulation : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet[hτ.measurableSpace] {step | population step = s})
    (hdepth : ∀ step (u : Fin m × 𝕍), u ∈ population step →
      ∀ n : ℕ, τ step = (n : WithTop ℕ) → u.2.length = n)
    (A : Set (FiniteRootStepField m X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (s : Finset (Fin m × 𝕍))
    (roots : Fin k → Fin m × 𝕍)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (B : Set (Fin k → 𝕍 → Step ℕ X))
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
        ((A ∩ {step | population step = s}) ∩
          multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootStepFieldLaw μ m (A ∩ {step | population step = s}) *
        (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
  let P := finiteRootStepFieldLaw μ m
  let Q := Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)
  let E : Set (FiniteRootStepField m X) :=
    A ∩ {step | population step = s}
  let C : ℕ → Set (FiniteRootStepField m X) :=
    fun n => E ∩ {step | τ step = (n : WithTop ℕ)}
  let D : ℕ → Set (FiniteRootStepField m X) :=
    fun n => C n ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B
  have hE : MeasurableSet[hτ.measurableSpace] E :=
    hA.inter (hpopulation s)
  have hCgen n : MeasurableSet[
      multiRootStepFiltration (m := m) (X := X) n] (C n) :=
    abstractMultiRootStoppedCell_measurable τ hτ E hE n
  have hCmeas n : MeasurableSet (C n) :=
    (multiRootStepFiltration (m := m) (X := X) |>.le n) _ (hCgen n)
  have hDmeas n : MeasurableSet (D n) :=
    (hCmeas n).inter ((multiRootSubtreeStepFieldVector_measurable roots) hB)
  have hcell n : P (D n) = P (C n) * Q B := by
    by_cases hlen : ∀ j, (roots j).2.length = n
    · exact fixed_multiRootSubtreeStepFieldVector_event_factorization μ roots
        hlen hinj (C n) B (hCgen n) hB
    · have hempty : C n = ∅ := by
        ext step
        simp only [C, E, Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hpop⟩, htime⟩
        apply hlen
        intro j
        apply hdepth step (roots j)
        · rw [hpop, hcover]
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · exact htime
      simp [D, hempty]
  have hCpair : Pairwise (fun n l => Disjoint (C n) (C l)) := by
    intro n l hne
    apply Set.disjoint_left.mpr
    intro step hn hl
    apply hne
    exact WithTop.coe_injective (hn.2.symm.trans hl.2)
  have hDpair : Pairwise (fun n l => Disjoint (D n) (D l)) := by
    intro n l hne
    exact (hCpair hne).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ n, C n) = E := by
    ext step
    constructor
    · simp only [Set.mem_iUnion, C, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨n, hEstep, _⟩
      exact hEstep
    · intro hEstep
      cases htime : τ step with
      | top => exact False.elim (hfinite step htime)
      | coe n => exact Set.mem_iUnion.mpr ⟨n, hEstep, htime⟩
  have hDunion : (⋃ n, D n) =
      E ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B := by
    ext step
    constructor
    · simp only [Set.mem_iUnion, D, C, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_preimage]
      rintro ⟨n, ⟨⟨hEstep, _⟩, hBstep⟩⟩
      exact ⟨hEstep, hBstep⟩
    · rintro ⟨hEstep, hBstep⟩
      cases htime : τ step with
      | top => exact False.elim (hfinite step htime)
      | coe n => exact Set.mem_iUnion.mpr ⟨n, ⟨⟨hEstep, htime⟩, hBstep⟩⟩
  have hCsum : (∑' n, P (C n)) = P E := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (E ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B) =
        P (⋃ n, D n) := by rw [hDunion]
    _ = ∑' n, P (D n) := measure_iUnion hDpair hDmeas
    _ = ∑' n, P (C n) * Q B := tsum_congr hcell
    _ = (∑' n, P (C n)) * Q B := ENNReal.tsum_mul_right
    _ = P E * Q B := by rw [hCsum]

theorem abstractStoppedPopulation_each_cell_branches
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (τ : FiniteRootStepField m X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤)
    (population : FiniteRootStepField m X → Finset (Fin m × 𝕍))
    (hpopulation : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet[hτ.measurableSpace] {step | population step = s})
    (hdepth : ∀ step (u : Fin m × 𝕍), u ∈ population step →
      ∀ n : ℕ, τ step = (n : WithTop ℕ) → u.2.length = n)
    (s : Finset (Fin m × 𝕍)) :
    ∃ roots : Fin s.card → Fin m × 𝕍,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootStepField m X))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → 𝕍 → Step ℕ X))
        (_ : MeasurableSet B),
        finiteRootStepFieldLaw μ m
            ((A ∩ {step | population step = s}) ∩
              multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootStepFieldLaw μ m
              (A ∩ {step | population step = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => stepFieldLaw μ)) B := by
  obtain ⟨roots, hcover, hinj⟩ := finiteMultiRootAddress_enumeration s
  exact ⟨roots, hcover, fun A hA B hB =>
    abstractStoppedPopulation_cell_factorization μ τ hτ hfinite population
      hpopulation hdepth A hA s roots hcover hinj B hB⟩

end ProbabilityTheory.BranchingRandomWalk
