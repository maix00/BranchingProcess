import ThesisSpeed.Probability.Branching.RootIndexed.DomainFlow
import ThesisSpeed.Probability.Timing.Stopping

/-!
# Random finite populations at a stopping generation

This file separates the random-cardinality measure argument from any concrete
particle-selection algorithm.  A finite population is a finset of labelled
multi-root addresses.  On every population cell, its descendant fields have
the corresponding finite product law.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

theorem finiteMultiRootAddress_enumeration {m : ℕ}
    (s : Finset (Fin m × TreeNode)) :
    ∃ roots : Fin s.card → Fin m × TreeNode,
      s = Finset.univ.image roots ∧ Function.Injective roots := by
  classical
  let e : {p : Fin m × TreeNode // p ∈ s} ≃ Fin s.card :=
    Fintype.equivFinOfCardEq (by simp)
  let roots : Fin s.card → Fin m × TreeNode := fun j => (e.symm j).1
  refine ⟨roots, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      exact Finset.mem_image.mpr
        ⟨e ⟨p, hp⟩, Finset.mem_univ _, by simp [roots]⟩
    · intro hp
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
      exact (e.symm j).2
  · intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij

theorem abstractMultiRootStoppedCell_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (τ : FiniteRootBranchingStepField m X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (E : Set (FiniteRootBranchingStepField m X))
    (hE : MeasurableSet[hτ.measurableSpace] E) (n : ℕ) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      (E ∩ {step | τ step = (n : WithTop ℕ)}) :=
  (hτ.measurableSet_inter_eq_iff E n).1
    (hE.inter (hτ.measurable
      (measurableSet_singleton (n : WithTop ℕ))))

theorem abstractStoppedPopulation_cells_partition
    {m : ℕ} {X : Type*}
    (population : FiniteRootBranchingStepField m X → Finset (Fin m × TreeNode))
    (A : Set (FiniteRootBranchingStepField m X)) :
    Pairwise (fun s t =>
      Disjoint (A ∩ {step | population step = s})
        (A ∩ {step | population step = t})) ∧
      (⋃ s : Finset (Fin m × TreeNode),
        A ∩ {step | population step = s}) = A := by
  constructor
  · intro s t hst
    apply Set.disjoint_left.mpr
    intro step hs ht
    exact hst (hs.2.symm.trans ht.2)
  · ext step
    constructor
    · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨s, hAstep, _⟩
      exact hAstep
    · intro hstep
      exact Set.mem_iUnion.mpr ⟨population step, hstep, rfl⟩

theorem abstractStoppedPopulation_cells_measure_sum
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (τ : FiniteRootBranchingStepField m X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (population : FiniteRootBranchingStepField m X → Finset (Fin m × TreeNode))
    (hpopulation : ∀ s : Finset (Fin m × TreeNode),
      MeasurableSet[hτ.measurableSpace] {step | population step = s})
    (A : Set (FiniteRootBranchingStepField m X))
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∑' s : Finset (Fin m × TreeNode),
      finiteRootBranchingStepFieldLaw μ m (A ∩ {step | population step = s})) =
      finiteRootBranchingStepFieldLaw μ m A := by
  obtain ⟨hpair, hunion⟩ :=
    abstractStoppedPopulation_cells_partition population A
  have hmeas : ∀ s : Finset (Fin m × TreeNode),
      MeasurableSet (A ∩ {step | population step = s}) := by
    intro s
    exact (hτ.measurableSpace_le _ hA).inter
      (hτ.measurableSpace_le _ (hpopulation s))
  calc
    (∑' s : Finset (Fin m × TreeNode),
        finiteRootBranchingStepFieldLaw μ m (A ∩ {step | population step = s})) =
      finiteRootBranchingStepFieldLaw μ m (⋃ s : Finset (Fin m × TreeNode),
        A ∩ {step | population step = s}) :=
      (measure_iUnion hpair hmeas).symm
    _ = finiteRootBranchingStepFieldLaw μ m A := by rw [hunion]

theorem abstractStoppedPopulation_cell_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k : ℕ}
    (τ : FiniteRootBranchingStepField m X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤)
    (population : FiniteRootBranchingStepField m X → Finset (Fin m × TreeNode))
    (hpopulation : ∀ s : Finset (Fin m × TreeNode),
      MeasurableSet[hτ.measurableSpace] {step | population step = s})
    (hdepth : ∀ step (u : Fin m × TreeNode), u ∈ population step →
      ∀ n : ℕ, τ step = (n : WithTop ℕ) → u.2.length = n)
    (A : Set (FiniteRootBranchingStepField m X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (s : Finset (Fin m × TreeNode))
    (roots : Fin k → Fin m × TreeNode)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (B : Set (Fin k → TreeNode → BranchingStep ℕ X))
    (hB : MeasurableSet B) :
    finiteRootBranchingStepFieldLaw μ m
        ((A ∩ {step | population step = s}) ∩
          multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootBranchingStepFieldLaw μ m (A ∩ {step | population step = s}) *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  let P := finiteRootBranchingStepFieldLaw μ m
  let Q := Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)
  let E : Set (FiniteRootBranchingStepField m X) :=
    A ∩ {step | population step = s}
  let C : ℕ → Set (FiniteRootBranchingStepField m X) :=
    fun n => E ∩ {step | τ step = (n : WithTop ℕ)}
  let D : ℕ → Set (FiniteRootBranchingStepField m X) :=
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
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (τ : FiniteRootBranchingStepField m X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤)
    (population : FiniteRootBranchingStepField m X → Finset (Fin m × TreeNode))
    (hpopulation : ∀ s : Finset (Fin m × TreeNode),
      MeasurableSet[hτ.measurableSpace] {step | population step = s})
    (hdepth : ∀ step (u : Fin m × TreeNode), u ∈ population step →
      ∀ n : ℕ, τ step = (n : WithTop ℕ) → u.2.length = n)
    (s : Finset (Fin m × TreeNode)) :
    ∃ roots : Fin s.card → Fin m × TreeNode,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (FiniteRootBranchingStepField m X))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → TreeNode → BranchingStep ℕ X))
        (_ : MeasurableSet B),
        finiteRootBranchingStepFieldLaw μ m
            ((A ∩ {step | population step = s}) ∩
              multiRootSubtreeStepFieldVector roots ⁻¹' B) =
          finiteRootBranchingStepFieldLaw μ m
              (A ∩ {step | population step = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => branchingStepFieldLaw μ)) B := by
  obtain ⟨roots, hcover, hinj⟩ := finiteMultiRootAddress_enumeration s
  exact ⟨roots, hcover, fun A hA B hB =>
    abstractStoppedPopulation_cell_factorization μ τ hτ hfinite population
      hpopulation hdepth A hA s roots hcover hinj B hB⟩

end ThesisSpeed
