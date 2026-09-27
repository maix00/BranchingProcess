import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppedPopulation.Factorization

/-!
# A dependent law for a stopped finite population

The cardinality of a population observed at a stopping time is random.  This
file packages all fixed-cardinality descendant vectors in the single sigma
type `StoppedSubtreeFamily`.  Its law is the corresponding countable mixture
of finite product laws.  Empty populations are represented by the `k = 0`
fibre and need no exceptional convention.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- A finite family of descendant step fields with its cardinality retained
in the type. -/
abbrev StoppedSubtreeFamily (X : Type*) [MeasurableSpace X] :=
  Sigma (fun k : ℕ => Fin k → 𝕍 → Step ℕ X)

/-- The canonical measurable inclusion of one fixed-cardinality fibre into
the dependent family. -/
def stoppedSubtreeFamilyMk {X : Type*} [MeasurableSpace X] (k : ℕ) :
    (Fin k → 𝕍 → Step ℕ X) → StoppedSubtreeFamily X :=
  fun fields => ⟨k, fields⟩

theorem stoppedSubtreeFamilyMk_measurable
    {X : Type*} [MeasurableSpace X] (k : ℕ) :
    Measurable (stoppedSubtreeFamilyMk (X := X) k) := by
  rw [measurable_iff_le_map]
  exact iInf_le _ k

/-- A fixed duplicate-free enumeration of a finite population. -/
noncomputable def stoppedPopulationRoots {m : ℕ}
    (s : Finset (Fin m × 𝕍)) : Fin s.card → Fin m × 𝕍 :=
  Classical.choose (finiteMultiRootAddress_enumeration s)

theorem stoppedPopulationRoots_cover {m : ℕ}
    (s : Finset (Fin m × 𝕍)) :
    s = Finset.univ.image (stoppedPopulationRoots s) :=
  (Classical.choose_spec (finiteMultiRootAddress_enumeration s)).1

theorem stoppedPopulationRoots_injective {m : ℕ}
    (s : Finset (Fin m × 𝕍)) :
    Function.Injective (stoppedPopulationRoots s) :=
  (Classical.choose_spec (finiteMultiRootAddress_enumeration s)).2

/-- All descendant fields below a stopped finite population, packaged without
padding the random number of roots by dummy coordinates. -/
noncomputable def stoppedPopulationSubtrees
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (population : FiniteRootStepField m ℕ X → Finset (Fin m × 𝕍))
    (step : FiniteRootStepField m ℕ X) : StoppedSubtreeFamily X :=
  let s := population step
  stoppedSubtreeFamilyMk s.card
    (multiRootSubtreeStepFieldVector (stoppedPopulationRoots s) step)

/-- The dependent descendant family is a random variable on the full sample
space. The population itself is stopped-past measurable, while its descendant
fields necessarily use future coordinates. The proof partitions by the
countably many population values; within each cell its cardinality and root
enumeration are fixed. -/
theorem stoppedPopulationSubtrees_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (τ : FiniteRootStepField m ℕ X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (population : FiniteRootStepField m ℕ X → Finset (Fin m × 𝕍))
    (hpopulation : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet[hτ.measurableSpace] {step | population step = s}) :
    Measurable (stoppedPopulationSubtrees population) := by
  intro B hB
  have hsection : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet
        ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) := by
    intro s
    exact hB.preimage (stoppedSubtreeFamilyMk_measurable s.card)
  have hpieces : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet
        ({step | population step = s} ∩
          multiRootSubtreeStepFieldVector (stoppedPopulationRoots s) ⁻¹'
            ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B)) := by
    intro s
    exact (hτ.measurableSpace_le _ (hpopulation s)).inter
      ((multiRootSubtreeStepFieldVector_measurable
        (stoppedPopulationRoots s)) (hsection s))
  have heq : stoppedPopulationSubtrees population ⁻¹' B =
      ⋃ s : Finset (Fin m × 𝕍),
        {step | population step = s} ∩
          multiRootSubtreeStepFieldVector (stoppedPopulationRoots s) ⁻¹'
            ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) := by
    ext step
    constructor
    · intro h
      refine Set.mem_iUnion.mpr ⟨population step, rfl, ?_⟩
      exact h
    · intro h
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
      rcases hs with ⟨hpop, hBstep⟩
      change population step = s at hpop
      subst s
      exact hBstep
  rw [heq]
  exact MeasurableSet.iUnion hpieces

/-- The joint stopped branching law with random cardinality.  Conditional on
each population cell, the fibre has the appropriate finite product law; the
unconditional expression is their countable mixture. -/
theorem stoppedPopulationSubtrees_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (τ : FiniteRootStepField m ℕ X → WithTop ℕ)
    (hτ : IsStoppingTime
      (multiRootStepFiltration (m := m) (X := X)) τ)
    (hfinite : ∀ step, τ step ≠ ⊤)
    (population : FiniteRootStepField m ℕ X → Finset (Fin m × 𝕍))
    (hpopulation : ∀ s : Finset (Fin m × 𝕍),
      MeasurableSet[hτ.measurableSpace] {step | population step = s})
    (hdepth : ∀ step (u : Fin m × 𝕍), u ∈ population step →
      ∀ n : ℕ, τ step = (n : WithTop ℕ) → u.2.length = n)
    (A : Set (FiniteRootStepField m ℕ X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (B : Set (StoppedSubtreeFamily X)) (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
        (A ∩ stoppedPopulationSubtrees population ⁻¹' B) =
      ∑' s : Finset (Fin m × 𝕍),
        finiteRootStepFieldLaw μ m
            (A ∩ {step | population step = s}) *
          (Measure.infinitePi
            (fun _ : Fin s.card => stepFieldLaw μ))
            ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) := by
  let P := finiteRootStepFieldLaw μ m
  let D : Finset (Fin m × 𝕍) → Set (FiniteRootStepField m ℕ X) :=
    fun s => (A ∩ {step | population step = s}) ∩
      multiRootSubtreeStepFieldVector (stoppedPopulationRoots s) ⁻¹'
        ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B)
  have hsection (s : Finset (Fin m × 𝕍)) : MeasurableSet
      ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) :=
    hB.preimage (stoppedSubtreeFamilyMk_measurable s.card)
  have hDmeas (s : Finset (Fin m × 𝕍)) : MeasurableSet (D s) :=
    ((hτ.measurableSpace_le _ hA).inter
      (hτ.measurableSpace_le _ (hpopulation s))).inter
        ((multiRootSubtreeStepFieldVector_measurable
          (stoppedPopulationRoots s)) (hsection s))
  have hDpair : Pairwise (fun s t => Disjoint (D s) (D t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro step hs ht
    exact hst (hs.1.2.symm.trans ht.1.2)
  have hDunion : (⋃ s, D s) =
      A ∩ stoppedPopulationSubtrees population ⁻¹' B := by
    ext step
    constructor
    · intro h
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp h
      rcases hs with ⟨⟨hAstep, hpop⟩, hBstep⟩
      refine ⟨hAstep, ?_⟩
      subst s
      exact hBstep
    · rintro ⟨hAstep, hBstep⟩
      refine Set.mem_iUnion.mpr ⟨population step, ⟨⟨hAstep, rfl⟩, ?_⟩⟩
      exact hBstep
  have hcell s : P (D s) =
      P (A ∩ {step | population step = s}) *
        (Measure.infinitePi
          (fun _ : Fin s.card => stepFieldLaw μ))
          ((stoppedSubtreeFamilyMk (X := X) s.card) ⁻¹' B) := by
    exact abstractStoppedPopulation_cell_factorization μ τ hτ hfinite
      population hpopulation hdepth A hA s (stoppedPopulationRoots s)
      (stoppedPopulationRoots_cover s) (stoppedPopulationRoots_injective s)
      _ (hsection s)
  calc
    P (A ∩ stoppedPopulationSubtrees population ⁻¹' B) =
        P (⋃ s, D s) := by rw [hDunion]
    _ = ∑' s, P (D s) := measure_iUnion hDpair hDmeas
    _ = _ := tsum_congr hcell

end ProbabilityTheory.BranchingRandomWalk
