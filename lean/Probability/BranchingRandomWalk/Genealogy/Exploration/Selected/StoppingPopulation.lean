import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.CellBranching
import Probability.BranchingRandomWalk.Timing.Stopping
import Probability.BranchingRandomWalk.Population.Processes.Selected

/-!
# Branching for a finite multi-root population at a stopping time

This file removes the fixed-cardinality restriction from the stopped
branching argument.  A random finite population is first partitioned by its
value `s` and by the finite value of the stopping time.  On each such cell,
the fixed enumeration of `s` lies at one deterministic generation, so the
deterministic multi-root branching theorem applies.

The statement includes `s = ∅`.  Thus extinction and branching-step point processes with no atoms require no exceptional convention. This file contains
the population read at a random generation, its cell measurability, the cell
partition, and the measure of each cell; the cellwise branching laws are in
`Selected/StoppingCellBranching/`.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-! The concrete selected population read at a random generation. -/

noncomputable def selectedPopulationAt
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ) :
    FiniteRootBranchingStepField m ℝ → Finset (RootAddress m) :=
  fun ω => match τ ω with
    | ⊤ => ∅
    | (n : ℕ) => selectedPopulation N x n ω

theorem selectedPopulationAt_cell_measurable {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (s : Finset (RootAddress m)) :
    MeasurableSet[hτ.measurableSpace]
      {ω | selectedPopulationAt N x τ ω = s} := by
  classical
  let U : Set (FiniteRootBranchingStepField m ℝ) :=
    ⋃ n : ℕ, {ω | τ ω = (n : WithTop ℕ)} ∩
      {ω | selectedPopulation N x n ω = s}
  have hU : MeasurableSet[hτ.measurableSpace] U := by
    apply MeasurableSet.iUnion
    intro n
    have ht : MeasurableSet[hτ.measurableSpace]
        {ω | τ ω = (n : WithTop ℕ)} :=
      hτ.measurable (measurableSet_singleton (n : WithTop ℕ))
    have hp : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
        {ω | selectedPopulation N x n ω = s} :=
      selectedPopulation_adapted N x n (measurableSet_singleton s)
    have htgen' := (hτ.measurableSet_inter_eq_iff Set.univ n).1
        (MeasurableSet.univ.inter
          (hτ.measurable (measurableSet_singleton (n : WithTop ℕ))))
    have htgen : MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
        {ω | τ ω = (n : WithTop ℕ)} := by
      convert htgen' using 1 <;> simp
    have hpn := (hτ.measurableSet_inter_eq_iff
      {ω | selectedPopulation N x n ω = s} n).2
      (by simpa [Set.inter_comm] using htgen.inter hp)
    simpa [Set.inter_comm] using hpn
  have heq : {ω | selectedPopulationAt N x τ ω = s} = U := by
    ext ω
    constructor
    · intro hs
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n =>
          apply Set.mem_iUnion.mpr
          refine ⟨n, ?_, ?_⟩
          · exact htime
          · change selectedPopulationAt N x τ ω = s at hs
            simpa [selectedPopulationAt, htime] using hs
    · intro hs
      obtain ⟨n, ht, hp⟩ := Set.mem_iUnion.mp hs
      change selectedPopulationAt N x τ ω = s
      change (match τ ω with
        | ⊤ => ∅
        | (n : ℕ) => selectedPopulation N x n ω) = s
      rw [ht]
      exact hp
  rw [heq]
  exact hU

theorem selectedPopulationAt_depth {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ)
    (ω : FiniteRootBranchingStepField m ℝ) (u : RootAddress m)
    (hu : u ∈ selectedPopulationAt N x τ ω) :
    ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n := by
  intro n hn
  simpa [selectedPopulationAt, hn] using
    selectedPopulation_depth N x n ω u (by simpa [selectedPopulationAt, hn] using hu)

/-- A stopped event intersected with one value of the stopping time is
observable in the corresponding deterministic generation domain. -/
theorem multiRoot_stoppedCell_measurable {m : ℕ}
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (E : Set (FiniteRootBranchingStepField m ℝ))
    (hE : MeasurableSet[hτ.measurableSpace] E)
    (n : ℕ) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := ℝ) n]
      (E ∩ {ω | τ ω = (n : WithTop ℕ)}) :=
    (hτ.measurableSet_inter_eq_iff E n).1
    (hE.inter (hτ.measurable
      (measurableSet_singleton (n : WithTop ℕ))))

/-- Finite-population cells form the canonical countable partition of a
stopped event.  This is the measure-theoretic random-cardinality layer. -/
theorem multiRoot_stoppedPopulation_cells_partition
    {m : ℕ}
    (population : FiniteRootBranchingStepField m ℝ → Finset (RootAddress m))
    (A : Set (FiniteRootBranchingStepField m ℝ)) :
    Pairwise (fun s t =>
      Disjoint (A ∩ {ω | population ω = s})
        (A ∩ {ω | population ω = t})) ∧
      (⋃ s : Finset (RootAddress m),
        A ∩ {ω | population ω = s}) = A := by
  constructor
  · intro s t hst
    apply Set.disjoint_left.mpr
    intro ω hs ht
    exact hst (hs.2.symm.trans ht.2)
  · ext ω
    constructor
    · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨s, hAω, _⟩
      exact hAω
    · intro hω
      exact Set.mem_iUnion.mpr ⟨population ω, hω, rfl⟩

/-- The preceding partition is measurable in the stopped domain and hence
admits countable measure summation. -/
theorem multiRoot_stoppedPopulation_cells_measure_sum
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    {m : ℕ}
    (τ : FiniteRootBranchingStepField m ℝ → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootStepFiltration (m := m) (X := ℝ)) τ)
    (population : FiniteRootBranchingStepField m ℝ → Finset (RootAddress m))
    (hpopulation : ∀ s : Finset (RootAddress m),
      MeasurableSet[hτ.measurableSpace] {ω | population ω = s})
    (A : Set (FiniteRootBranchingStepField m ℝ))
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∑' s : Finset (RootAddress m),
      finiteRootBranchingStepFieldLaw μ m (A ∩ {ω | population ω = s})) =
      finiteRootBranchingStepFieldLaw μ m A := by
  obtain ⟨hpair, hunion⟩ := multiRoot_stoppedPopulation_cells_partition
    population A
  have hmeas : ∀ s : Finset (RootAddress m),
      MeasurableSet (A ∩ {ω | population ω = s}) := by
    intro s
    exact (hτ.measurableSpace_le _ hA).inter
      (hτ.measurableSpace_le _ (hpopulation s))
  calc
    (∑' s : Finset (RootAddress m),
        finiteRootBranchingStepFieldLaw μ m (A ∩ {ω | population ω = s})) =
      finiteRootBranchingStepFieldLaw μ m (⋃ s : Finset (RootAddress m),
        A ∩ {ω | population ω = s}) :=
      (measure_iUnion hpair hmeas).symm
    _ = finiteRootBranchingStepFieldLaw μ m A := by rw [hunion]

end ProbabilityTheory.BranchingRandomWalk
