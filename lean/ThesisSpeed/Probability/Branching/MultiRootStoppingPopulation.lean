import ThesisSpeed.Probability.Branching.SelectedPopulationBranching
import ThesisSpeed.Probability.Timing.Stopping
import ThesisSpeed.Probability.Population.Processes.Selected

/-!
# Branching for a finite multi-root population at a stopping time

This file removes the fixed-cardinality restriction from the stopped
branching argument.  A random finite population is first partitioned by its
value `s` and by the finite value of the stopping time.  On each such cell,
the fixed enumeration of `s` lies at one deterministic generation, so the
deterministic multi-root branching theorem applies.

The statement includes `s = ∅`.  Thus extinction and offspring point
processes with no atoms require no exceptional convention.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-! The concrete selected population read at a random generation. -/

noncomputable def selectedPopulationAt
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (τ : MultiRootTree m → WithTop ℕ) :
    MultiRootTree m → Finset (RootAddress m) :=
  fun ω => match τ ω with
    | ⊤ => ∅
    | (n : ℕ) => selectedPopulation N x n ω

theorem selectedPopulationAt_cell_measurable {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (τ : MultiRootTree m → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootFiltration m) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (s : Finset (RootAddress m)) :
    MeasurableSet[hτ.measurableSpace]
      {ω | selectedPopulationAt N x τ ω = s} := by
  classical
  let U : Set (MultiRootTree m) :=
    ⋃ n : ℕ, {ω | τ ω = (n : WithTop ℕ)} ∩
      {ω | selectedPopulation N x n ω = s}
  have hU : MeasurableSet[hτ.measurableSpace] U := by
    apply MeasurableSet.iUnion
    intro n
    have ht : MeasurableSet[hτ.measurableSpace]
        {ω | τ ω = (n : WithTop ℕ)} :=
      hτ.measurable (measurableSet_singleton (n : WithTop ℕ))
    have hp : MeasurableSet[multiRootFiltration m n]
        {ω | selectedPopulation N x n ω = s} :=
      selectedPopulation_adapted N x n (measurableSet_singleton s)
    have htgen' := (hτ.measurableSet_inter_eq_iff Set.univ n).1
        (MeasurableSet.univ.inter
          (hτ.measurable (measurableSet_singleton (n : WithTop ℕ))))
    have htgen : MeasurableSet[multiRootFiltration m n]
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
    (τ : MultiRootTree m → WithTop ℕ)
    (ω : MultiRootTree m) (u : RootAddress m)
    (hu : u ∈ selectedPopulationAt N x τ ω) :
    ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n := by
  intro n hn
  simpa [selectedPopulationAt, hn] using
    selectedPopulation_depth N x n ω u (by simpa [selectedPopulationAt, hn] using hu)

/-- A stopped event intersected with one value of the stopping time is
observable in the corresponding deterministic generation domain. -/
theorem multiRoot_stoppedCell_measurable {m : ℕ}
    (τ : MultiRootTree m → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootFiltration m) τ)
    (E : Set (MultiRootTree m))
    (hE : MeasurableSet[hτ.measurableSpace] E)
    (n : ℕ) :
    MeasurableSet[multiRootFiltration m n]
      (E ∩ {ω | τ ω = (n : WithTop ℕ)}) :=
  (hτ.measurableSet_inter_eq_iff E n).1
    (hE.inter (hτ.measurable
      (measurableSet_singleton (n : WithTop ℕ))))

/-- On a prescribed value `s` of a finite population selected at a finite
stopping time, the descendant trees of all particles in `s` have the
independent product law.  Measurability is required only for the population
as a map out of the stopped domain sigma algebra. -/
theorem multiRoot_stoppedPopulation_cell_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m k : ℕ}
    (τ : MultiRootTree m → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootFiltration m) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (population : MultiRootTree m → Finset (RootAddress m))
    (hpopulation : Measurable[hτ.measurableSpace] population)
    (hdepth : ∀ ω (u : RootAddress m), u ∈ population ω →
      ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n)
    (A : Set (MultiRootTree m))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (s : Finset (RootAddress m))
    (roots : Fin k → RootAddress m)
    (hcover : s = Finset.univ.image roots)
    (hinj : Function.Injective roots)
    (B : Set (Fin k → MarkedTree OffspringMark))
    (hB : MeasurableSet B) :
    iidMultiRootLaw μ m
        ((A ∩ {ω | population ω = s}) ∩
          multiRootSubtreeVector roots ⁻¹' B) =
      iidMultiRootLaw μ m (A ∩ {ω | population ω = s}) *
        (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
  let P := iidMultiRootLaw μ m
  let Q := Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)
  let E : Set (MultiRootTree m) := A ∩ {ω | population ω = s}
  let C : ℕ → Set (MultiRootTree m) :=
    fun n => E ∩ {ω | τ ω = (n : WithTop ℕ)}
  let D : ℕ → Set (MultiRootTree m) :=
    fun n => C n ∩ multiRootSubtreeVector roots ⁻¹' B
  have hE : MeasurableSet[hτ.measurableSpace] E :=
    hA.inter (hpopulation (measurableSet_singleton s))
  have hCgen n : MeasurableSet[multiRootFiltration m n] (C n) :=
    multiRoot_stoppedCell_measurable τ hτ E hE n
  have hCmeas n : MeasurableSet (C n) :=
    (multiRootFiltration m |>.le n) _ (hCgen n)
  have hDmeas n : MeasurableSet (D n) :=
    (hCmeas n).inter ((multiRootSubtreeVector_measurable roots) hB)
  have hcell n : P (D n) = P (C n) * Q B := by
    by_cases hlen : ∀ j, (roots j).2.length = n
    · exact fixed_multiRootSubtreeVector_event_factorization μ roots hlen hinj
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
      E ∩ multiRootSubtreeVector roots ⁻¹' B := by
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
    P (E ∩ multiRootSubtreeVector roots ⁻¹' B) = P (⋃ n, D n) := by
      rw [hDunion]
    _ = ∑' n, P (D n) := measure_iUnion hDpair hDmeas
    _ = ∑' n, P (C n) * Q B := tsum_congr hcell
    _ = (∑' n, P (C n)) * Q B := ENNReal.tsum_mul_right
    _ = P E * Q B := by rw [hCsum]

/-- Every cell of a stopped finite population admits an enumeration whose
descendant vector branches with the appropriate (cell-dependent) finite
product law. -/
theorem multiRoot_stoppedPopulation_each_cell_branches
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {m : ℕ}
    (τ : MultiRootTree m → WithTop ℕ)
    (hτ : IsStoppingTime (multiRootFiltration m) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (population : MultiRootTree m → Finset (RootAddress m))
    (hpopulation : Measurable[hτ.measurableSpace] population)
    (hdepth : ∀ ω (u : RootAddress m), u ∈ population ω →
      ∀ n : ℕ, τ ω = (n : WithTop ℕ) → u.2.length = n)
    (s : Finset (RootAddress m)) :
    ∃ roots : Fin s.card → RootAddress m,
      s = Finset.univ.image roots ∧
      ∀ (A : Set (MultiRootTree m))
        (_ : MeasurableSet[hτ.measurableSpace] A)
        (B : Set (Fin s.card → MarkedTree OffspringMark))
        (_ : MeasurableSet B),
        iidMultiRootLaw μ m
            ((A ∩ {ω | population ω = s}) ∩
              multiRootSubtreeVector roots ⁻¹' B) =
          iidMultiRootLaw μ m (A ∩ {ω | population ω = s}) *
            (Measure.infinitePi
              (fun _ : Fin s.card => iidMarkedTreeLaw μ)) B := by
  obtain ⟨roots, hcover, hinj⟩ := finiteRootAddress_enumeration s
  exact ⟨roots, hcover, fun A hA B hB =>
    multiRoot_stoppedPopulation_cell_factorization μ τ hτ hfinite
      population hpopulation hdepth A hA s roots hcover hinj B hB⟩

end ThesisSpeed
