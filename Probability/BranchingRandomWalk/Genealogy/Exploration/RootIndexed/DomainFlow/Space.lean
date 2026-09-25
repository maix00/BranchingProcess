import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability

/-!
# Coordinate spaces of the multi-root step field

The coordinate space is `Fin m × 𝕍`. Splitting the coordinates into the
generations below and at or above `n` gives the past and future spaces, whose
generating coordinate families are independent and disjoint.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory


@[instance_reducible] def multiRootStepCoordinateSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (p : Fin m × 𝕍) : MeasurableSpace (FiniteRootStepField m X) :=
  MeasurableSpace.comap (fun ω => ω p.1 p.2) inferInstance

@[instance_reducible] def multiRootStepPastSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (FiniteRootStepField m X) :=
  ⨆ p ∈ {p : Fin m × 𝕍 | p.2.length < n},
    multiRootStepCoordinateSpace p

@[instance_reducible] def multiRootStepFutureSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (FiniteRootStepField m X) :=
  ⨆ p ∈ {p : Fin m × 𝕍 | n ≤ p.2.length},
    multiRootStepCoordinateSpace p

theorem multiRootStepGenerationSpace_eq_past
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    multiRootStepGenerationSpace (m := m) (X := X) n =
      multiRootStepPastSpace n := by
  apply le_antisymm
  · unfold multiRootStepGenerationSpace
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨i, u, hu, t, ht, rfl⟩
    have hle : multiRootStepCoordinateSpace (X := X) (i, u) ≤
        multiRootStepPastSpace n :=
      le_iSup_of_le (i, u) (le_iSup_of_le hu le_rfl)
    apply hle
    exact ⟨t, ht, rfl⟩
  · apply iSup_le
    intro p
    apply iSup_le
    intro hp
    exact (multiRootStep_measurable (X := X) p.1 p.2 hp).comap_le

theorem multiRootStep_coordinates_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] :
    iIndep (multiRootStepCoordinateSpace (m := m) (X := X))
      (finiteRootStepFieldLaw μ m) := by
  have h : iIndepFun
      (fun (p : Fin m × 𝕍) (ω : FiniteRootStepField m X) =>
        ω p.1 p.2) (finiteRootStepFieldLaw μ m) := by
    unfold finiteRootStepFieldLaw
      rootIndexedStepFieldLaw stepFieldLaw
    simpa using (iIndepFun_uncurry_infinitePi'
      (μ := fun (_ : Fin m) (_ : 𝕍) => μ)
      (X := fun (_ : Fin m) (_ : 𝕍) => id)
      (fun _ _ => measurable_id))
  exact h.iIndep

theorem multiRootStep_past_future_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    Indep (multiRootStepFiltration (m := m) (X := X) n)
      (multiRootStepFutureSpace n) (finiteRootStepFieldLaw μ m) := by
  have hle : ∀ p : Fin m × 𝕍,
      multiRootStepCoordinateSpace (X := X) p ≤
        (inferInstance : MeasurableSpace (FiniteRootStepField m X)) := by
    intro p
    have hmeas : Measurable
        (fun ω : FiniteRootStepField m X => ω p.1 p.2) :=
      (measurable_pi_apply p.2 : Measurable
        (fun field : 𝕍 → Step ℕ X => field p.2)).comp
        (measurable_pi_apply p.1 : Measurable
          (fun ω : FiniteRootStepField m X => ω p.1))
    exact hmeas.comap_le
  have hdisj : Disjoint
      {p : Fin m × 𝕍 | p.2.length < n}
      {p : Fin m × 𝕍 | n ≤ p.2.length} := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    change p.2.length < n at hp
    change n ≤ p.2.length at hq
    exact (not_lt_of_ge hq) hp
  rw [show multiRootStepFiltration (m := m) (X := X) n =
      multiRootStepGenerationSpace (m := m) (X := X) n from rfl,
    multiRootStepGenerationSpace_eq_past]
  exact indep_iSup_of_disjoint hle
    (multiRootStep_coordinates_independent μ) hdisj

end ProbabilityTheory.BranchingRandomWalk
