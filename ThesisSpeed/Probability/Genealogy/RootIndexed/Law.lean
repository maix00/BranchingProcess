import ThesisSpeed.Probability.Genealogy.RootIndexed.Positions
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

noncomputable abbrev finiteRootBranchingStepFieldLaw
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) (m : ℕ) :
    Measure (FiniteRootBranchingStepField m X) :=
  rootIndexedBranchingStepFieldLaw (Root := Fin m) μ

theorem countableRootBranchingStepFieldLaw_first
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (m : ℕ) :
    (rootIndexedBranchingStepFieldLaw (Root := ℕ) μ).map
        (RootIndexedBranchingStepField.first m) =
      finiteRootBranchingStepFieldLaw μ m := by
  exact rootIndexedBranchingStepFieldLaw_reindex μ
    (fun i : Fin m => i.val) Fin.val_injective

theorem finiteRootBranchingStepFieldLaw_first
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {m n : ℕ} (h : m ≤ n) :
    (finiteRootBranchingStepFieldLaw μ n).map
        (FiniteRootBranchingStepField.first h) =
      finiteRootBranchingStepFieldLaw μ m := by
  exact rootIndexedBranchingStepFieldLaw_reindex μ
    (Fin.castLE h) (fun a b hij =>
      Fin.ext (congrArg (fun z : Fin n => z.val) hij))

theorem finiteRootBranchingStepFieldLaw_root_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) :
    (finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i) =
      branchingStepFieldLaw μ := by
  simpa [finiteRootBranchingStepFieldLaw,
    rootIndexedBranchingStepFieldLaw] using
    (Measure.infinitePi_map_eval
      (fun _ : Fin m => branchingStepFieldLaw μ) i)

theorem finiteRootBranchingStepFieldLaw_coordinate_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) (u : 𝕍) :
    (finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i u) = μ := by
  calc
    (finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i u) =
        ((finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i)).map
          (fun field => field u) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_pi_apply u
            · exact measurable_pi_apply i
    _ = μ := by rw [finiteRootBranchingStepFieldLaw_root_marginal μ i,
      branchingStepFieldLaw_coordinate μ u]

theorem finiteRootBranchingStepFieldLaw_roots_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] (m : ℕ) :
    iIndepFun (fun i (ω : FiniteRootBranchingStepField m X) => ω i)
      (finiteRootBranchingStepFieldLaw μ m) := by
  unfold finiteRootBranchingStepFieldLaw rootIndexedBranchingStepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Fin m => branchingStepFieldLaw μ)
    (X := fun _ => id)
    (fun _ => measurable_id))

theorem finiteRootBranchingStepFieldLaw_all_ordered
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ ξ ∂μ, OrderedNatRealBranchingStep ξ)
    (hordered : MeasurableSet
      {ξ : BranchingStep ℕ ℝ | OrderedNatRealBranchingStep ξ})
    (m : ℕ) :
    ∀ᵐ step ∂finiteRootBranchingStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, OrderedNatRealBranchingStep (step i u) := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hmarg := finiteRootBranchingStepFieldLaw_coordinate_marginal μ i u
  rw [← hmarg] at hμ
  have hcoord : Measurable
      (fun step : FiniteRootBranchingStepField m ℝ => step i u) :=
    (measurable_pi_apply u).comp (measurable_pi_apply i)
  exact (ae_map_iff hcoord.aemeasurable hordered).1 hμ

end ThesisSpeed
