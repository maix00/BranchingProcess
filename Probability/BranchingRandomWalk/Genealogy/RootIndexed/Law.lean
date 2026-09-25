import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Positions
import Probability.BranchingRandomWalk.Step.Law
import Combinatorics.BranchingStep.Slot.Order
import Mathlib.Probability.Independence.InfinitePi

/-!
# Product laws on root-indexed step fields

One i.i.d. step field is attached to each initial root. `finiteRoot...` is the
`Fin m` case, and the marginal, reindexing, and independence statements below
are what the multi-root population arguments consume.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-! ## The root-indexed product law -/

noncomputable def rootIndexedBranchingStepFieldLaw
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) :
    Measure (RootIndexedBranchingStepField Root X) :=
  Measure.infinitePi (fun _ : Root => branchingStepFieldLaw (α := ℕ) μ)

instance rootIndexedBranchingStepFieldLaw.isProbabilityMeasure
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure
      (rootIndexedBranchingStepFieldLaw (Root := Root) μ) := by
  unfold rootIndexedBranchingStepFieldLaw
  infer_instance

theorem rootIndexedBranchingStepFieldLaw_reindex
    {Root NewRoot X : Type*} [Countable Root] [Countable NewRoot]
    [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (f : NewRoot → Root) (hf : Function.Injective f) :
    (rootIndexedBranchingStepFieldLaw (Root := Root) μ).map
        (RootIndexedBranchingStepField.reindex f) =
      rootIndexedBranchingStepFieldLaw (Root := NewRoot) μ := by
  unfold rootIndexedBranchingStepFieldLaw
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Root => branchingStepFieldLaw (α := ℕ) μ) (f := f) hf

/-! ## The finite-root case -/

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

/-- A one-node event of measure one transports to every coordinate of every
root of the finite-root product law. -/
theorem finiteRootBranchingStepFieldLaw_ae_all_of_measure_one
    {s : Set NatRealBranchingStep} (hs : MeasurableSet s)
    (μ : Measure NatRealBranchingStep) [IsProbabilityMeasure μ]
    (hμ : μ s = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootBranchingStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ s := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hmeas : Measurable
      (fun step : FiniteRootBranchingStepField m ℝ => step i u) :=
    (measurable_pi_apply u).comp (measurable_pi_apply i)
  have hpre : finiteRootBranchingStepFieldLaw μ m
      {step : FiniteRootBranchingStepField m ℝ | step i u ∈ s} = μ s := by
    calc
      finiteRootBranchingStepFieldLaw μ m
          {step : FiniteRootBranchingStepField m ℝ | step i u ∈ s} =
          ((finiteRootBranchingStepFieldLaw μ m).map
            (fun step : FiniteRootBranchingStepField m ℝ => step i u)) s := by
            rw [Measure.map_apply hmeas hs]
            rfl
      _ = μ s := by
            rw [finiteRootBranchingStepFieldLaw_coordinate_marginal μ i u]
  change ∀ᵐ step ∂finiteRootBranchingStepFieldLaw μ m,
    step ∈ (fun step : FiniteRootBranchingStepField m ℝ => step i u) ⁻¹' s
  apply (ae_mem_iff_measure_eq (hmeas hs).nullMeasurableSet).2
  change finiteRootBranchingStepFieldLaw μ m
      {step : FiniteRootBranchingStepField m ℝ | step i u ∈ s} =
    (finiteRootBranchingStepFieldLaw μ m) Set.univ
  rw [hpre, hμ]
  simp

theorem finiteRootBranchingStepFieldLaw_all_ordered
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ orderedBranchingSteps = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootBranchingStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ orderedBranchingSteps :=
  finiteRootBranchingStepFieldLaw_ae_all_of_measure_one
    orderedBranchingSteps_measurable μ hμ m

theorem finiteRootBranchingStepFieldLaw_all_nonempty
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ childNonempty = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootBranchingStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ childNonempty :=
  finiteRootBranchingStepFieldLaw_ae_all_of_measure_one
    childNonempty_measurable μ hμ m

/-- Ordered support together with the thesis's at-least-one-child assumption
forces slot zero at every address of every initial root, simultaneously. -/
theorem finiteRootBranchingStepFieldLaw_all_first_child
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    (hordered : μ orderedBranchingSteps = 1)
    (hnonempty : μ childNonempty = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootBranchingStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ childRealized 0 := by
  filter_upwards [finiteRootBranchingStepFieldLaw_all_ordered μ hordered m,
    finiteRootBranchingStepFieldLaw_all_nonempty μ hnonempty m] with step hord hne
  intro i u
  obtain ⟨j, hj⟩ := hne i u
  exact orderedBranchingSteps_first_present (step i u) (hord i u) j hj

end ProbabilityTheory.BranchingRandomWalk
