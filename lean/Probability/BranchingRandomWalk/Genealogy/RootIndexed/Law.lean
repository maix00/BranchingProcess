import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Positions
import MeasureTheory.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Step.Law
import MeasureTheory.BranchingWalk.Cloud.Order.Basic
import Mathlib.Probability.Independence.InfinitePi

/-!
# Product laws on root-indexed step fields

One i.i.d. step field is attached to each initial root. `finiteRoot...` is the
`Fin m` case, and the marginal, reindexing, and independence statements below
are what the multi-root population arguments consume.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory



/-! ## The root-indexed product law -/

noncomputable def rootIndexedStepFieldLaw
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) :
    Measure (RootIndexedStepField Root X) :=
  Measure.infinitePi (fun _ : Root => stepFieldLaw (α := ℕ) μ)

instance rootIndexedStepFieldLaw.isProbabilityMeasure
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure
      (rootIndexedStepFieldLaw (Root := Root) μ) := by
  unfold rootIndexedStepFieldLaw
  infer_instance

theorem rootIndexedStepFieldLaw_reindex
    {Root NewRoot X : Type*} [Countable Root] [Countable NewRoot]
    [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (f : NewRoot → Root) (hf : Function.Injective f) :
    (rootIndexedStepFieldLaw (Root := Root) μ).map
        (RootIndexedStepField.reindex f) =
      rootIndexedStepFieldLaw (Root := NewRoot) μ := by
  unfold rootIndexedStepFieldLaw
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Root => stepFieldLaw (α := ℕ) μ) (f := f) hf

/-! ## The finite-root case -/

noncomputable abbrev finiteRootStepFieldLaw
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) (m : ℕ) :
    Measure (FiniteRootStepField m X) :=
  rootIndexedStepFieldLaw (Root := Fin m) μ

theorem countableRootStepFieldLaw_first
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (m : ℕ) :
    (rootIndexedStepFieldLaw (Root := ℕ) μ).map
        (RootIndexedStepField.first m) =
      finiteRootStepFieldLaw μ m := by
  exact rootIndexedStepFieldLaw_reindex μ
    (fun i : Fin m => i.val) Fin.val_injective

theorem finiteRootStepFieldLaw_first
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {m n : ℕ} (h : m ≤ n) :
    (finiteRootStepFieldLaw μ n).map
        (FiniteRootStepField.first h) =
      finiteRootStepFieldLaw μ m := by
  exact rootIndexedStepFieldLaw_reindex μ
    (Fin.castLE h) (fun a b hij =>
      Fin.ext (congrArg (fun z : Fin n => z.val) hij))

theorem finiteRootStepFieldLaw_root_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) :
    (finiteRootStepFieldLaw μ m).map (fun ω => ω i) =
      stepFieldLaw μ := by
  simpa [finiteRootStepFieldLaw,
    rootIndexedStepFieldLaw] using
    (Measure.infinitePi_map_eval
      (fun _ : Fin m => stepFieldLaw μ) i)

theorem finiteRootStepFieldLaw_coordinate_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) (u : 𝕍) :
    (finiteRootStepFieldLaw μ m).map (fun ω => ω i u) = μ := by
  calc
    (finiteRootStepFieldLaw μ m).map (fun ω => ω i u) =
        ((finiteRootStepFieldLaw μ m).map (fun ω => ω i)).map
          (fun field => field u) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_pi_apply u
            · exact measurable_pi_apply i
    _ = μ := by rw [finiteRootStepFieldLaw_root_marginal μ i,
      stepFieldLaw_coordinate μ u]

theorem finiteRootStepFieldLaw_roots_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] (m : ℕ) :
    iIndepFun (fun i (ω : FiniteRootStepField m X) => ω i)
      (finiteRootStepFieldLaw μ m) := by
  unfold finiteRootStepFieldLaw rootIndexedStepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Fin m => stepFieldLaw μ)
    (X := fun _ => id)
    (fun _ => measurable_id))

/-- A one-node event of measure one transports to every coordinate of every
root of the finite-root product law. -/
theorem finiteRootStepFieldLaw_ae_all_of_measure_one
    {s : Set NatRealStep} (hs : MeasurableSet s)
    (μ : Measure NatRealStep) [IsProbabilityMeasure μ]
    (hμ : μ s = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ s := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hmeas : Measurable
      (fun step : FiniteRootStepField m ℝ => step i u) :=
    (measurable_pi_apply u).comp (measurable_pi_apply i)
  have hpre : finiteRootStepFieldLaw μ m
      {step : FiniteRootStepField m ℝ | step i u ∈ s} = μ s := by
    calc
      finiteRootStepFieldLaw μ m
          {step : FiniteRootStepField m ℝ | step i u ∈ s} =
          ((finiteRootStepFieldLaw μ m).map
            (fun step : FiniteRootStepField m ℝ => step i u)) s := by
            rw [Measure.map_apply hmeas hs]
            rfl
      _ = μ s := by
            rw [finiteRootStepFieldLaw_coordinate_marginal μ i u]
  change ∀ᵐ step ∂finiteRootStepFieldLaw μ m,
    step ∈ (fun step : FiniteRootStepField m ℝ => step i u) ⁻¹' s
  apply (ae_mem_iff_measure_eq (hmeas hs).nullMeasurableSet).2
  change finiteRootStepFieldLaw μ m
      {step : FiniteRootStepField m ℝ | step i u ∈ s} =
    (finiteRootStepFieldLaw μ m) Set.univ
  rw [hpre, hμ]
  simp

theorem finiteRootStepFieldLaw_all_ordered
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ orderedSteps = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ orderedSteps :=
  finiteRootStepFieldLaw_ae_all_of_measure_one
    orderedSteps_measurable μ hμ m

theorem finiteRootStepFieldLaw_all_nonempty
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ nonemptySupport = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ nonemptySupport :=
  finiteRootStepFieldLaw_ae_all_of_measure_one
    nonemptySupport_measurable μ hμ m

/-- Ordered support together with the thesis's at-least-one-child assumption
forces slot zero at every address of every initial root, simultaneously. -/
theorem finiteRootStepFieldLaw_all_first_child
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hordered : μ orderedSteps = 1)
    (hnonempty : μ nonemptySupport = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ childRealized 0 := by
  filter_upwards [finiteRootStepFieldLaw_all_ordered μ hordered m,
    finiteRootStepFieldLaw_all_nonempty μ hnonempty m] with step hord hne
  intro i u
  obtain ⟨j, hj⟩ := hne i u
  exact orderedSteps_present_of_le (step i u) (hord i u) (Nat.zero_le j) hj

end ProbabilityTheory.BranchingRandomWalk
