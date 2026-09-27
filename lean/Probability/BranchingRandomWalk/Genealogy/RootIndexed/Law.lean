import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Positions
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Step.Law
import Combinatorics.BranchingWalk.Step.Monotone
import Mathlib.Probability.Independence.InfinitePi
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Product laws on root-indexed step fields

One i.i.d. step field is attached to each initial root. `finiteRoot...` is the
`Fin m` case, and the marginal, reindexing, and independence statements below
are what the multi-root population arguments consume.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-! ## The root-indexed product law -/

noncomputable def RootIndexed.stepFieldLaw
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) :
    Measure (RootIndexed.StepField Root ℕ X) :=
  Measure.infinitePi (fun _ : Root =>
    ProbabilityTheory.BranchingRandomWalk.stepFieldLaw (α := ℕ) (X := X) μ)

instance RootIndexed.stepFieldLaw.isProbabilityMeasure
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  unfold RootIndexed.stepFieldLaw
  infer_instance

theorem RootIndexed.stepFieldLaw_reindex
    {Root NewRoot X : Type*} [Countable Root] [Countable NewRoot]
    [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (f : NewRoot → Root) (hf : Function.Injective f) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.StepField.reindex f) =
      RootIndexed.stepFieldLaw (Root := NewRoot) μ := by
  unfold RootIndexed.stepFieldLaw
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Root =>
      ProbabilityTheory.BranchingRandomWalk.stepFieldLaw (α := ℕ) (X := X) μ)
      (f := f) hf

/-! ## The finite-root case -/

noncomputable abbrev finiteRootStepFieldLaw
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) (m : ℕ) :
    Measure (FiniteRootStepField m ℕ X) :=
  RootIndexed.stepFieldLaw (Root := Fin m) μ

theorem countableRootStepFieldLaw_first
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (m : ℕ) :
    (RootIndexed.stepFieldLaw (Root := ℕ) μ).map
        (RootIndexed.StepField.first m) =
      finiteRootStepFieldLaw μ m := by
  exact RootIndexed.stepFieldLaw_reindex μ
    (fun i : Fin m => i.val) Fin.val_injective

theorem finiteRootStepFieldLaw_first
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {m n : ℕ} (h : m ≤ n) :
    (finiteRootStepFieldLaw μ n).map
        (FiniteRootStepField.first h) =
      finiteRootStepFieldLaw μ m := by
  exact RootIndexed.stepFieldLaw_reindex μ
    (Fin.castLE h) (fun a b hij =>
      Fin.ext (congrArg (fun z : Fin n => z.val) hij))

theorem finiteRootStepFieldLaw_root_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) :
    (finiteRootStepFieldLaw μ m).map (fun ω => ω i) =
      stepFieldLaw μ := by
  simpa [finiteRootStepFieldLaw,
    RootIndexed.stepFieldLaw] using
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
    iIndepFun (fun i (ω : FiniteRootStepField m ℕ X) => ω i)
      (finiteRootStepFieldLaw μ m) := by
  unfold finiteRootStepFieldLaw RootIndexed.stepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Fin m => stepFieldLaw μ)
    (X := fun _ => id)
    (fun _ => measurable_id))

/-- A one-node event of measure one transports to every coordinate of every
root of the finite-root product law. -/
theorem finiteRootStepFieldLaw_ae_all_of_measure_one
    {s : Set (Step ℕ ℝ)} (hs : MeasurableSet s)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ s = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ s := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hmeas : Measurable
      (fun step : FiniteRootStepField m ℕ ℝ => step i u) :=
    (measurable_pi_apply u).comp (measurable_pi_apply i)
  have hpre : finiteRootStepFieldLaw μ m
      {step : FiniteRootStepField m ℕ ℝ | step i u ∈ s} = μ s := by
    calc
      finiteRootStepFieldLaw μ m
          {step : FiniteRootStepField m ℕ ℝ | step i u ∈ s} =
          ((finiteRootStepFieldLaw μ m).map
            (fun step : FiniteRootStepField m ℕ ℝ => step i u)) s := by
            rw [Measure.map_apply hmeas hs]
            rfl
      _ = μ s := by
            rw [finiteRootStepFieldLaw_coordinate_marginal μ i u]
  change ∀ᵐ step ∂finiteRootStepFieldLaw μ m,
    step ∈ (fun step : FiniteRootStepField m ℕ ℝ => step i u) ⁻¹' s
  apply (ae_mem_iff_measure_eq (hmeas hs).nullMeasurableSet).2
  change finiteRootStepFieldLaw μ m
      {step : FiniteRootStepField m ℕ ℝ | step i u ∈ s} =
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
      ∀ u : 𝕍, survive (step i u) 0 := by
  filter_upwards [finiteRootStepFieldLaw_all_ordered μ hordered m,
    finiteRootStepFieldLaw_all_nonempty μ hnonempty m] with step hord hne
  intro i u
  obtain ⟨j, hj⟩ := hne i u
  exact orderedSteps_survive_of_le (step i u) (hord i u) (Nat.zero_le j) hj

end ProbabilityTheory.BranchingRandomWalk
