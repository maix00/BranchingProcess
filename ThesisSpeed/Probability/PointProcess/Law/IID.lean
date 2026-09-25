import ThesisSpeed.Probability.PointProcess.Legacy.WeightedSlot
import ThesisSpeed.Probability.Genealogy.Tree
import ThesisSpeed.Probability.PointProcess.Legacy.PositionsWeighted
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent offspring marks on the pre-sampled tree

Given any probability law on the general countable-offspring mark space,
mathlib's infinite product supplies an independent mark at every Ulam--Harris
address, including addresses that a later selection rule never visits.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

variable (μ : Measure WeightedBranchingStep) [IsProbabilityMeasure μ]

/-- The i.i.d. marked-tree law. -/
noncomputable def iidMarkLaw : Measure (Mark ℕ WeightedBranchingStep) :=
  Measure.infinitePi (fun _ : 𝕍 => μ)

instance : IsProbabilityMeasure (iidMarkLaw μ) := by
  unfold iidMarkLaw
  infer_instance

/-- Each fixed address has the prescribed offspring law. -/
theorem iidMark_marginal (u : 𝕍) :
    (iidMarkLaw μ).map (fun ω : Mark ℕ WeightedBranchingStep => ω u) = μ := by
  simpa [iidMarkLaw] using
    (Measure.infinitePi_map_eval (fun _ : 𝕍 => μ) u)

/-- All offspring marks are jointly independent; future reserve branches are
already present in this product and are never sampled retrospectively. -/
theorem iidMark_independent :
    iIndepFun (fun u (ω : Mark ℕ WeightedBranchingStep) => ω u)
      (iidMarkLaw μ) := by
  unfold iidMarkLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : 𝕍 => μ)
    (X := fun _ : 𝕍 => id)
    (fun _ => measurable_id))

/-- Any injective reindexing of the pre-sampled offspring coordinates remains
jointly independent.  This is the reusable cross-generation input for spine
increments and reserve branches. -/
theorem iidMark_injective_coordinates_independent
    {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (f : ι → 𝕍) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : Mark ℕ WeightedBranchingStep) => ω (f i))
      (iidMarkLaw μ) := by
  exact (iidMark_independent μ).precomp hf

/-- Measurable functions of injectively reindexed marks remain independent.
This is the exact form used when turning offspring marks into increment
observables. -/
theorem iidMark_injective_coordinates_comp_independent
    (μ : Measure WeightedBranchingStep) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (f : ι → 𝕍) (hf : Function.Injective f)
    (g : ∀ i, WeightedBranchingStep → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (ω : Mark ℕ WeightedBranchingStep) => g i (ω (f i)))
      (iidMarkLaw μ) := by
  exact (iidMark_injective_coordinates_independent μ f hf).comp
    (fun i => g i) hg

theorem iidMark_injective_displacements_independent
    (μ : Measure WeightedBranchingStep) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (f : ι → 𝕍) (hf : Function.Injective f) :
    iIndepFun
      (fun i (ω : Mark ℕ WeightedBranchingStep) =>
        childDisplacement (ω (f i)) 0)
      (iidMarkLaw μ) := by
  apply iidMark_injective_coordinates_comp_independent μ f hf
    (fun _ ξ => childDisplacement ξ 0)
  intro i
  exact childDisplacement_measurable 0

theorem iidMark_injective_displacements_law
    (μ : Measure WeightedBranchingStep) [IsProbabilityMeasure μ]
    {k : ℕ} (f : Fin k → 𝕍)
    (hf : Function.Injective f) :
    (iidMarkLaw μ).map
        (fun ω i => childDisplacement (ω (f i)) 0) =
      Measure.infinitePi
        (fun _ : Fin k => μ.map (fun ξ => childDisplacement ξ 0)) := by
  have h := (iidMark_injective_displacements_independent μ f hf)
  have hmeas : ∀ i : Fin k, Measurable
      (fun ω : Mark ℕ WeightedBranchingStep =>
        childDisplacement (ω (f i)) 0) := by
    intro i
    exact (childDisplacement_measurable 0).comp
      (measurable_pi_apply (f i))
  rw [h.map_fun_eq_infinitePi_map hmeas]
  apply congrArg Measure.infinitePi
  funext i
  calc
    Measure.map (fun ω : Mark ℕ WeightedBranchingStep =>
        childDisplacement (ω (f i)) 0) (iidMarkLaw μ) =
      ((iidMarkLaw μ).map (fun ω => ω (f i))).map
        (fun ξ => childDisplacement ξ 0) := by
          rw [Measure.map_map]
          · rfl
          · exact childDisplacement_measurable 0
          · exact measurable_pi_apply (f i)
    _ = μ.map (fun ξ => childDisplacement ξ 0) := by
      rw [iidMark_marginal μ (f i)]

end ThesisSpeed
