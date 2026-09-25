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

variable (μ : Measure OffspringMark) [IsProbabilityMeasure μ]

/-- The i.i.d. marked-tree law. -/
noncomputable def iidMarkedTreeLaw : Measure (MarkedTree OffspringMark) :=
  Measure.infinitePi (fun _ : TreeNode => μ)

instance : IsProbabilityMeasure (iidMarkedTreeLaw μ) := by
  unfold iidMarkedTreeLaw
  infer_instance

/-- Each fixed address has the prescribed offspring law. -/
theorem iidMarkedTree_marginal (u : TreeNode) :
    (iidMarkedTreeLaw μ).map (fun ω : MarkedTree OffspringMark => ω u) = μ := by
  simpa [iidMarkedTreeLaw] using
    (Measure.infinitePi_map_eval (fun _ : TreeNode => μ) u)

/-- All offspring marks are jointly independent; future reserve branches are
already present in this product and are never sampled retrospectively. -/
theorem iidMarkedTree_independent :
    iIndepFun (fun u (ω : MarkedTree OffspringMark) => ω u)
      (iidMarkedTreeLaw μ) := by
  unfold iidMarkedTreeLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : TreeNode => μ)
    (X := fun _ : TreeNode => id)
    (fun _ => measurable_id))

/-- Any injective reindexing of the pre-sampled offspring coordinates remains
jointly independent.  This is the reusable cross-generation input for spine
increments and reserve branches. -/
theorem iidMarkedTree_injective_coordinates_independent
    {ι : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (f : ι → TreeNode) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : MarkedTree OffspringMark) => ω (f i))
      (iidMarkedTreeLaw μ) := by
  exact (iidMarkedTree_independent μ).precomp hf

/-- Measurable functions of injectively reindexed marks remain independent.
This is the exact form used when turning offspring marks into increment
observables. -/
theorem iidMarkedTree_injective_coordinates_comp_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (f : ι → TreeNode) (hf : Function.Injective f)
    (g : ∀ i, OffspringMark → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (ω : MarkedTree OffspringMark) => g i (ω (f i)))
      (iidMarkedTreeLaw μ) := by
  exact (iidMarkedTree_injective_coordinates_independent μ f hf).comp
    (fun i => g i) hg

theorem iidMarkedTree_injective_displacements_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (f : ι → TreeNode) (hf : Function.Injective f) :
    iIndepFun
      (fun i (ω : MarkedTree OffspringMark) =>
        childDisplacement (ω (f i)) 0)
      (iidMarkedTreeLaw μ) := by
  apply iidMarkedTree_injective_coordinates_comp_independent μ f hf
    (fun _ ξ => childDisplacement ξ 0)
  intro i
  exact childDisplacement_measurable 0

theorem iidMarkedTree_injective_displacements_law
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k : ℕ} (f : Fin k → TreeNode)
    (hf : Function.Injective f) :
    (iidMarkedTreeLaw μ).map
        (fun ω i => childDisplacement (ω (f i)) 0) =
      Measure.infinitePi
        (fun _ : Fin k => μ.map (fun ξ => childDisplacement ξ 0)) := by
  have h := (iidMarkedTree_injective_displacements_independent μ f hf)
  have hmeas : ∀ i : Fin k, Measurable
      (fun ω : MarkedTree OffspringMark =>
        childDisplacement (ω (f i)) 0) := by
    intro i
    exact (childDisplacement_measurable 0).comp
      (measurable_pi_apply (f i))
  rw [h.map_fun_eq_infinitePi_map hmeas]
  apply congrArg Measure.infinitePi
  funext i
  calc
    Measure.map (fun ω : MarkedTree OffspringMark =>
        childDisplacement (ω (f i)) 0) (iidMarkedTreeLaw μ) =
      ((iidMarkedTreeLaw μ).map (fun ω => ω (f i))).map
        (fun ξ => childDisplacement ξ 0) := by
          rw [Measure.map_map]
          · rfl
          · exact childDisplacement_measurable 0
          · exact measurable_pi_apply (f i)
    _ = μ.map (fun ξ => childDisplacement ξ 0) := by
      rw [iidMarkedTree_marginal μ (f i)]

end ThesisSpeed
