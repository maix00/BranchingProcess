import ThesisSpeed.Probability.PointProcess.Encoding
import ThesisSpeed.Probability.Genealogy.Tree
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

end ThesisSpeed
