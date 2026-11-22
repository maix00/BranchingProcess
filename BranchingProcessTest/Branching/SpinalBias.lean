import Probability.BranchingProcess.Spine.Family.Conditional
import Probability.BranchingProcess.Spine.Tree.Construction

open MeasureTheory ProbabilityTheory Combinatorics.Branching
open scoped ENNReal

namespace SpinalBiasExamples

-- A zero-weight side branch is allowed: positivity applies only to the spine.
def weight (s : Bool) : ℝ≥0∞ := if s then 0 else 1

def family : Step Bool Bool := fun i => some i

noncomputable def offspring : Kernel Bool (Step Bool Bool) :=
  Kernel.const _ (Measure.dirac family)

instance : IsMarkovKernel offspring := by unfold offspring; infer_instance

lemma harmonic_false : (∫⁻ ξ, ∑' i, (ξ i).elim 0 weight ∂offspring false) = weight false := by
  have hm : Measurable (fun ξ : Step Bool Bool => ∑' i, (ξ i).elim 0 weight) :=
    Measurable.tsum (fun i => (measurable_option_elim 0 (by fun_prop : Measurable weight)).comp
      (measurable_pi_apply i))
  rw [offspring, Kernel.const_apply, lintegral_dirac' family hm]
  simp [tsum_fintype, family, weight]

lemma harmonic_eligible (s : Bool) (hs : weight s ≠ 0) (_ : weight s ≠ ∞) :
    (∫⁻ ξ, ∑' i, (ξ i).elim 0 weight ∂offspring s) = weight s := by
  cases s
  · exact harmonic_false
  · exact False.elim (hs (by simp [weight]))

-- The distinguished family law is a probability measure even though h(true)=0.
example : IsProbabilityMeasure
    (BranchingProcess.Spine.biasedFamilyChild offspring weight false) :=
  BranchingProcess.Spine.biasedFamilyChild_isProbabilityMeasure offspring (by fun_prop)
    false (by simp [weight]) (by simp [weight]) harmonic_false

-- Chosen child exists and has finite positive weight, not merely a formal slot.
example : ∀ᵐ p ∂BranchingProcess.Spine.biasedFamilyChild offspring weight false,
    ∃ t, p.1 p.2 = some t ∧ weight t ≠ 0 ∧ weight t ≠ ∞ :=
  BranchingProcess.Spine.ae_biasedFamilyChild_eligible offspring (by fun_prop)
    false (by simp [weight]) (by simp [weight]) harmonic_false

-- Normal children outside the positive-weight domain are retained, not killed.
example : Step.distinguishChild (fun s => weight s ≠ 0 ∧ weight s ≠ ∞)
    family false true = some (Sum.inl true) := by
  rw [Step.distinguishChild_other _ _ false true (by decide)]
  rfl

-- The complete typed tree uses the existing state process and has a probability law.
example : IsMarkovKernel
    (BranchingProcess.Spine.treeKernel offspring (h := weight) (by fun_prop)
      harmonic_eligible) := inferInstance

-- Constant weight reduces the Doob transform to the original kernel.
example (K : Kernel Bool Bool) [IsSFiniteKernel K] :
    K.doobTransform (fun _ => 1) = K := Kernel.doobTransform_one K

end SpinalBiasExamples

#print axioms ProbabilityTheory.Kernel.lintegral_doobTransform
#print axioms ProbabilityTheory.Kernel.doobTransform_isProbabilityMeasure
#print axioms ProbabilityTheory.Kernel.ae_doobTransform_weight_ne_top
#print axioms ProbabilityTheory.BranchingProcess.lintegral_meanChildKernel
#print axioms ProbabilityTheory.BranchingProcess.Spine.biasedFamilyChild_isProbabilityMeasure
#print axioms ProbabilityTheory.BranchingProcess.Spine.spineChildKernel_eq_doobTransform
#print axioms ProbabilityTheory.BranchingProcess.Spine.lintegral_biasedFamilyChild_eq_conditional
#print axioms ProbabilityTheory.BranchingProcess.Spine.ae_biasedFamily_totalWeight
#print axioms ProbabilityTheory.BranchingProcess.Spine.ae_biasedFamilyChild_eligible
#print axioms ProbabilityTheory.BranchingProcess.Spine.reproductionKernel_distinguished_map
#print axioms ProbabilityTheory.BranchingProcess.Spine.treeKernel_root
