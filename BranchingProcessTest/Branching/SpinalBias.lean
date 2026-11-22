import Probability.BranchingProcess.Spine.Family.Conditional
import Probability.BranchingProcess.Spine.Tree.Ray
import Probability.BranchingProcess.Spine.Tree.FirstGeneration

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

-- Ordinary branches can later return to positive-weight states. They still
-- remain ordinary: there is exactly one distinguished node at every depth.
example : ∀ᵐ t ∂BranchingProcess.Spine.treeKernel offspring (h := weight)
      (by fun_prop) harmonic_eligible (some (Sum.inr ⟨false, by simp [weight]⟩)),
    ∃! f, Combinatorics.UlamHarris.IsRay (BranchingProcess.Spine.distinguishedNodes t) f ∧
      BranchingProcess.Spine.distinguishedNodes t =
        Set.range (Combinatorics.UlamHarris.lineagePrefix f) :=
  BranchingProcess.Spine.ae_treeKernel_unique_spine offspring (by fun_prop)
    harmonic_eligible ⟨false, by simp [weight]⟩

-- The density is a marginal of this same infinite tree, including zero-weight siblings.
example : (BranchingProcess.Spine.treeKernel offspring (h := weight)
      (by fun_prop) harmonic_eligible (some (Sum.inr ⟨false, by simp [weight]⟩))).map
      (fun t => Step.map (Sum.elim id Subtype.val) (fun j => t [j])) =
      (offspring false).withDensity
        (fun ξ => (∑' i, (ξ i).elim 0 weight) / weight false) :=
  BranchingProcess.Spine.treeKernel_firstFamily offspring (by fun_prop)
    harmonic_eligible ⟨false, by simp [weight]⟩

-- With an absent root, every node has absent children. No measurable equality
-- or countability hypothesis is imposed on the state space.
example {S : Type*} [MeasurableSpace S] (K : Kernel S (Step Bool S)) [IsMarkovKernel K]
    (hsupport : ∀ s, ∀ᵐ ξ ∂K s, ∀ i, ξ i = none) :
    ∀ᵐ t ∂BranchingProcess.State.treeKernel K none, ∀ u,
      ∀ i, t (u ++ [i]) = none := by
  apply BranchingProcess.State.ae_treeKernel_reproduction K none
    (fun _ ξ => ∀ i, ξ i = none)
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_option_none.preimage
      ((measurable_pi_apply i).comp measurable_snd)
  · intro o
    cases o with
    | none =>
      rw [Kernel.optionElim_none]
      exact (ae_dirac_iff (by
        rw [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i =>
          measurableSet_option_none.preimage (measurable_pi_apply i))).mpr (fun _ => rfl)
    | some a => exact hsupport a

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

#print axioms Combinatorics.UlamHarris.existsUnique_isRay_of_unique_child
#print axioms Combinatorics.UlamHarris.IsRay.eq_range_of_unique_child
#print axioms ProbabilityTheory.BranchingProcess.State.generationKernel_childFamily
#print axioms ProbabilityTheory.BranchingProcess.State.treeKernel_children
#print axioms ProbabilityTheory.BranchingProcess.State.ae_treeKernel_reproduction
#print axioms ProbabilityTheory.BranchingProcess.Spine.ae_treeKernel_unique_spine
#print axioms ProbabilityTheory.BranchingProcess.Spine.treeKernel_firstFamily
