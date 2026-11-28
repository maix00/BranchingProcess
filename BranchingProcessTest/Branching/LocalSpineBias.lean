import Probability.BranchingProcess.Spine.LocalBias.Path
import Probability.BranchingProcess.Spine.LocalBias.Normalization
import Probability.BranchingProcess.Spine.Tree.Density.PathPayoff

open MeasureTheory ProbabilityTheory Combinatorics.Branching
open scoped ENNReal

namespace LocalSpineBiasExamples

open BranchingProcess.Spine

def familyDependent : LocalBias Unit Bool where
  domain := Set.univ
  density := fun _ ξ i =>
    if (ξ true).isSome then (if i then 1 else 0) else (if i then 0 else 1)

-- Select the second child if it exists; otherwise select the first.
-- This changes the selection when a sibling is added, with both the parent
-- and the first child's state fixed. A parent/child-state ratio cannot do that.
def single : Step Bool Unit := fun i => if i then none else some ()
def double : Step Bool Unit := fun _ => some ()

example : familyDependent.density () single false = 1 ∧
    familyDependent.density () double false = 0 := by
  simp [familyDependent, single, double]

lemma admissible (μ : Measure (Step Bool Unit)) [IsProbabilityMeasure μ]
    (hfirst : ∀ᵐ ξ ∂μ, ξ false = some ()) :
    familyDependent.IsAdmissible (Kernel.const Unit μ) := by
  constructor
  · exact MeasurableSet.univ
  · intro i
    have hs : MeasurableSet {p : Unit × Step Bool Unit | (p.2 true).isSome} :=
      measurableSet_option_isSome.preimage ((measurable_pi_apply true).comp measurable_snd)
    cases i <;> exact measurable_const.ite hs measurable_const
  · intro s _
    have he : ∀ ξ : Step Bool Unit, ∑' i, familyDependent.density s ξ i = 1 := by
      intro ξ
      cases ht : ξ true <;> simp [familyDependent, tsum_fintype, ht]
    simp only [Kernel.const_apply, he]
    simp
  · intro s _
    rw [Kernel.const_apply]
    filter_upwards [hfirst] with ξ hξ
    intro i hi
    cases ht : ξ true with
    | none =>
      cases i with
      | false => exact ⟨(), hξ, Set.mem_univ _⟩
      | true => simp [familyDependent, ht] at hi
    | some t =>
      cases i with
      | false => simp [familyDependent, ht] at hi
      | true => exact ⟨t, ht, Set.mem_univ _⟩

example (μ : Measure (Step Bool Unit)) [IsProbabilityMeasure μ]
    (hfirst : ∀ᵐ ξ ∂μ, ξ false = some ())
    (F : List Bool → (List Bool → Option Unit) → ℝ≥0∞)
    (hF : ∀ u, Measurable[BranchingProcess.State.treeFiltration u.length] (F u)) :
    (∫⁻ t, ∑' u : List Bool,
      LocalBias.addressWeight familyDependent u.length u.get
        (BranchingProcess.State.treeHistory u.length t) * F u t
      ∂BranchingProcess.State.treeKernel (Kernel.const Unit μ) (some ())) =
    ∫⁻ t, ∑' u : List Bool, if (t u).any Sum.isRight = true then
      F u (fun v => (t v).map (Sum.elim id Subtype.val)) else 0
      ∂LocalBias.treeKernel (Kernel.const Unit μ) familyDependent (admissible μ hfirst)
        (some (Sum.inr ⟨(), Set.mem_univ _⟩)) :=
  LocalBias.lintegral_adaptedPayoff_eq _ _ (admissible μ hfirst)
    ⟨(), Set.mem_univ _⟩ F hF

-- A constant positive weight for deterministic binary reproduction is an
-- eigenfunction of eigenvalue 2, and is not harmonic. Local normalization
-- nevertheless supplies an admissible probability spine without a new proof.
noncomputable def binary : Kernel Unit (Step Bool Unit) :=
  Kernel.const _ (Measure.dirac double)

instance : IsMarkovKernel binary := by unfold binary; infer_instance

lemma binary_mean (s : Unit) :
    (∫⁻ ξ : Step Bool Unit, ∑' i, (ξ i).elim 0 (fun _ : Unit => (1 : ℝ≥0∞))
      ∂binary s) = 2 := by
  have hm : Measurable (fun ξ : Step Bool Unit =>
      ∑' i, (ξ i).elim 0 (fun _ : Unit => (1 : ℝ≥0∞))) :=
    Measurable.tsum fun i =>
      (measurable_option_elim 0 measurable_const).comp (measurable_pi_apply i)
  rw [binary, Kernel.const_apply]
  rw [lintegral_dirac' double hm]
  simp [tsum_fintype, double]

example : (LocalBias.normalizedWeight binary (fun _ => 1)).IsAdmissible binary := by
  apply LocalBias.normalizedWeight_isAdmissible binary measurable_const
  intro s _ _
  rw [binary_mean]
  norm_num

example : (LocalBias.normalizedWeight binary (fun _ => 1)).density () double false =
    (2 : ℝ≥0∞)⁻¹ := by
  change (1 : ℝ≥0∞) / (∫⁻ ξ, ∑' i, (ξ i).elim 0 (fun _ : Unit => (1 : ℝ≥0∞))
    ∂binary ()) = _
  rw [binary_mean, one_div]

end LocalSpineBiasExamples

#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.familyChildKernel_mass
#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.ae_familyChildKernel_eligible
#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.normalizedWeight_isAdmissible
#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.ae_treeKernel_unique_spine
#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.lintegral_treeKernel_fixedAddress
#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.lintegral_adaptedPayoff_eq
#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.lintegral_pathPayoff_eq
#print axioms ProbabilityTheory.BranchingProcess.Spine.lintegral_adaptedPayoff_eq
#print axioms ProbabilityTheory.BranchingProcess.Spine.lintegral_pathPayoff_eq
