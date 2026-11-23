import Probability.BranchingProcess.Spine.Tree.Density.Conditional

open MeasureTheory ProbabilityTheory Combinatorics.Branching Finset
open scoped ENNReal

namespace SpineDensityExamples

def weight (s : Bool) : ℝ≥0∞ := if s then 0 else 1

def family : Step Bool Bool := fun i => some i

noncomputable def offspring : Kernel Bool (Step Bool Bool) :=
  Kernel.const _ (Measure.dirac family)

instance : IsMarkovKernel offspring := by unfold offspring; infer_instance

lemma harmonic (s : Bool) (hs : weight s ≠ 0) (_ : weight s ≠ ∞) :
    (∫⁻ ξ, ∑' i, (ξ i).elim 0 weight ∂offspring s) = weight s := by
  cases s
  · have hm : Measurable (fun ξ : Step Bool Bool => ∑' i, (ξ i).elim 0 weight) :=
      Measurable.tsum (fun i =>
        (measurable_option_elim 0 (by fun_prop : Measurable weight)).comp
          (measurable_pi_apply i))
    rw [offspring, Kernel.const_apply, lintegral_dirac' family hm]
    simp [family, weight, tsum_fintype]
  · exact False.elim (hs (by simp [weight]))

-- The terminal state can have positive weight after a zero-weight ancestor.
-- The ancestral indicator still makes its spinal weight zero.
example (x : Π k : Iic 2, (Unit × (Fin k.1 → Bool)) → Option Bool)
    (hparent : x ⟨1, by simp⟩ ((), fun _ : Fin 1 => true) = some true)
    (hterminal : x ⟨2, by simp⟩
      ((), Fin.snoc (fun _ : Fin 1 => true) false) = some false) :
    BranchingProcess.Spine.addressWeight weight 2
      (Fin.snoc (fun _ : Fin 1 => true) false) x = 0 ∧
      (x ⟨2, by simp⟩ ((), Fin.snoc (fun _ : Fin 1 => true) false)).elim 0 weight = 1 := by
  constructor
  · simp [BranchingProcess.Spine.addressWeight, Fin.init_snoc, hparent, weight]
  · simp [hterminal, weight]

-- The normalization is uniform in the depth, including n=0 and n>1.
example (n : ℕ) :
    (∫⁻ t, BranchingProcess.Spine.totalWeight weight n
      (fun _k p => t (List.ofFn p.2))
      ∂BranchingProcess.State.treeKernel offspring (some false)) = 1 :=
  BranchingProcess.Spine.lintegral_totalWeight offspring (by fun_prop) harmonic
    ⟨false, by simp [weight]⟩ n

-- Conditioning uses the entire untyped finite tree, including ordinary siblings.
example (n : ℕ) (z : Fin n → Bool) :
    let P := BranchingProcess.Spine.treeKernel offspring (h := weight)
      (by fun_prop) harmonic (some (Sum.inr ⟨false, by simp [weight]⟩))
    P⁻[(fun t => if (t (List.ofFn z)).any Sum.isRight = true then 1 else 0) |
      MeasurableSpace.comap (BranchingProcess.Spine.untypedHistory (h := weight) n)
        inferInstance] =ᵐ[P]
      fun t => BranchingProcess.Spine.addressWeight weight n z
        (BranchingProcess.Spine.untypedHistory n t) /
        BranchingProcess.Spine.totalWeight weight n
          (BranchingProcess.Spine.untypedHistory n t) :=
  BranchingProcess.Spine.condLExp_treeKernel_fixedAddress offspring (by fun_prop) harmonic
    ⟨false, by simp [weight]⟩ n z

end SpineDensityExamples

#print axioms ProbabilityTheory.BranchingProcess.Spine.addressWeight_eq_endpointRatio
#print axioms ProbabilityTheory.BranchingProcess.Spine.lintegral_treeKernel_fixedAddress
#print axioms ProbabilityTheory.BranchingProcess.Spine.treeKernel_finiteHistory
#print axioms ProbabilityTheory.BranchingProcess.Spine.treeKernel_fixedAddress_measure
#print axioms ProbabilityTheory.BranchingProcess.Spine.lintegral_totalWeight
#print axioms ProbabilityTheory.BranchingProcess.Spine.eq_treeKernel_marginal_of_finiteHistory
#print axioms ProbabilityTheory.BranchingProcess.Spine.condLExp_treeKernel_fixedAddress
#print axioms ProbabilityTheory.BranchingProcess.Spine.ae_treeKernel_totalWeight
