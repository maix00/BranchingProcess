import Probability.BranchingProcess.Spine.Tree.BranchingProperty
import Probability.BranchingProcess.State.Descendants.Observed

open MeasureTheory ProbabilityTheory Combinatorics.Branching
open scoped ENNReal

namespace SpineDisintegrationExamples

-- The observable looks two generations below a sibling, not merely at the
-- root family. The sibling can be absent or ordinary with zero weight.
example (Q : Kernel Bool (Step Bool Bool)) [IsMarkovKernel Q]
    {h : Bool → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    (∫⁻ t, if (t [false]).any Sum.isRight = true then
      (if (t [true, false, true]).isSome then (1 : ℝ≥0∞) else 0) else 0
      ∂BranchingProcess.Spine.treeKernel Q hh harmonic (some (Sum.inr s))) =
    ∫⁻ ξ, ((ξ false).elim 0 h / h s) *
      ∫⁻ trees, (if (trees true [false, true]).isSome then (1 : ℝ≥0∞) else 0)
        ∂Measure.infinitePi (fun j => BranchingProcess.Spine.treeKernel Q hh harmonic
          (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) ξ false j)) ∂Q s := by
  apply BranchingProcess.Spine.lintegral_treeKernel_fixedChild_subtrees Q hh harmonic s false
    (g := fun p => if (p.2 true [false, true]).isSome then 1 else 0)
  have hm : Measurable (fun p : Step Bool Bool ×
      (Bool → List Bool → Option (Bool ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞})) =>
      (p.2 true [false, true]).isSome) :=
    (show Measurable (Option.isSome :
      Option (Bool ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) → Bool) from
        measurable_option_elim false measurable_const).comp (by fun_prop)
  exact measurable_const.ite (hm (MeasurableSet.singleton true)) measurable_const

end SpineDisintegrationExamples

#print axioms ProbabilityTheory.BranchingProcess.State.descendantTrees_jointLaw
#print axioms ProbabilityTheory.BranchingProcess.State.condExp_descendantTrees
#print axioms ProbabilityTheory.BranchingProcess.State.treeKernel_children_subtrees
#print axioms ProbabilityTheory.BranchingProcess.Spine.lintegral_treeKernel_fixedChild_subtrees
