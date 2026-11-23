import Probability.Process.Tree.Line.FirstEntrance
import Probability.Process.Tree.Line.Truncation
import Probability.Process.Tree.Line.PathHitting
import Probability.Process.Tree.Line.Pasting
import Probability.BranchingRandomWalk.Spine.StoppingLine.FirstEntrance

open MeasureTheory Combinatorics.UlamHarris ProbabilityTheory.Tree

namespace LineConstructionExamples

abbrev Node := RootIndexed.TreeNode Unit Bool

def generation (n : ℕ) : Set Node := {u | u.2.length = n}

example (n : ℕ) : RootIndexed.Line.firstEntrance (generation n) = generation n :=
  RootIndexed.Line.firstEntrance_eq (RootIndexed.isLine_generation n)

-- A target that is never reached gives an empty line, not a coverage assertion.
example : RootIndexed.Line.firstEntrance (∅ : Set Node) = ∅ :=
  RootIndexed.Line.firstEntrance_eq IsAntichain.empty

-- Even an empty target has a bounded cut, at the requested generation.
example (n : ℕ) : RootIndexed.Line.truncate (∅ : Set Node) n = generation n := by
  change RootIndexed.Line.firstEntrance (∅ ∪ generation n) = generation n
  rw [Set.empty_union]
  exact RootIndexed.Line.firstEntrance_eq (RootIndexed.isLine_generation n)

-- A finite-depth tree need not meet a cut; no nonexistent particle is asserted alive.
example : ({u : Node | u.2.length < 2} ∩ RootIndexed.Line.truncate ∅ 3) = ∅ := by
  have hcut : RootIndexed.Line.truncate (∅ : Set Node) 3 = generation 3 := by
    change RootIndexed.Line.firstEntrance (∅ ∪ generation 3) = generation 3
    rw [Set.empty_union]
    exact RootIndexed.Line.firstEntrance_eq (RootIndexed.isLine_generation 3)
  rw [hcut]
  ext u
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, generation, Set.mem_empty_iff_false,
    iff_false, not_and]
  omega

example (n m : ℕ) (h : n ≤ m) : RootIndexed.Line.Precedes
    (RootIndexed.Line.truncate (∅ : Set Node) n)
    (RootIndexed.Line.truncate ∅ m) := RootIndexed.Line.truncate_mono ∅ h

-- A genuinely random target, with initial information sufficient to decide it.
def randomTarget (b : Bool) : Set Node := generation (if b then 2 else 3)

lemma optional_firstEntrance :
    @IsOptionalLine Bool Unit Bool ⊤ (linePast ⊤ (fun _ => ⊥))
      (fun b => RootIndexed.Line.firstEntrance (randomTarget b)) := by
  apply isOptionalLine_firstEntrance (mΩ := ⊤) ⊤ (fun _ => ⊥) le_rfl (fun _ => bot_le)
  intro u
  have heq : ancestralPast (⊤ : MeasurableSpace Bool) (fun _ : Node => ⊥) u = ⊤ :=
    top_unique le_sup_left
  rw [heq]
  trivial

example (n : ℕ) :
    @IsOptionalLine Bool Unit Bool ⊤ (linePast ⊤ (fun _ => ⊥))
      (fun b => RootIndexed.Line.truncate (randomTarget b) n) := by
  apply isOptionalLine_truncate_of_ancestral_mem (mΩ := ⊤)
    ⊤ (fun _ => ⊥) le_rfl (fun _ => bot_le)
  intro u
  have heq : ancestralPast (⊤ : MeasurableSpace Bool) (fun _ : Node => ⊥) u = ⊤ :=
    top_unique le_sup_left
  rw [heq]
  trivial

example (b : Bool) (f : ℕ → Bool) (n : ℕ) :
    RootIndexed.Line.Precedes (RootIndexed.Line.firstEntrance (randomTarget b))
      {((), lineagePrefix f n)} ↔
    hittingAfter (fun k b => ((), lineagePrefix f k) ∈ randomTarget b) {True} 0 b ≤ n :=
  firstEntrance_precedes_ray_iff_hittingAfter_le randomTarget () f b n

open ProbabilityTheory.BranchingRandomWalk ProbabilityTheory.BranchingRandomWalk.Spine
  Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)

-- Entry at the initial state counts as success; never entering has mass zero.
example {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (h : HasBoundaryNormalization φ μ) (x : ℝ) :
    (∫⁻ ω, firstEntranceWeight φ Set.univ x ω ∂offspringFieldLaw μ) = 1 := by
  apply (lintegral_firstEntranceWeight_eq_one_iff φ μ h MeasurableSet.univ x).mpr
  exact Filter.Eventually.of_forall fun _ => ⟨0, Set.mem_univ _⟩

example {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (h : HasBoundaryNormalization φ μ) (x : ℝ) :
    (∫⁻ ω, firstEntranceWeight φ ∅ x ω ∂offspringFieldLaw μ) = 0 := by
  rw [lintegral_firstEntranceWeight_eq φ μ h MeasurableSet.empty x]
  simp

end LineConstructionExamples

#print axioms Combinatorics.UlamHarris.RootIndexed.Line.descendantClosure_firstEntrance
#print axioms Combinatorics.UlamHarris.RootIndexed.Line.firstEntrance_inter_of_ancestorClosed
#print axioms Combinatorics.UlamHarris.RootIndexed.Line.truncate_mono
#print axioms Combinatorics.UlamHarris.RootIndexed.Line.truncate_meetsEveryRay
#print axioms ProbabilityTheory.Tree.isOptionalLine_firstEntrance
#print axioms ProbabilityTheory.Tree.isOptionalLine_truncate_of_ancestral_mem
#print axioms ProbabilityTheory.Tree.firstEntrance_precedes_ray_iff_hittingAfter_le
#print axioms ProbabilityTheory.Tree.IsOptionalLine.ite_of_precedes
#print axioms ProbabilityTheory.Tree.IsOptionalLine.measurableSpace_const

#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.firstEntranceWeight_eq_tsum
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_firstEntranceWeight_eq
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_firstEntranceWeight_le_one
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_firstEntranceWeight_eq_one_iff
