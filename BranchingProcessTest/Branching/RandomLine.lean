import Probability.Process.Tree.Line.Ancestral
import Probability.Process.Tree.Line.Information.Stopped

open MeasureTheory Combinatorics.UlamHarris ProbabilityTheory.Tree

namespace RandomLineExamples

-- false and true are child indices 1 and 2 in the discussion.
abbrev Node := RootIndexed.TreeNode Unit Bool

def generation (n : ℕ) : Set Node := {u | u.2.length = n}

def rightParent : Node := ((), [true])
def leftChild : Node := ((), [false, false])

-- The only nonconstant observation is the right parent's fair-coin outcome.
-- The measurability distinction itself requires no choice of probability law.
@[instance_reducible] def reproductionInformation (u : Node) : MeasurableSpace Bool :=
  if u = rightParent then ⊤ else ⊥

def globalLine (b : Bool) : Set Node :=
  if b = true then generation 2 else generation 3

lemma optional_globalLine :
    IsOptionalLine (linePast ⊥ reproductionInformation) globalLine := by
  have hab : RootIndexed.Line.Precedes (generation 2) (generation 3) := by
    intro v hv
    refine ⟨(v.1, v.2.take 2), ?_, rfl, List.take_prefix _ _⟩
    change (v.2.take 2).length = 2
    simp [List.length_take, show v.2.length = 3 from hv]
  have hA : MeasurableSet ({b | b = true} : Set Bool) := MeasurableSet.singleton true
  have hAa : MeasurableSet[linePast ⊥ reproductionInformation (generation 2)]
      ({b | b = true} : Set Bool) := by
    have hright : rightParent ∉ RootIndexed.Line.descendantClosure (generation 2) := by
      rintro ⟨u, hu, hanc⟩
      have hlen := hanc.2.length_le
      change u.2.length = 2 at hu
      change u.2.length ≤ 1 at hlen
      omega
    have htop : (⊤ : MeasurableSpace Bool) ≤
        linePast ⊥ reproductionInformation (generation 2) := by
      simpa [reproductionInformation] using
        coordinate_le_linePast ⊥ reproductionInformation hright
    exact htop _ trivial
  have h := isOptionalLine_ite_of_precedes
    (linePast ⊥ reproductionInformation)
    (fun _ _ h => linePast_mono ⊥ reproductionInformation h)
    (RootIndexed.isLine_generation 2) (RootIndexed.isLine_generation 3) hab hA hAa
  convert h using 1
  funext b
  by_cases hb : b = true <;> simp [globalLine, generation, hb]

lemma left_ancestralPast : ancestralPast ⊥ reproductionInformation leftChild = ⊥ := by
  apply le_antisymm _ bot_le
  refine sup_le le_rfl (iSup_le fun u => iSup_le fun hu => ?_)
  by_cases heq : u = rightParent
  · subst u
    exact False.elim ((by simp [RootIndexed.IsAncestor, rightParent, leftChild] :
      ¬ RootIndexed.IsAncestor rightParent leftChild) hu.1)
  · simp [reproductionInformation, heq]

-- At the right node, birth-time and post-reproduction information differ.
example : ancestralPast ⊥ reproductionInformation rightParent = ⊥ := by
  apply le_antisymm _ bot_le
  refine sup_le le_rfl (iSup_le fun u => iSup_le fun hu => ?_)
  by_cases heq : u = rightParent
  · exact False.elim (hu.2 heq)
  · simp [reproductionInformation, heq]

example : ancestralHistory ⊥ reproductionInformation rightParent = ⊤ := by
  apply le_antisymm le_top
  simpa [reproductionInformation] using
    coordinate_le_ancestralHistory ⊥ reproductionInformation
      (RootIndexed.IsAncestor.refl rightParent)

-- The left node cannot decide using its own ancestors: it needs the right coin.
lemma not_ancestral_globalLine :
    ¬ IsAncestralStoppingLine (ancestralPast ⊥ reproductionInformation) globalLine := by
  intro h
  have hm := h.measurableSet_mem leftChild
  rw [left_ancestralPast] at hm
  have hevent : {b | leftChild ∈ globalLine b} = {true} := by
    ext b
    cases b <;> simp [globalLine, generation, leftChild]
  rw [hevent] at hm
  rcases MeasurableSpace.measurableSet_bot_iff.mp hm with he | he
  · have := Set.ext_iff.mp he true
    simp at this
  · have := Set.ext_iff.mp he false
    simp at this

-- A line with second-, third-, and fourth-generation members is a test line too.
def mixedLine : Set Node :=
  {((), [false, false]), ((), [false, true, false]), ((), [false, true, true, false])}

example : RootIndexed.IsLine mixedLine := by
  simp [mixedLine, RootIndexed.IsLine, IsAntichain, Set.Pairwise, RootIndexed.IsAncestor]

example : {b | RootIndexed.Line.Precedes (globalLine b) mixedLine} = {true} := by
  ext b
  cases b with
  | false =>
      simp only [globalLine, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
        Set.mem_singleton_iff, Bool.false_eq_true, iff_false]
      intro h
      obtain ⟨u, hu, hanc⟩ := h leftChild (by simp [leftChild, mixedLine])
      have hlen := hanc.2.length_le
      change u.2.length = 3 at hu
      change u.2.length ≤ 2 at hlen
      omega
  | true =>
      simp only [globalLine, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_singleton_iff,
        iff_true]
      intro v hv
      simp only [mixedLine, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨((), [false, false]), rfl, rfl, List.prefix_rfl⟩
      · exact ⟨((), [false, true]), rfl, rfl, [false], rfl⟩
      · exact ⟨((), [false, true]), rfl, rfl, [true, false], rfl⟩

-- A cut on the left leaves the complete right history in its past.
example : linePast ⊥ reproductionInformation {((), [false])} = ⊤ := by
  apply le_antisymm le_top
  have hright : rightParent ∉ RootIndexed.Line.descendantClosure {((), [false])} := by
    rintro ⟨u, hu, hanc⟩
    obtain rfl := Set.mem_singleton_iff.mp hu
    exact (by simp [RootIndexed.IsAncestor, rightParent] :
      ¬ RootIndexed.IsAncestor ((), [false]) rightParent) hanc
  simpa [reproductionInformation] using
    coordinate_le_linePast ⊥ reproductionInformation hright

-- Retaining only the right subtree gives a genuinely ancestral stopping rule.
def rightLine (b : Bool) : Set Node :=
  globalLine b ∩ {u | RootIndexed.IsAncestor rightParent u}

lemma ancestral_rightLine :
    IsAncestralStoppingLine (ancestralPast ⊥ reproductionInformation) rightLine := by
  refine ⟨optional_globalLine.toIsRandomLine.restrict _, fun u => ?_⟩
  by_cases hanc : RootIndexed.IsAncestor rightParent u
  · by_cases heq : rightParent = u
    · subst u
      have hevent : {b | rightParent ∈ rightLine b} = ∅ := by
        ext b
        cases b <;> simp [globalLine, generation, rightParent, rightLine]
      rw [hevent]
      exact @MeasurableSet.empty Bool (ancestralPast ⊥ reproductionInformation rightParent)
    · have htop : (⊤ : MeasurableSpace Bool) ≤
          ancestralPast ⊥ reproductionInformation u := by
        simpa [reproductionInformation] using
          coordinate_le_ancestralPast ⊥ reproductionInformation hanc heq
      exact htop _ trivial
  · have hevent : {b | u ∈ rightLine b} = ∅ := by
      ext b
      simp [rightLine, hanc]
    rw [hevent]
    exact @MeasurableSet.empty Bool (ancestralPast ⊥ reproductionInformation u)

example : IsOptionalLine (linePast ⊥ reproductionInformation) rightLine :=
  ancestral_rightLine.isOptionalLine_linePast ⊥ reproductionInformation

example : optional_globalLine.measurableSpace ≤
    (ancestral_rightLine.isOptionalLine_linePast ⊥ reproductionInformation).measurableSpace := by
  apply optional_globalLine.measurableSpace_mono
  intro b v hv
  exact ⟨v, hv.1, RootIndexed.IsAncestor.refl v⟩

#print axioms ProbabilityTheory.Tree.linePast_generation_eq_generatedByCoordinates
#print axioms ProbabilityTheory.Tree.IsOptionalLine.measurableSpace_mono
#print axioms ProbabilityTheory.Tree.IsAncestralStoppingLine.isOptionalLine_linePast
#print axioms ProbabilityTheory.Tree.isOptionalLine_ite_of_precedes
#print axioms RandomLineExamples.optional_globalLine
#print axioms RandomLineExamples.not_ancestral_globalLine
#print axioms RandomLineExamples.ancestral_rightLine

end RandomLineExamples
