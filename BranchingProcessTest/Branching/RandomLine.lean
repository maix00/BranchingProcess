import Probability.Process.Tree.Line.Ancestral
import Probability.Process.Tree.Line.Information.Stopped
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.State

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

private theorem coin_not_measurable : ¬ MeasurableSet[⊥] ({true} : Set Bool) := by
  intro hm
  rcases MeasurableSpace.measurableSet_bot_iff.mp hm with he | he
  · have := Set.ext_iff.mp he true
    simp at this
  · have := Set.ext_iff.mp he false
    simp at this

-- The left node cannot decide using its own ancestors: it needs the right coin.
lemma not_ancestral_globalLine :
    ¬ (∀ u, MeasurableSet[ancestralPast ⊥ reproductionInformation u]
      {b | u ∈ globalLine b}) := by
  intro h
  have hm := h leftChild
  rw [left_ancestralPast] at hm
  have hevent : {b | leftChild ∈ globalLine b} = {true} := by
    ext b
    cases b <;> simp [globalLine, generation, leftChild]
  rw [hevent] at hm
  exact coin_not_measurable hm

-- A line with second-, third-, and fourth-generation members is a test line too.
def mixedLine : Set Node :=
  {((), [false, false]), ((), [false, true, false]), ((), [false, true, true, false])}

lemma mixedLine_isLine : RootIndexed.IsLine mixedLine := by
  simp [mixedLine, RootIndexed.IsLine, IsAntichain, Set.Pairwise, RootIndexed.IsAncestor]

lemma precedes_mixedLine : {b | RootIndexed.Line.Precedes (globalLine b) mixedLine} = {true} := by
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
    ∀ u, MeasurableSet[ancestralPast ⊥ reproductionInformation u]
      {b | u ∈ rightLine b} := by
  intro u
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

lemma optional_rightLine : IsOptionalLine (linePast ⊥ reproductionInformation) rightLine :=
  (optional_globalLine.toIsRandomLine.restrict _).isOptionalLine_of_ancestral_mem
    ⊥ reproductionInformation ancestral_rightLine

example : optional_globalLine.measurableSpace ≤
    optional_rightLine.measurableSpace := by
  apply optional_globalLine.measurableSpace_mono
  intro b v hv
  exact ⟨v, hv.1, RootIndexed.IsAncestor.refl v⟩

-- The life space is Bool here; the life coordinate is a map from the whole
-- sample domain Bool into that space. Its information is a native comap.
def lifeRecord (u : Node) (b : Bool) : Bool := if u = rightParent then b else false

lemma lifeRecord_information (u : Node) :
    MeasurableSpace.comap (lifeRecord u) inferInstance = reproductionInformation u := by
  by_cases hu : u = rightParent
  · have he : lifeRecord u = id := by funext b; simp [lifeRecord, hu]
    rw [he]
    simp only [MeasurableSpace.comap_id, reproductionInformation, ite_eq_left hu]
    exact top_unique (fun _ _ => MeasurableSet.of_discrete)
  · have he : lifeRecord u = fun _ => false := by funext b; simp [lifeRecord, hu]
    rw [he]
    simp [reproductionInformation, hu]

-- Reversibly changing the symbols of every record leaves the optional-line object unchanged.
def flipRecord : Bool ≃ᵐ Bool :=
  MeasurableEquiv.ofInvolutive Bool.not Bool.not_not (measurable_of_finite _)

example : IsOptionalLine (fun ℓ => linePast ⊥
    (fun u => MeasurableSpace.comap (flipRecord ∘ lifeRecord u) inferInstance) ℓ) globalLine := by
  apply optional_globalLine.mono
  intro ℓ _
  have heq := linePast_observation_equiv (⊥ : MeasurableSpace Bool)
    lifeRecord (fun _ => flipRecord) ℓ
  simp only [lifeRecord_information] at heq
  exact le_of_eq heq.symm

-- Erasing the record is only a projection: it need not preserve optionality.
lemma not_optional_after_erasing : ¬ IsOptionalLine (fun ℓ => linePast ⊥
    (fun _ : Node => MeasurableSpace.comap (fun _ : Bool => ()) inferInstance) ℓ) globalLine := by
  intro h
  have hm := h.measurableSet_precedes mixedLine mixedLine_isLine
  have hp : linePast (⊥ : MeasurableSpace Bool)
      (fun _ : Node => MeasurableSpace.comap (fun _ : Bool => ()) inferInstance) mixedLine = ⊥ := by
    simp [linePast]
  change MeasurableSet[linePast (⊥ : MeasurableSpace Bool)
    (fun _ : Node => MeasurableSpace.comap (fun _ : Bool => ()) inferInstance) mixedLine]
    {b | RootIndexed.Line.Precedes (globalLine b) mixedLine} at hm
  rw [hp] at hm
  rw [precedes_mixedLine] at hm
  exact coin_not_measurable hm

-- The actual field type stores a Step Bool Bool at each parent. No new life-space
-- wrapper is used: this is the existing branching field and existing state recursion.
def markedOffspring (b : Bool) :
    ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField Unit Bool Bool :=
  fun r u _ => some (lifeRecord (r, u) b)

def stateObservation (u : Node) (b : Bool) : Bool :=
  Combinatorics.Branching.stateAlong Bool.xor (markedOffspring b u.1) false [] u.2

lemma stateObservation_measurable (u : Node) :
    Measurable[ancestralPast ⊥ (fun v : Node => MeasurableSpace.comap
      (fun b => markedOffspring b v.1 v.2) inferInstance) u] (stateObservation u) :=
  ProbabilityTheory.BranchingRandomWalk.RootIndexed.state_measurable_ancestralPast
    Bool.xor (measurable_of_finite _) markedOffspring (fun _ _ => false) ⊥
      (fun _ => measurable_const) u.1 u.2

-- Including the current birth state does not expose that node's future reproduction.
example (b : Bool) : stateObservation rightParent b = false := by
  simp [stateObservation, rightParent, markedOffspring, lifeRecord,
    Combinatorics.Branching.stateAlong]

example (b : Bool) : stateObservation ((), [true, false]) b = b := by
  simp [stateObservation, markedOffspring, lifeRecord, rightParent,
    Combinatorics.Branching.stateAlong]

example (u : Node) : ancestralStateInformation ⊥ stateObservation u ≤
    ancestralPast ⊥ (fun v : Node => MeasurableSpace.comap
      (fun b => markedOffspring b v.1 v.2) inferInstance) u :=
  ancestralStateInformation_le_ancestralPast ⊥ _ stateObservation stateObservation_measurable u

#print axioms ProbabilityTheory.Tree.ancestralStateInformation_le_ancestralPast
#print axioms ProbabilityTheory.Tree.linePast_observation_equiv
#print axioms ProbabilityTheory.Tree.linePast_observation_map_le
#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.state_measurable_ancestralPast
#print axioms RandomLineExamples.not_optional_after_erasing
#print axioms ProbabilityTheory.Tree.linePast_generation_eq_generatedByCoordinates
#print axioms ProbabilityTheory.Tree.IsOptionalLine.measurableSpace_mono
#print axioms ProbabilityTheory.Tree.IsRandomLine.isOptionalLine_of_ancestral_mem
#print axioms ProbabilityTheory.Tree.isOptionalLine_ite_of_precedes
#print axioms RandomLineExamples.optional_globalLine
#print axioms RandomLineExamples.not_ancestral_globalLine
#print axioms RandomLineExamples.ancestral_rightLine

end RandomLineExamples
