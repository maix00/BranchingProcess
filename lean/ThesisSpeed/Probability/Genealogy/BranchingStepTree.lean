import ThesisSpeed.Probability.Genealogy.Tree
import ThesisSpeed.Probability.Branching.Step
import Mathlib.Probability.Independence.InfinitePi

/-!
# Step fields and the trees they realize

`BranchingStepField X` is the primitive node-indexed field of branching
steps. `BranchingStepTree? X` bundles such a field as a random object; a slot
may be absent, so potential nodes need not exist. The realized tree and the
accumulated marks are derived from the step field.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

abbrev BranchingStepField (X : Type*) :=
  TreeNode → BranchingStep ℕ X

abbrev RootIndexedBranchingStepField (Root : Type*) (X : Type*) :=
  Root → BranchingStepField X

abbrev FiniteRootBranchingStepField (m : ℕ) (X : Type*) :=
  RootIndexedBranchingStepField (Fin m) X

abbrev CountableRootBranchingStepField (X : Type*) :=
  RootIndexedBranchingStepField ℕ X

def RootIndexedBranchingStepField.reindex
    {Root NewRoot X : Type*} (f : NewRoot → Root)
    (step : RootIndexedBranchingStepField Root X) :
    RootIndexedBranchingStepField NewRoot X :=
  fun r => step (f r)

def RootIndexedBranchingStepField.first
    {X : Type*} (m : ℕ) (step : CountableRootBranchingStepField X) :
    FiniteRootBranchingStepField m X :=
  step.reindex Fin.val

def FiniteRootBranchingStepField.first
    {X : Type*} {m n : ℕ} (h : m ≤ n)
    (step : FiniteRootBranchingStepField n X) :
    FiniteRootBranchingStepField m X :=
  step.reindex (Fin.castLE h)

/-- The total accumulated mark along a root path. Absent slots contribute
zero, so this is an algebraic extension; the partial version that records
absence is `branchingStepAccumulatedMark?`. -/
def branchingStepAccumulatedMark {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u : TreeNode) : X :=
  ∑ j ∈ Finset.range u.length,
    branchingStepIncrement (ω (u.take j)) (u[j]!)

noncomputable def branchingStepFieldLaw {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) :
    Measure (TreeNode → BranchingStep ℕ X) :=
  Measure.infinitePi (fun _ : TreeNode => μ)

noncomputable def rootIndexedBranchingStepFieldLaw
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) :
    Measure (RootIndexedBranchingStepField Root X) :=
  Measure.infinitePi (fun _ : Root => branchingStepFieldLaw μ)

instance branchingStepFieldLaw.isProbabilityMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep ℕ X))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (branchingStepFieldLaw μ) := by
  unfold branchingStepFieldLaw
  infer_instance

instance rootIndexedBranchingStepFieldLaw.isProbabilityMeasure
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure
      (rootIndexedBranchingStepFieldLaw (Root := Root) μ) := by
  unfold rootIndexedBranchingStepFieldLaw
  infer_instance

theorem rootIndexedBranchingStepFieldLaw_reindex
    {Root NewRoot X : Type*} [Countable Root] [Countable NewRoot]
    [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (f : NewRoot → Root) (hf : Function.Injective f) :
    (rootIndexedBranchingStepFieldLaw (Root := Root) μ).map
        (RootIndexedBranchingStepField.reindex f) =
      rootIndexedBranchingStepFieldLaw (Root := NewRoot) μ := by
  unfold rootIndexedBranchingStepFieldLaw
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Root => branchingStepFieldLaw μ) (f := f) hf

theorem branchingStepFieldLaw_coordinate
    {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep ℕ X))
    [IsProbabilityMeasure μ] (u : TreeNode) :
    (branchingStepFieldLaw μ).map (fun ω => ω u) = μ := by
  unfold branchingStepFieldLaw
  exact Measure.infinitePi_map_eval (fun _ : TreeNode => μ) u

theorem branchingStepFieldLaw_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] :
    iIndepFun (fun u (ω : TreeNode → BranchingStep ℕ X) => ω u)
      (branchingStepFieldLaw μ) := by
  unfold branchingStepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : TreeNode => μ)
    (X := fun _ : TreeNode => id)
    (fun _ => measurable_id))

theorem branchingStepFieldLaw_injective_coordinates_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (f : ι → TreeNode) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : TreeNode → BranchingStep ℕ X) => ω (f i))
      (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_independent μ).precomp hf

theorem branchingStepFieldLaw_injective_coordinates_comp_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (f : ι → TreeNode) (hf : Function.Injective f)
    (g : ∀ i, BranchingStep ℕ X → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (ω : TreeNode → BranchingStep ℕ X) =>
      g i (ω (f i))) (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_injective_coordinates_independent μ f hf).comp
    (fun i => g i) hg

theorem branchingStepAccumulatedMark_nil {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) :
    branchingStepAccumulatedMark ω [] = 0 := by simp [branchingStepAccumulatedMark]

theorem branchingStepAccumulatedMark_singleton {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (i : ℕ) :
    branchingStepAccumulatedMark ω [i] = branchingStepIncrement (ω []) i := by
  simp [branchingStepAccumulatedMark]

theorem branchingStepAccumulatedMark_append_singleton {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u : TreeNode) (i : ℕ) :
    branchingStepAccumulatedMark ω (u ++ [i]) =
      branchingStepAccumulatedMark ω u + branchingStepIncrement (ω u) i := by
  simp only [branchingStepAccumulatedMark, List.length_append, List.length_singleton,
    Finset.sum_range_succ]
  have hlast : (u ++ [i]).take u.length = u := by simp
  have hslot : (u ++ [i])[u.length]! = i := by simp
  rw [hlast, hslot]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  simp [List.take_append_of_le_length (Nat.le_of_lt hjlt),
    List.getElem?_append_left hjlt]

theorem branchingStepAccumulatedMark_append_two {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u : TreeNode)
    (i j : ℕ) :
    branchingStepAccumulatedMark ω (u ++ [i, j]) =
      branchingStepAccumulatedMark ω u +
        branchingStepIncrement (ω u) i +
        branchingStepIncrement (ω (u ++ [i])) j := by
  rw [show u ++ [i, j] = (u ++ [i]) ++ [j] by simp]
  rw [branchingStepAccumulatedMark_append_singleton]
  rw [branchingStepAccumulatedMark_append_singleton]

theorem branchingStepAccumulatedMark_append {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u v : TreeNode) :
    branchingStepAccumulatedMark ω (u ++ v) =
      branchingStepAccumulatedMark ω u +
        branchingStepAccumulatedMark (fun w => ω (u ++ w)) v := by
  revert ω u
  induction v with
  | nil =>
      intro ω u
      simp [branchingStepAccumulatedMark]
  | cons i v ih =>
      intro ω u
      rw [List.append_cons]
      rw [ih (ω := ω) (u := u ++ [i])]
      rw [branchingStepAccumulatedMark_append_singleton]
      have h := ih (ω := fun w => ω (u ++ w)) (u := [i])
      have h' : branchingStepAccumulatedMark (fun w => ω (u ++ w)) (i :: v) =
          branchingStepIncrement (ω u) i +
            branchingStepAccumulatedMark (fun w => ω (u ++ [i] ++ w)) v := by
        simpa [branchingStepAccumulatedMark_singleton, List.append_assoc] using h
      rw [h']
      simp only [add_assoc]

/-! ## The realized tree of a step field

`BranchingStepTree?` is the random object encoded by a node-indexed field of
branching steps. A slot may be absent; the realized tree below keeps exactly
the addresses whose slots are present along the whole root path. The
accumulated mark is a derived quantity: `branchingStepAccumulatedMark?` is the
partial version that returns `none` when some slot on the path is absent. -/

structure BranchingStepTree? (X : Type*) where
  step : BranchingStepField X

namespace BranchingStepTree?

instance {X : Type*} : CoeFun (BranchingStepTree? X)
    (fun _ => BranchingStepField X) :=
  ⟨fun T => T.step⟩

variable {X : Type*}

@[simp] theorem step_eq (T : BranchingStepTree? X) : T.step = T.step := rfl

end BranchingStepTree?

/-- A node is realized when every child slot on its root path is present. -/
def branchingRealizedNode {X : Type*}
    (step : BranchingStepField X) (u : TreeNode) : Prop :=
  ∀ j ∈ Finset.range u.length,
    branchingStepPresent (step (u.take j)) (u[j]!)

theorem branchingRealizedNode_nil {X : Type*} (step : BranchingStepField X) :
    branchingRealizedNode step [] := by
  simp [branchingRealizedNode]

theorem branchingRealizedNode_append_singleton_iff
    {X : Type*} (step : BranchingStepField X) (u : TreeNode) (i : ℕ) :
    branchingRealizedNode step (u ++ [i]) ↔
      branchingRealizedNode step u ∧
        branchingStepPresent (step u) i := by
  constructor
  · intro h
    constructor
    · intro j hj
      have hjlt : j < u.length := Finset.mem_range.mp hj
      have hpath := h j (by
        apply Finset.mem_range.mpr
        simpa using Nat.lt_succ_of_lt hjlt)
      simpa [List.take_append_of_le_length (Nat.le_of_lt hjlt),
        List.getElem?_append_left hjlt] using hpath
    · have hlast := h u.length (by simp)
      simpa using hlast
  · rintro ⟨hu, hi⟩ j hj
    by_cases hju : j < u.length
    · have hpath := hu j (Finset.mem_range.mpr hju)
      simpa [List.take_append_of_le_length (Nat.le_of_lt hju),
        List.getElem?_append_left hju] using hpath
    · have hj_eq : j = u.length := by
        have hj_le : j ≤ u.length := by
          simpa [List.length_append] using hj
        omega
      subst j
      simpa using hi

theorem branchingRealizedNode_append_iff
    {X : Type*} (step : BranchingStepField X) (u v : TreeNode) :
    branchingRealizedNode step (u ++ v) ↔
      branchingRealizedNode step u ∧
        branchingRealizedNode (fun w => step (u ++ w)) v := by
  induction v using List.reverseRecOn with
  | nil => simp [branchingRealizedNode]
  | append_singleton v i ih =>
      rw [← List.append_assoc u v [i]]
      rw [branchingRealizedNode_append_singleton_iff]
      rw [ih]
      rw [branchingRealizedNode_append_singleton_iff]
      simp only [and_assoc]

/-- Accumulated mark from the root to `u`; `none` when a slot on the root
path is absent. -/
noncomputable def branchingStepAccumulatedMark? {X : Type*} [AddCommMonoid X]
    (step : BranchingStepField X) (u : TreeNode) : Option X :=
  by classical
     exact if h : branchingRealizedNode step u then
       some (branchingStepAccumulatedMark step u) else none

theorem branchingStepAccumulatedMark?_eq_some_iff
    {X : Type*} [AddCommMonoid X]
    (step : BranchingStepField X) (u : TreeNode) :
    branchingStepAccumulatedMark? step u =
        some (branchingStepAccumulatedMark step u) ↔
      branchingRealizedNode step u := by
  classical
  by_cases h : branchingRealizedNode step u <;>
    simp [branchingStepAccumulatedMark?, h]

theorem branchingStepAccumulatedMark?_eq_none_iff
    {X : Type*} [AddCommMonoid X]
    (step : BranchingStepField X) (u : TreeNode) :
    branchingStepAccumulatedMark? step u = none ↔
      ¬ branchingRealizedNode step u := by
  classical
  by_cases h : branchingRealizedNode step u <;>
    simp [branchingStepAccumulatedMark?, h]

theorem branchingStepAccumulatedMark?_isSome_iff
    {X : Type*} [AddCommMonoid X]
    (step : BranchingStepField X) (u : TreeNode) :
    (branchingStepAccumulatedMark? step u).isSome ↔
      branchingRealizedNode step u := by
  classical
  by_cases h : branchingRealizedNode step u <;>
    simp [branchingStepAccumulatedMark?, h]

@[simp] theorem branchingStepAccumulatedMark?_nil
    {X : Type*} [AddCommMonoid X] (step : BranchingStepField X) :
    branchingStepAccumulatedMark? step [] = some 0 := by
  classical
  simp [branchingStepAccumulatedMark?, branchingRealizedNode,
    branchingStepAccumulatedMark_nil]

theorem branchingStepAccumulatedMark?_append_singleton
    {X : Type*} [AddCommMonoid X]
    (step : BranchingStepField X) (u : TreeNode) (i : ℕ) :
    branchingStepAccumulatedMark? step (u ++ [i]) =
      @ite _ _ (Classical.propDecidable
        (branchingRealizedNode step u ∧ branchingStepPresent (step u) i))
        (some (branchingStepAccumulatedMark step u +
          branchingStepIncrement (step u) i)) none := by
  classical
  by_cases hu : branchingRealizedNode step u
  · by_cases hi : branchingStepPresent (step u) i
    · simp [branchingStepAccumulatedMark?,
        branchingRealizedNode_append_singleton_iff, hu, hi,
        branchingStepAccumulatedMark_append_singleton]
    · rw [branchingStepAccumulatedMark?]
      simp [branchingRealizedNode_append_singleton_iff, hu, hi,
        branchingStepAccumulatedMark?]
  · rw [branchingStepAccumulatedMark?]
    simp [branchingRealizedNode_append_singleton_iff, hu,
      branchingStepAccumulatedMark?]

/-- The deterministic tree realized by an ordered step field. -/
def branchingRealizedTree {X : Type*} [LE X] (step : BranchingStepField X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) : UlamHarrisTree where
  carrier := {u | branchingRealizedNode step u}
  root_mem := branchingRealizedNode_nil step
  prefix_closed := by
    intro u v huv
    change branchingRealizedNode step (u ++ v) at huv
    exact (branchingRealizedNode_append_iff step u v).1 huv |>.1
  sibling_closed := by
    intro u i j hj hij
    change branchingRealizedNode step (u ++ [j]) at hj
    rw [branchingRealizedNode_append_singleton_iff] at hj
    exact (branchingRealizedNode_append_singleton_iff step u i).2
      ⟨hj.1, branchingStep_present_of_later (step u) (hordered u).1 hij hj.2⟩

@[simp] theorem branchingRealizedTree_carrier {X : Type*} [LE X]
    (step : BranchingStepField X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) :
    (branchingRealizedTree step hordered).carrier =
      {u | branchingRealizedNode step u} := rfl

@[simp] theorem mem_branchingRealizedTree_iff {X : Type*} [LE X]
    (step : BranchingStepField X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) (u : TreeNode) :
    u ∈ (branchingRealizedTree step hordered).carrier ↔
      branchingRealizedNode step u := Iff.rfl

namespace BranchingStepTree?

variable {X : Type*} [AddCommMonoid X]

/-- The realized tree of an ordered step tree. -/
def realizedTree (T : BranchingStepTree? X) [LE X]
    (hordered : ∀ u, OrderedBranchingStep (T.step u)) : UlamHarrisTree :=
  branchingRealizedTree T.step hordered

/-- The total accumulated mark, extended by zero through absent slots. -/
def accumulatedMark (T : BranchingStepTree? X) (u : TreeNode) : X :=
  branchingStepAccumulatedMark T.step u

/-- The partial accumulated mark; `none` if a slot on the root path is absent. -/
noncomputable def accumulatedMark? (T : BranchingStepTree? X)
    (u : TreeNode) : Option X :=
  branchingStepAccumulatedMark? T.step u

/-- The realized marked tree of an ordered step tree: the realized addresses
carry their accumulated marks. This is the bridge from the step-field object
to the tree-with-marks object. -/
def markedTree (T : BranchingStepTree? X) [LE X]
    (hordered : ∀ u, OrderedBranchingStep (T.step u)) : MarkedTree ℕ X where
  tree := T.realizedTree hordered
  mark := fun u _ => branchingStepAccumulatedMark T.step u

@[simp] theorem markedTree_mark (T : BranchingStepTree? X) [LE X]
    (hordered : ∀ u, OrderedBranchingStep (T.step u))
    (u : TreeNode) (hu : u ∈ (T.realizedTree hordered).carrier) :
    (T.markedTree hordered).mark u hu =
      branchingStepAccumulatedMark T.step u := rfl

@[simp] theorem markedTree_tree (T : BranchingStepTree? X) [LE X]
    (hordered : ∀ u, OrderedBranchingStep (T.step u)) :
    (T.markedTree hordered).tree = T.realizedTree hordered := rfl

end BranchingStepTree?

end ThesisSpeed
