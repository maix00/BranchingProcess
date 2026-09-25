import ThesisSpeed.Probability.Genealogy.Tree
import ThesisSpeed.Probability.Branching.Step
import Mathlib.Probability.Independence.InfinitePi

/-!
# Step fields and the trees they realize

`BranchingStepField α X` is the primitive field of branching steps indexed by
the addresses `TreeNode α`, with offspring labels in the same type `α`.
`BranchingStepTree? α X` bundles such a field as a random object; a slot may
be absent, so potential nodes need not exist. The realized tree and the
accumulated marks are derived from the step field.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-- The branching step field of the paper: one branching step at every
address. The address labels and the offspring labels are the same type `α`. -/
abbrev BranchingStepField (α : Type*) (X : Type*) :=
  TreeNode α → BranchingStep α X

abbrev RootIndexedBranchingStepField (Root : Type*) (X : Type*) :=
  Root → BranchingStepField ℕ X

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
def branchingStepAccumulatedMark {α : Type*} [Inhabited α] {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (u : TreeNode α) : X :=
  ∑ j ∈ Finset.range u.length,
    branchingStepIncrement (ω (u.take j)) (u[j]!)

noncomputable def branchingStepFieldLaw {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep α X)) :
    Measure (BranchingStepField α X) :=
  Measure.infinitePi (fun _ : TreeNode α => μ)

noncomputable def rootIndexedBranchingStepFieldLaw
    {Root X : Type*} [Countable Root] [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) :
    Measure (RootIndexedBranchingStepField Root X) :=
  Measure.infinitePi (fun _ : Root => branchingStepFieldLaw (α := ℕ) μ)

instance branchingStepFieldLaw.isProbabilityMeasure
    {α : Type*} {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep α X))
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
    (P := fun _ : Root => branchingStepFieldLaw (α := ℕ) μ) (f := f) hf

theorem branchingStepFieldLaw_coordinate
    {α : Type*} {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep α X))
    [IsProbabilityMeasure μ] (u : TreeNode α) :
    (branchingStepFieldLaw μ).map (fun ω => ω u) = μ := by
  unfold branchingStepFieldLaw
  exact Measure.infinitePi_map_eval (fun _ : TreeNode α => μ) u

theorem branchingStepFieldLaw_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep α X)) [IsProbabilityMeasure μ] :
    iIndepFun (fun u (ω : BranchingStepField α X) => ω u)
      (branchingStepFieldLaw μ) := by
  unfold branchingStepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : TreeNode α => μ)
    (X := fun _ : TreeNode α => id)
    (fun _ => measurable_id))

theorem branchingStepFieldLaw_injective_coordinates_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (f : ι → TreeNode α) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : BranchingStepField α X) => ω (f i))
      (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_independent μ).precomp hf

theorem branchingStepFieldLaw_injective_coordinates_comp_independent
    {α : Type*} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep α X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (f : ι → TreeNode α) (hf : Function.Injective f)
    (g : ∀ i, BranchingStep α X → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (ω : BranchingStepField α X) =>
      g i (ω (f i))) (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_injective_coordinates_independent μ f hf).comp
    (fun i => g i) hg

theorem branchingStepAccumulatedMark_nil {α : Type*} [Inhabited α] {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) :
    branchingStepAccumulatedMark ω [] = 0 := by simp [branchingStepAccumulatedMark]

theorem branchingStepAccumulatedMark_singleton {α : Type*} [Inhabited α] {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (i : α) :
    branchingStepAccumulatedMark ω [i] = branchingStepIncrement (ω []) i := by
  simp [branchingStepAccumulatedMark]

theorem branchingStepAccumulatedMark_append_singleton {α : Type*} [Inhabited α] {X : Type*}
    [AddCommMonoid X]
    (ω : BranchingStepField α X) (u : TreeNode α) (i : α) :
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

theorem branchingStepAccumulatedMark_append_two {α : Type*} [Inhabited α] {X : Type*}
    [AddCommMonoid X]
    (ω : BranchingStepField α X) (u : TreeNode α)
    (i j : α) :
    branchingStepAccumulatedMark ω (u ++ [i, j]) =
      branchingStepAccumulatedMark ω u +
        branchingStepIncrement (ω u) i +
        branchingStepIncrement (ω (u ++ [i])) j := by
  rw [show u ++ [i, j] = (u ++ [i]) ++ [j] by simp]
  rw [branchingStepAccumulatedMark_append_singleton]
  rw [branchingStepAccumulatedMark_append_singleton]

theorem branchingStepAccumulatedMark_append {α : Type*} [Inhabited α] {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (u v : TreeNode α) :
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

structure BranchingStepTree? (α : Type*) (X : Type*) where
  step : BranchingStepField α X

namespace BranchingStepTree?

instance {α X : Type*} : CoeFun (BranchingStepTree? α X)
    (fun _ => BranchingStepField α X) :=
  ⟨fun T => T.step⟩

variable {α : Type*} {X : Type*}

@[simp] theorem step_eq (T : BranchingStepTree? α X) : T.step = T.step := rfl

end BranchingStepTree?

/-- A node is realized when every child slot on its root path is present. -/
def branchingRealizedNode {α X : Type*} [Inhabited α]
    (step : BranchingStepField α X) (u : TreeNode α) : Prop :=
  ∀ j ∈ Finset.range u.length,
    branchingStepPresent (step (u.take j)) (u[j]!)

theorem branchingRealizedNode_nil {α X : Type*} [Inhabited α] (step : BranchingStepField α X) :
    branchingRealizedNode step [] := by
  simp [branchingRealizedNode]

theorem branchingRealizedNode_append_singleton_iff
    {α X : Type*} [Inhabited α] (step : BranchingStepField α X) (u : TreeNode α) (i : α) :
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
    {α X : Type*} [Inhabited α] (step : BranchingStepField α X) (u v : TreeNode α) :
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
noncomputable def branchingStepAccumulatedMark? {α X : Type*} [Inhabited α] [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) : Option X :=
  by classical
     exact if h : branchingRealizedNode step u then
       some (branchingStepAccumulatedMark step u) else none

theorem branchingStepAccumulatedMark?_eq_some_iff
    {α X : Type*} [Inhabited α] [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) :
    branchingStepAccumulatedMark? step u =
        some (branchingStepAccumulatedMark step u) ↔
      branchingRealizedNode step u := by
  classical
  by_cases h : branchingRealizedNode step u <;>
    simp [branchingStepAccumulatedMark?, h]

theorem branchingStepAccumulatedMark?_eq_none_iff
    {α X : Type*} [Inhabited α] [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) :
    branchingStepAccumulatedMark? step u = none ↔
      ¬ branchingRealizedNode step u := by
  classical
  by_cases h : branchingRealizedNode step u <;>
    simp [branchingStepAccumulatedMark?, h]

theorem branchingStepAccumulatedMark?_isSome_iff
    {α X : Type*} [Inhabited α] [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) :
    (branchingStepAccumulatedMark? step u).isSome ↔
      branchingRealizedNode step u := by
  classical
  by_cases h : branchingRealizedNode step u <;>
    simp [branchingStepAccumulatedMark?, h]

@[simp] theorem branchingStepAccumulatedMark?_nil
    {α X : Type*} [Inhabited α] [AddCommMonoid X] (step : BranchingStepField α X) :
    branchingStepAccumulatedMark? step [] = some 0 := by
  classical
  simp [branchingStepAccumulatedMark?, branchingRealizedNode,
    branchingStepAccumulatedMark_nil]

theorem branchingStepAccumulatedMark?_append_singleton
    {α X : Type*} [Inhabited α] [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (i : α) :
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
def branchingRealizedTree {α X : Type*} [Inhabited α] [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) : GenealogicalTree α where
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

@[simp] theorem branchingRealizedTree_carrier {α X : Type*} [Inhabited α] [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) :
    (branchingRealizedTree step hordered).carrier =
      {u | branchingRealizedNode step u} := rfl

@[simp] theorem mem_branchingRealizedTree_iff {α X : Type*} [Inhabited α] [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) (u : TreeNode α) :
    u ∈ (branchingRealizedTree step hordered).carrier ↔
      branchingRealizedNode step u := Iff.rfl

namespace BranchingStepTree?

variable {α : Type*} [Inhabited α] {X : Type*} [AddCommMonoid X]

/-- The realized tree of an ordered step tree. -/
def realizedTree (T : BranchingStepTree? α X) [LT α] [LE X]
    (hordered : ∀ u, OrderedBranchingStep (T.step u)) : GenealogicalTree α :=
  branchingRealizedTree T.step hordered

/-- The total accumulated mark, extended by zero through absent slots. -/
def accumulatedMark (T : BranchingStepTree? α X) (u : TreeNode α) : X :=
  branchingStepAccumulatedMark T.step u

/-- The partial accumulated mark; `none` if a slot on the root path is absent. -/
noncomputable def accumulatedMark? (T : BranchingStepTree? α X)
    (u : TreeNode α) : Option X :=
  branchingStepAccumulatedMark? T.step u

/-- The realized marked tree of an ordered step tree: the realized addresses
carry their accumulated marks. This is the bridge from the step-field object
to the tree-with-marks object. -/
def markedTree (T : BranchingStepTree? α X) [LT α] [LE X]
    (hordered : ∀ u, OrderedBranchingStep (T.step u)) : MarkedTree α X where
  tree := T.realizedTree hordered
  mark := fun u _ => branchingStepAccumulatedMark T.step u

@[simp] theorem markedTree_mark (T : BranchingStepTree? α X) [LT α] [LE X]
    (hordered : ∀ u, OrderedBranchingStep (T.step u))
    (u : TreeNode α) (hu : u ∈ (T.realizedTree hordered).carrier) :
    (T.markedTree hordered).mark u hu =
      branchingStepAccumulatedMark T.step u := rfl

@[simp] theorem markedTree_tree (T : BranchingStepTree? α X) [LT α] [LE X]
    (hordered : ∀ u, OrderedBranchingStep (T.step u)) :
    (T.markedTree hordered).tree = T.realizedTree hordered := rfl

end BranchingStepTree?

end ThesisSpeed
