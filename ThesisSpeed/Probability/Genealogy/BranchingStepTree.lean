import ThesisSpeed.Probability.Genealogy.Tree
import ThesisSpeed.Probability.Branching.Step
import Mathlib.Probability.Independence.InfinitePi

/-!
# Step fields and the trees they realize

`BranchingStepField α X` is the primitive field of branching steps indexed by
the addresses `TreeNode α`, with offspring labels in the same type `α`.
A slot may be absent, so potential nodes need not exist. The realized tree
(`branchingRealizedTree`), the accumulated marks
(`branchingStepAccumulatedMark`, `branchingStepAccumulatedMark?`) and the
marked tree (`branchingStepMarkedTree`) are all derived from such a field, so
no separate tree-valued wrapper type is introduced.
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

/-- The accumulated mark along the remaining path `p` while the walk is at the
address `v`. The current address is carried along explicitly, so no index
arithmetic (`take`, `getElem!`) is needed. -/
def branchingStepAccumulatedMarkFrom {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) : TreeNode α → TreeNode α → X
  | _, [] => 0
  | v, i :: p => branchingStepIncrement (ω v) i +
      branchingStepAccumulatedMarkFrom ω (v ++ [i]) p

/-- The total accumulated mark along a root path. Absent slots contribute
zero, so this is an algebraic extension; the partial version that records
absence is `branchingStepAccumulatedMark?`. The paper's sum over the prefixes
of `u` is the bridge lemma `branchingStepAccumulatedMark_eq_sum`. -/
def branchingStepAccumulatedMark {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (u : TreeNode α) : X :=
  branchingStepAccumulatedMarkFrom ω [] u

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

@[simp] theorem branchingStepAccumulatedMarkFrom_nil {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v : TreeNode α) :
    branchingStepAccumulatedMarkFrom ω v [] = 0 := rfl

theorem branchingStepAccumulatedMarkFrom_cons {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v : TreeNode α) (i : α) (p : TreeNode α) :
    branchingStepAccumulatedMarkFrom ω v (i :: p) =
      branchingStepIncrement (ω v) i +
        branchingStepAccumulatedMarkFrom ω (v ++ [i]) p := rfl

/-- The accumulator splits an appended path, moving the starting address by
the first part. -/
theorem branchingStepAccumulatedMarkFrom_append {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v p q : TreeNode α) :
    branchingStepAccumulatedMarkFrom ω v (p ++ q) =
      branchingStepAccumulatedMarkFrom ω v p +
        branchingStepAccumulatedMarkFrom ω (v ++ p) q := by
  induction p generalizing v with
  | nil => simp [branchingStepAccumulatedMarkFrom]
  | cons i p ih =>
      have hpath : v ++ (i :: p) = (v ++ [i]) ++ p := by simp
      rw [List.cons_append, branchingStepAccumulatedMarkFrom_cons,
        branchingStepAccumulatedMarkFrom_cons, ih (v := v ++ [i]), hpath, add_assoc]

/-- Re-basing the step field below a prefix `u` is the same as moving the
starting address by `u`. -/
theorem branchingStepAccumulatedMarkFrom_rebase {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (u v p : TreeNode α) :
    branchingStepAccumulatedMarkFrom (fun w => ω (u ++ w)) v p =
      branchingStepAccumulatedMarkFrom ω (u ++ v) p := by
  induction p generalizing v with
  | nil => rfl
  | cons i p ih =>
      have hpath : u ++ (v ++ [i]) = (u ++ v) ++ [i] := by simp
      rw [branchingStepAccumulatedMarkFrom_cons, branchingStepAccumulatedMarkFrom_cons,
        ih (v := v ++ [i]), hpath]

/-- The paper's defining formula, in the form that carries the starting
address. For `j < p.length` the option `p[j]?` is `some p_j`; the `getD 0`
guards the out-of-range indices. -/
theorem branchingStepAccumulatedMarkFrom_eq_sum {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v : TreeNode α) (p : TreeNode α) :
    branchingStepAccumulatedMarkFrom ω v p =
      ∑ j ∈ Finset.range p.length,
        (Option.map (branchingStepIncrement (ω (v ++ p.take j))) (p[j]?)).getD 0 := by
  induction p generalizing v with
  | nil => simp [branchingStepAccumulatedMarkFrom]
  | cons i p ih =>
      rw [branchingStepAccumulatedMarkFrom_cons, ih (v := v ++ [i]),
        List.length_cons, Finset.sum_range_succ']
      have hzero : (Option.map (branchingStepIncrement
            (ω (v ++ (i :: p).take 0))) ((i :: p)[0]?)).getD 0 =
          branchingStepIncrement (ω v) i := by simp
      have hshift : (∑ k ∈ Finset.range p.length,
            (Option.map (branchingStepIncrement
              (ω (v ++ (i :: p).take (k + 1)))) ((i :: p)[k + 1]?)).getD 0) =
          ∑ k ∈ Finset.range p.length,
            (Option.map (branchingStepIncrement (ω ((v ++ [i]) ++ p.take k)))
              (p[k]?)).getD 0 := by
        apply Finset.sum_congr rfl
        intro k _
        have hpath : v ++ (i :: p.take k) = (v ++ [i]) ++ p.take k := by simp
        rw [List.take_succ_cons, List.getElem?_cons_succ, hpath]
      rw [hshift, hzero]
      exact add_comm _ _

theorem branchingStepAccumulatedMark_nil {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) :
    branchingStepAccumulatedMark ω [] = 0 := rfl

theorem branchingStepAccumulatedMark_singleton {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (i : α) :
    branchingStepAccumulatedMark ω [i] = branchingStepIncrement (ω []) i := by
  simp [branchingStepAccumulatedMark, branchingStepAccumulatedMarkFrom]

theorem branchingStepAccumulatedMark_append_singleton {α : Type*} {X : Type*}
    [AddCommMonoid X]
    (ω : BranchingStepField α X) (u : TreeNode α) (i : α) :
    branchingStepAccumulatedMark ω (u ++ [i]) =
      branchingStepAccumulatedMark ω u + branchingStepIncrement (ω u) i := by
  simp [branchingStepAccumulatedMark, branchingStepAccumulatedMarkFrom_append,
    branchingStepAccumulatedMarkFrom]

theorem branchingStepAccumulatedMark_append_two {α : Type*} {X : Type*}
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

/-- The paper's sum over the prefixes of `u`. -/
theorem branchingStepAccumulatedMark_eq_sum {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (u : TreeNode α) :
    branchingStepAccumulatedMark ω u =
      ∑ j ∈ Finset.range u.length,
        (Option.map (branchingStepIncrement (ω (u.take j))) (u[j]?)).getD 0 := by
  simpa [branchingStepAccumulatedMark] using
    branchingStepAccumulatedMarkFrom_eq_sum ω [] u

/-- The same sum indexed by `Fin p.length`, in the form that carries the
starting address. Every index comes with its own bound, so the summand is the
slot at that index and no `getD` guard is needed. -/
theorem branchingStepAccumulatedMarkFrom_eq_sum_fin {α : Type*} {X : Type*}
    [AddCommMonoid X]
    (ω : BranchingStepField α X) (v p : TreeNode α) :
    branchingStepAccumulatedMarkFrom ω v p =
      ∑ j : Fin p.length, branchingStepIncrement (ω (v ++ p.take j)) (p[j]) := by
  induction p generalizing v with
  | nil => simp [branchingStepAccumulatedMarkFrom]
  | cons i p ih =>
      change branchingStepIncrement (ω v) i +
          branchingStepAccumulatedMarkFrom ω (v ++ [i]) p =
        ∑ j : Fin (p.length + 1),
          branchingStepIncrement (ω (v ++ (i :: p).take j)) ((i :: p)[j])
      rw [Fin.sum_univ_succ, ih (v := v ++ [i])]
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro k _
        congr 2
        simp

/-- The paper's sum over the prefixes, indexed by `Fin u.length` instead of
`Finset.range u.length`. -/
theorem branchingStepAccumulatedMark_eq_sum_fin {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (u : TreeNode α) :
    branchingStepAccumulatedMark ω u =
      ∑ j : Fin u.length, branchingStepIncrement (ω (u.take j)) (u[j]) := by
  simpa [branchingStepAccumulatedMark] using
    branchingStepAccumulatedMarkFrom_eq_sum_fin ω ([] : TreeNode α) u

theorem branchingStepAccumulatedMark_append {α : Type*} {X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (u v : TreeNode α) :
    branchingStepAccumulatedMark ω (u ++ v) =
      branchingStepAccumulatedMark ω u +
        branchingStepAccumulatedMark (fun w => ω (u ++ w)) v := by
  simp only [branchingStepAccumulatedMark]
  rw [branchingStepAccumulatedMarkFrom_append,
    branchingStepAccumulatedMarkFrom_rebase ω u [] v, List.append_nil]
  rfl

/-! ## The realized tree of a step field

The step field is the primitive object. A slot may be absent; the realized
tree below keeps exactly the addresses whose slots are present along the whole
root path. The accumulated mark is a derived quantity:
`branchingStepAccumulatedMark?` is the partial version that returns `none` when
some slot on the path is absent. -/

/-- Being realized along the remaining path `p` from the address `v`: every
child slot on the path is present, with the current address carried along. -/
def branchingStepPresentAlong {α X : Type*} (step : BranchingStepField α X) :
    TreeNode α → TreeNode α → Prop
  | _, [] => True
  | v, i :: p => branchingStepPresent (step v) i ∧
      branchingStepPresentAlong step (v ++ [i]) p

/-- A node is realized when every child slot on its root path is present. -/
def branchingRealizedNode {α X : Type*}
    (step : BranchingStepField α X) (u : TreeNode α) : Prop :=
  branchingStepPresentAlong step [] u

@[simp] theorem branchingStepPresentAlong_nil {α X : Type*} (step : BranchingStepField α X)
    (v : TreeNode α) : branchingStepPresentAlong step v [] := trivial

theorem branchingStepPresentAlong_cons {α X : Type*} (step : BranchingStepField α X)
    (v : TreeNode α) (i : α) (p : TreeNode α) :
    branchingStepPresentAlong step v (i :: p) ↔
      branchingStepPresent (step v) i ∧
        branchingStepPresentAlong step (v ++ [i]) p :=
  Iff.rfl

theorem branchingStepPresentAlong_append_singleton {α X : Type*}
    (step : BranchingStepField α X) :
    ∀ (v p : TreeNode α) (i : α),
      branchingStepPresentAlong step v (p ++ [i]) ↔
        branchingStepPresentAlong step v p ∧
          branchingStepPresent (step (v ++ p)) i
  | v, [], i => by simp [branchingStepPresentAlong]
  | v, j :: p, i => by
      have ih := branchingStepPresentAlong_append_singleton step (v ++ [j]) p i
      have hpath : v ++ (j :: p) = (v ++ [j]) ++ p := by simp
      simp only [List.cons_append, branchingStepPresentAlong_cons, hpath]
      rw [ih, and_assoc]

theorem branchingStepPresentAlong_append {α X : Type*}
    (step : BranchingStepField α X) :
    ∀ (v p q : TreeNode α),
      branchingStepPresentAlong step v (p ++ q) ↔
        branchingStepPresentAlong step v p ∧
          branchingStepPresentAlong step (v ++ p) q
  | v, [], q => by simp [branchingStepPresentAlong]
  | v, j :: p, q => by
      have ih := branchingStepPresentAlong_append step (v ++ [j]) p q
      have hpath : v ++ (j :: p) = (v ++ [j]) ++ p := by simp
      simp only [List.cons_append, branchingStepPresentAlong_cons, hpath]
      rw [ih, and_assoc]

theorem branchingStepPresentAlong_rebase {α X : Type*}
    (step : BranchingStepField α X) :
    ∀ (u v p : TreeNode α),
      branchingStepPresentAlong (fun w => step (u ++ w)) v p ↔
        branchingStepPresentAlong step (u ++ v) p
  | u, v, [] => by simp [branchingStepPresentAlong]
  | u, v, k :: p => by
      have ih := branchingStepPresentAlong_rebase step u (v ++ [k]) p
      have hpath : u ++ (v ++ [k]) = (u ++ v) ++ [k] := by simp
      simp only [branchingStepPresentAlong_cons]
      rw [ih, hpath]

theorem branchingRealizedNode_nil {α X : Type*} (step : BranchingStepField α X) :
    branchingRealizedNode step [] := trivial

theorem branchingRealizedNode_append_singleton_iff
    {α X : Type*} (step : BranchingStepField α X) (u : TreeNode α) (i : α) :
    branchingRealizedNode step (u ++ [i]) ↔
      branchingRealizedNode step u ∧
        branchingStepPresent (step u) i := by
  simpa [branchingRealizedNode] using
    branchingStepPresentAlong_append_singleton step [] u i

theorem branchingRealizedNode_append_iff
    {α X : Type*} (step : BranchingStepField α X) (u v : TreeNode α) :
    branchingRealizedNode step (u ++ v) ↔
      branchingRealizedNode step u ∧
        branchingRealizedNode (fun w => step (u ++ w)) v := by
  have h := branchingStepPresentAlong_append step [] u v
  have h' := (branchingStepPresentAlong_rebase step u [] v).symm
  simp only [branchingRealizedNode, List.nil_append, List.append_nil] at h h' ⊢
  rw [h]
  exact and_congr_right fun _ => h'

/-- Realization as a `Fin`-indexed conjunction: index `j` constrains the child
slot at depth `j` of the address. This is the `Fin` form of the paper's
`∀ j < |u|` statement, so no out-of-range guard is needed. -/
theorem branchingStepPresentAlong_iff_forall_fin {α X : Type*}
    (step : BranchingStepField α X) (v p : TreeNode α) :
    branchingStepPresentAlong step v p ↔
      ∀ j : Fin p.length, branchingStepPresent (step (v ++ p.take j)) (p[j]) := by
  induction p generalizing v with
  | nil =>
      constructor
      · intro _ j
        exact j.elim0
      · intro _
        trivial
  | cons i p ih =>
      change (branchingStepPresent (step v) i ∧
          branchingStepPresentAlong step (v ++ [i]) p) ↔
        ∀ j : Fin (p.length + 1),
          branchingStepPresent (step (v ++ (i :: p).take j)) ((i :: p)[j])
      rw [Fin.forall_fin_succ]
      refine and_congr ?_ ?_
      · simp
      · rw [ih (v := v ++ [i])]
        apply forall_congr'
        intro k
        simp

theorem branchingRealizedNode_iff_forall_fin {α X : Type*}
    (step : BranchingStepField α X) (u : TreeNode α) :
    branchingRealizedNode step u ↔
      ∀ j : Fin u.length, branchingStepPresent (step (u.take j)) (u[j]) := by
  simpa [branchingRealizedNode] using
    branchingStepPresentAlong_iff_forall_fin step ([] : TreeNode α) u

/-! ## The partial accumulated mark

`branchingStepAccumulatedMarkFrom?` is the same path recursion as
`branchingStepAccumulatedMarkFrom`, but it accumulates in `Option X`: as soon
as one slot on the path is absent it returns `none`. Being a direct recursion,
it needs neither `classical` nor a decision procedure for
`branchingRealizedNode`. -/

/-- The partial accumulated mark along the remaining path `p` from the address
`v`; `none` as soon as one slot on the path is absent. -/
def branchingStepAccumulatedMarkFrom? {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) : TreeNode α → TreeNode α → Option X
  | _, [] => some 0
  | v, i :: p =>
      (ω v i).bind fun x =>
        (branchingStepAccumulatedMarkFrom? ω (v ++ [i]) p).map fun y => x + y

/-- Accumulated mark from the root to `u`; `none` when a slot on the root path
is absent. -/
def branchingStepAccumulatedMark? {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) : Option X :=
  branchingStepAccumulatedMarkFrom? step [] u

@[simp] theorem branchingStepAccumulatedMarkFrom?_nil {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v : TreeNode α) :
    branchingStepAccumulatedMarkFrom? ω v [] = some 0 := rfl

theorem branchingStepAccumulatedMarkFrom?_cons {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v : TreeNode α) (i : α) (p : TreeNode α) :
    branchingStepAccumulatedMarkFrom? ω v (i :: p) =
      (ω v i).bind fun x =>
        (branchingStepAccumulatedMarkFrom? ω (v ++ [i]) p).map fun y => x + y := rfl

theorem branchingStepAccumulatedMarkFrom?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v p : TreeNode α) :
    branchingStepAccumulatedMarkFrom? ω v p = none ↔
      ¬ branchingStepPresentAlong ω v p := by
  induction p generalizing v with
  | nil => simp [branchingStepPresentAlong]
  | cons i p ih =>
      rw [branchingStepAccumulatedMarkFrom?_cons, branchingStepPresentAlong_cons]
      cases h : ω v i with
      | none => simp [h, branchingStepPresent]
      | some x =>
          have hp : branchingStepPresent (ω v) i := ⟨x, h⟩
          simp [hp, ih (v := v ++ [i]), Option.map_eq_none_iff]

/-- On a realized path the partial recursion returns the total accumulated
mark. -/
theorem branchingStepAccumulatedMarkFrom?_eq_some_of_present {α X : Type*}
    [AddCommMonoid X] (ω : BranchingStepField α X) :
    ∀ (v p : TreeNode α), branchingStepPresentAlong ω v p →
      branchingStepAccumulatedMarkFrom? ω v p =
        some (branchingStepAccumulatedMarkFrom ω v p)
  | v, [], _ => rfl
  | v, i :: p, h => by
      obtain ⟨x, hx⟩ := h.1
      have ih := branchingStepAccumulatedMarkFrom?_eq_some_of_present ω (v ++ [i]) p h.2
      rw [branchingStepAccumulatedMarkFrom?_cons, branchingStepAccumulatedMarkFrom_cons,
        branchingStepIncrement_some (ω v) i x hx, hx, ih]
      simp

/-- The three readings of the partial mark — it has a value, the path is
realized, and that value is the total accumulated mark — are one statement. -/
theorem branchingStepAccumulatedMarkFrom?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v p : TreeNode α) (x : X) :
    branchingStepAccumulatedMarkFrom? ω v p = some x ↔
      branchingStepPresentAlong ω v p ∧
        branchingStepAccumulatedMarkFrom ω v p = x := by
  constructor
  · intro h
    by_cases hp : branchingStepPresentAlong ω v p
    · have htot := branchingStepAccumulatedMarkFrom?_eq_some_of_present ω v p hp
      rw [htot] at h
      exact ⟨hp, Option.some.inj h⟩
    · have hnone := (branchingStepAccumulatedMarkFrom?_eq_none_iff ω v p).mpr hp
      rw [hnone] at h
      exact absurd h (by simp)
  · rintro ⟨hp, rfl⟩
    exact branchingStepAccumulatedMarkFrom?_eq_some_of_present ω v p hp

theorem branchingStepAccumulatedMarkFrom?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (ω : BranchingStepField α X) (v p : TreeNode α) :
    (branchingStepAccumulatedMarkFrom? ω v p).isSome ↔
      branchingStepPresentAlong ω v p := by
  cases h : branchingStepAccumulatedMarkFrom? ω v p with
  | none => simp [(branchingStepAccumulatedMarkFrom?_eq_none_iff ω v p).mp h]
  | some x =>
      have hp : branchingStepPresentAlong ω v p :=
        ((branchingStepAccumulatedMarkFrom?_eq_some_iff ω v p x).mp h).1
      simp [hp]

@[simp] theorem branchingStepAccumulatedMark?_nil {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) : branchingStepAccumulatedMark? step [] = some 0 := rfl

theorem branchingStepAccumulatedMark?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (x : X) :
    branchingStepAccumulatedMark? step u = some x ↔
      branchingRealizedNode step u ∧ branchingStepAccumulatedMark step u = x := by
  simpa [branchingStepAccumulatedMark?, branchingRealizedNode, branchingStepAccumulatedMark]
    using branchingStepAccumulatedMarkFrom?_eq_some_iff step [] u x

theorem branchingStepAccumulatedMark?_eq_some_of_realized {α X : Type*}
    [AddCommMonoid X] (step : BranchingStepField α X) {u : TreeNode α}
    (h : branchingRealizedNode step u) :
    branchingStepAccumulatedMark? step u = some (branchingStepAccumulatedMark step u) :=
  (branchingStepAccumulatedMark?_eq_some_iff step u _).mpr ⟨h, rfl⟩

theorem branchingStepAccumulatedMark?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) :
    branchingStepAccumulatedMark? step u = none ↔ ¬ branchingRealizedNode step u := by
  simpa [branchingStepAccumulatedMark?, branchingRealizedNode] using
    branchingStepAccumulatedMarkFrom?_eq_none_iff step [] u

theorem branchingStepAccumulatedMark?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) :
    (branchingStepAccumulatedMark? step u).isSome ↔ branchingRealizedNode step u := by
  simpa [branchingStepAccumulatedMark?, branchingRealizedNode] using
    branchingStepAccumulatedMarkFrom?_isSome_iff step [] u

/-- The partial mark in the paper's range-indexed sum form: it is `some x`
exactly when the address is realized and the accumulated increment equals `x`.
The `getD 0` guard absorbs the indices outside the range; realizability is
carried separately by the first conjunct. -/
theorem branchingStepAccumulatedMark?_eq_some_sum_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (x : X) :
    branchingStepAccumulatedMark? step u = some x ↔
      branchingRealizedNode step u ∧
        (∑ j ∈ Finset.range u.length,
          (Option.map (branchingStepIncrement (step (u.take j))) (u[j]?)).getD 0) = x := by
  rw [branchingStepAccumulatedMark?_eq_some_iff, branchingStepAccumulatedMark_eq_sum]

/-- The partial mark in the `Fin`-indexed sum form. -/
theorem branchingStepAccumulatedMark?_eq_some_sum_fin_iff {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (x : X) :
    branchingStepAccumulatedMark? step u = some x ↔
      (∀ j : Fin u.length, branchingStepPresent (step (u.take j)) (u[j])) ∧
        (∑ j : Fin u.length, branchingStepIncrement (step (u.take j)) (u[j])) = x := by
  rw [branchingStepAccumulatedMark?_eq_some_iff, branchingRealizedNode_iff_forall_fin,
    branchingStepAccumulatedMark_eq_sum_fin]

/-- Appending one step: the partial mark at `u ++ [i]` is `some` of the
incremented total exactly when `u` is realized and the slot at `i` is present.
This replaces the earlier statement that wrapped the total definition in an
`if`, which forced a `Classical.propDecidable` instance into the conclusion. -/
theorem branchingStepAccumulatedMark?_append_singleton
    {α X : Type*} [AddCommMonoid X]
    (step : BranchingStepField α X) (u : TreeNode α) (i : α) :
    branchingStepAccumulatedMark? step (u ++ [i]) =
        some (branchingStepAccumulatedMark step u + branchingStepIncrement (step u) i) ↔
      branchingRealizedNode step u ∧ branchingStepPresent (step u) i := by
  rw [branchingStepAccumulatedMark?_eq_some_iff, branchingRealizedNode_append_singleton_iff,
    branchingStepAccumulatedMark_append_singleton]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- The deterministic tree realized by an ordered step field. -/
def branchingRealizedTree {α X : Type*} [LT α] [LE X]
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

@[simp] theorem branchingRealizedTree_carrier {α X : Type*} [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) :
    (branchingRealizedTree step hordered).carrier =
      {u | branchingRealizedNode step u} := rfl

@[simp] theorem mem_branchingRealizedTree_iff {α X : Type*} [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) (u : TreeNode α) :
    u ∈ (branchingRealizedTree step hordered).carrier ↔
      branchingRealizedNode step u := Iff.rfl

/-- The marked tree of an ordered step field: the realized addresses carry
their accumulated marks. This is the bridge from the step field to the
tree-with-marks object; both the realized tree and the marks are derived from
the field. -/
def branchingStepMarkedTree {α X : Type*} [AddCommMonoid X] [LT α] [LE X]
    (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) : MarkedTree α X where
  tree := branchingRealizedTree step hordered
  mark := fun u _ => branchingStepAccumulatedMark step u

@[simp] theorem branchingStepMarkedTree_tree {α X : Type*} [AddCommMonoid X]
    [LT α] [LE X] (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u)) :
    (branchingStepMarkedTree step hordered).tree =
      branchingRealizedTree step hordered := rfl

@[simp] theorem branchingStepMarkedTree_mark {α X : Type*} [AddCommMonoid X]
    [LT α] [LE X] (step : BranchingStepField α X)
    (hordered : ∀ u, OrderedBranchingStep (step u))
    (u : TreeNode α) (hu : u ∈ (branchingRealizedTree step hordered).carrier) :
    (branchingStepMarkedTree step hordered).mark u hu =
      branchingStepAccumulatedMark step u := rfl

end ThesisSpeed
