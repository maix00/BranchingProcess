import ThesisSpeed.Probability.Timing.Measurability
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Deterministic Ulam--Harris trees, marked trees, and pre-sampled fields

Three objects are kept apart.

* `TreeNode α` is the abstract address type `List α` of a rooted tree whose
  child labels live in `α`. It is not tied to `ℕ`.
* `GenealogicalTree α` is a deterministic rooted tree of `TreeNode α`
  addresses.
  It is a structure with tree axioms, not an arbitrary set of addresses.
* `MarkedTree α X` pairs one such realized tree with a mark on every realized
  node.
* `𝕍` is the Ulam--Harris vertex set `⋃ₙ ℕⁿ = TreeNode ℕ` of the paper.
* `Mark α M` is the mark function `TreeNode α → M` of the
  paper. It assigns a mark to *every* address, including reserve branches
  never used by the walk; `Mark ℕ M` is the mark function on `𝕍`.

The mark function is a separate object because the restart and reserve
arguments must evaluate marks at addresses that the walk never visits. It is
not a `M`: `M` is the value type of a single mark, while a mark function
is a function on addresses. The random mark function of the paper is a
`Mark`-valued random variable.

The generation filtration is defined on the pre-sampled field; a mark at
depth `d` is revealed when generation `d + 1` is observed.
-/

open MeasureTheory

namespace ThesisSpeed

variable {M : Type*} [MeasurableSpace M]

/-- Addresses of a rooted tree whose child labels live in `α`. This is the
abstract word type; `TreeNode ℕ` is the Ulam--Harris instance. -/
abbrev TreeNode (α : Type*) := List α

/-- The Ulam--Harris vertex set `𝕍 = ⋃ₙ ℕⁿ` of the paper. -/
abbrev 𝕍 := TreeNode ℕ

/-- A rooted tree of addresses. The carrier contains the root, is prefix
closed, and for ordered child labels contains every smaller sibling below a
present child. `Set (List α)` is only the underlying carrier of this
structure. -/
structure GenealogicalTree (α : Type*) [LT α] where
  carrier : Set (List α)
  root_mem : [] ∈ carrier
  prefix_closed : ∀ {u v : List α}, u ++ v ∈ carrier → u ∈ carrier
  sibling_closed : ∀ {u : List α} {i j : α},
    u ++ [j] ∈ carrier → i < j → u ++ [i] ∈ carrier

abbrev UlamHarrisTree := GenealogicalTree ℕ

@[simp] theorem GenealogicalTree.root_mem' {α : Type*} [LT α]
    (T : GenealogicalTree α) :
    [] ∈ T.carrier := T.root_mem

theorem GenealogicalTree.mem_prefix {α : Type*} [LT α] (T : GenealogicalTree α)
    {u v : List α} (h : u ++ v ∈ T.carrier) : u ∈ T.carrier :=
  T.prefix_closed h

/-- A realized tree together with a mark on each of its realized nodes. This
is the object meant when one says "marked tree"; it is not the full address
field. -/
structure MarkedTree (α X : Type*) [LT α] where
  tree : GenealogicalTree α
  mark : (u : List α) → u ∈ tree.carrier → X

namespace MarkedTree

variable {α X : Type*} [LT α]

/-- The mark at the root. -/
def rootMark (T : MarkedTree α X) : X := T.mark [] T.tree.root_mem

@[simp] theorem rootMark_eq (T : MarkedTree α X) :
    T.rootMark = T.mark [] T.tree.root_mem := rfl

end MarkedTree

/-- The mark function of the paper: a mark in `M` attached to every address
before any realized-tree restriction. The address type is arbitrary;
`Mark ℕ M` is the mark function on `𝕍`. The generation filtration is defined
directly on it, and a `MarkedTree` is what remains after keeping only the
realized nodes.

The name `Mark` is the object (a function on addresses), not a single mark:
a single mark is a term of the value type `M`. -/
abbrev Mark (α : Type*) (M : Type*) := TreeNode α → M

/-- The strict mark function: a mark is supplied only where the address is
realized, and `none` where it is not. This is the option-valued companion of
`Mark`, in the same `?` convention as `BranchingStepTree?` and
`branchingStepAccumulatedMark?`. -/
abbrev Mark? (α : Type*) (M : Type*) := TreeNode α → Option M

namespace MarkedTree

variable {α X : Type*} [LT α]

/-- The strict mark function of a marked tree: a realized address carries its
mark, every other address is undefined. This is how a `MarkedTree` is regarded
as a strict mark function on the whole address space. -/
noncomputable def markFunction? (T : MarkedTree α X) : Mark? α X :=
  by
    classical
    exact fun u => if h : u ∈ T.tree.carrier then some (T.mark u h) else none

@[simp] theorem markFunction?_apply_mem (T : MarkedTree α X) {u : TreeNode α}
    (h : u ∈ T.tree.carrier) : T.markFunction? u = some (T.mark u h) := by
  classical
  simp [markFunction?, h]

@[simp] theorem markFunction?_apply_notMem (T : MarkedTree α X) {u : TreeNode α}
    (h : u ∉ T.tree.carrier) : T.markFunction? u = none := by
  classical
  simp [markFunction?, h]

end MarkedTree

variable {α : Type*}

/-- Node addresses carry the discrete σ-algebra. -/
instance instMeasurableSpaceTreeNode (α : Type*) : MeasurableSpace (TreeNode α) := ⊤

/-- Information revealed by generation `n`: all marks at addresses of
depth strictly below `n`. -/
@[instance_reducible] def generationSpace (n : ℕ) :
    MeasurableSpace (Mark α M) :=
  MeasurableSpace.generateFrom
    {s | ∃ u : TreeNode α, u.length < n ∧
      ∃ t : Set M, MeasurableSet t ∧
        s = {ω : Mark α M | ω u ∈ t}}

/-- Before the root reproduces, no offspring mark is revealed. -/
theorem generationSpace_zero :
    generationSpace (α := α) (M := M) 0 = ⊥ := by
  unfold generationSpace
  have hgen :
      {s : Set (Mark α M) | ∃ u : TreeNode α, u.length < 0 ∧
        ∃ t : Set M, MeasurableSet t ∧
          s = {ω : Mark α M | ω u ∈ t}} = ∅ := by
    ext s
    simp
  rw [hgen, MeasurableSpace.generateFrom_empty]

/-- The generation information forms a filtration of the full product space. -/
def generationFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (Mark α M)) where
  seq := generationSpace
  mono' := by
    intro i j hij
    apply MeasurableSpace.generateFrom_mono
    rintro s ⟨u, hu, t, ht, rfl⟩
    exact ⟨u, lt_of_lt_of_le hu hij, t, ht, rfl⟩
  le' := by
    intro n
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨u, hu, t, ht, rfl⟩
    exact (measurable_pi_apply u) ht

/-- A node's mark is observable from the next generation onward. -/
theorem mark_measurable_of_depth_lt (u : TreeNode α) (n : ℕ)
    (hu : u.length < n) :
    Measurable[generationFiltration (M := M) n]
      (fun ω : Mark α M => ω u) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom ⟨u, hu, t, ht, rfl⟩

theorem mark_measurable_next (u : TreeNode α) :
    Measurable[generationFiltration (M := M) (u.length + 1)]
      (fun ω : Mark α M => ω u) :=
  mark_measurable_of_depth_lt u _ (Nat.lt_succ_self _)

/-- Only marks of parents in generation `n` are supplied to a generation
update. All deeper marks are hidden behind a dummy value. -/
def frontierMarks [Inhabited M] (n : ℕ)
    (ω : Mark α M) : Mark α M :=
  fun u => if u.length = n then ω u else default

/-- The entire current frontier, regarded as a product-valued observation, is
measurable when generation `n + 1` has been exposed. -/
theorem frontierMarks_measurable [Inhabited M] (n : ℕ) :
    Measurable[generationFiltration (α := α) (M := M) (n + 1)]
      (frontierMarks (α := α) (M := M) n) := by
  apply (@measurable_pi_iff (Mark α M) (TreeNode α) (fun _ => M)
    (generationFiltration (α := α) (M := M) (n + 1))
    (fun _ => inferInstance) (frontierMarks (α := α) (M := M) n)).2
  intro u
  by_cases hu : u.length = n
  · simpa [frontierMarks, hu] using
      (mark_measurable_of_depth_lt u (n + 1)
        (by rw [hu]; exact Nat.lt_succ_self n))
  · simp [frontierMarks, hu]

/-- A population state updated measurably from the current frontier is adapted.
This includes retained genealogical identities, not only their count. -/
theorem frontier_causal_state_adapted {State : Type*}
    [MeasurableSpace State] [Inhabited M]
    (state : ℕ → Mark α M → State)
    (step : State × Mark α M → State)
    (hstep : Measurable step)
    (hzero : Measurable[generationFiltration (M := M) 0] (state 0))
    (hrec : ∀ n ω, state (n + 1) ω =
      step (state n ω, frontierMarks n ω)) :
    ∀ n, Measurable[generationFiltration (M := M) n] (state n) :=
  causal_recursion_adapted (generationFiltration (M := M))
    state (frontierMarks (M := M)) step hstep hzero
    frontierMarks_measurable hrec

/-- A node selected using generation-`n` information has an observable mark,
provided its address lies among nodes whose marks have already been revealed.
This is the random-index measurability step used for reserve lineages. -/
theorem selected_mark_measurable [Countable α] (n : ℕ)
    (chosen : Mark α M → TreeNode α)
    (hchosen : Measurable[generationFiltration (M := M) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length < n) :
    Measurable[generationFiltration (M := M) n]
      (fun ω : Mark α M => ω (chosen ω)) := by
  intro t ht
  have hset :
      {ω : Mark α M | ω (chosen ω) ∈ t} =
        ⋃ u : TreeNode α,
          {ω : Mark α M | chosen ω = u} ∩
            {ω : Mark α M | ω u ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hmark⟩
      simpa [hu] using hmark
  change MeasurableSet[generationFiltration (M := M) n]
    {ω : Mark α M | ω (chosen ω) ∈ t}
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length < n
  · exact (hchosen (measurableSet_singleton u)).inter
      ((mark_measurable_of_depth_lt u n hu) ht)
  · have hempty : {ω : Mark α M | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

/-- An unconditionally pre-defined lineage that extends one generation at a
time from its own currently revealed mark is adapted. The premise about
length rules out a retrospectively chosen ancestor. -/
theorem causal_lineage_adapted [Countable α]
    (path : ℕ → Mark α M → TreeNode α)
    (step : TreeNode α × M → TreeNode α)
    (hstep : Measurable step)
    (hroot : Measurable[generationFiltration (M := M) 0] (path 0))
    (hdepth : ∀ n ω, (path n ω).length = n)
    (hrec : ∀ n ω, path (n + 1) ω =
      step (path n ω, ω (path n ω))) :
    ∀ n, Measurable[generationFiltration (M := M) n] (path n) := by
  intro n
  induction n with
  | zero => exact hroot
  | succ n ih =>
      have hold : Measurable[generationFiltration (M := M) (n + 1)]
          (path n) :=
        ih.mono (generationFiltration (M := M) |>.mono (Nat.le_succ n)) le_rfl
      have hmark : Measurable[generationFiltration (M := M) (n + 1)]
          (fun ω : Mark α M => ω (path n ω)) :=
        selected_mark_measurable (n + 1) (path n) hold
          (fun ω => by rw [hdepth n ω]; exact Nat.lt_succ_self n)
      have hpair : Measurable[generationFiltration (M := M) (n + 1)]
          (fun ω : Mark α M => (path n ω, ω (path n ω))) :=
        hold.prodMk hmark
      convert hstep.comp hpair using 1
      funext ω
      exact hrec n ω

/-- The split is declared when the offspring mark at the parent has been
revealed. Generation zero cannot declare a split. -/
def splitDeclaration (path : ℕ → Mark α M → TreeNode α)
    (splitMark : Set M) : ℕ → Set (Mark α M)
  | 0 => ∅
  | n + 1 => {ω | ω (path n ω) ∈ splitMark}

/-- The first observable split generation is a stopping time for the actual
pre-sampled-tree generation filtration. -/
theorem first_split_generation_isStoppingTime [Countable α]
    (path : ℕ → Mark α M → TreeNode α)
    (hpath : ∀ n, Measurable[generationFiltration (M := M) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n)
    (splitMark : Set M) (hsplit : MeasurableSet splitMark) :
    IsStoppingTime (generationFiltration (M := M))
      (firstDeclaredSuccess (splitDeclaration path splitMark)) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  cases n with
  | zero =>
      change MeasurableSet[generationFiltration (M := M) 0]
        (∅ : Set (Mark α M))
      exact (generationSpace (M := M) 0).measurableSet_empty
  | succ n =>
      have hold : Measurable[generationFiltration (M := M) (n + 1)]
          (path n) :=
        (hpath n).mono
          (generationFiltration (M := M) |>.mono (Nat.le_succ n)) le_rfl
      exact (selected_mark_measurable (n + 1) (path n) hold
        (fun ω => by rw [hdepth n ω]; exact Nat.lt_succ_self n)) hsplit

end ThesisSpeed
