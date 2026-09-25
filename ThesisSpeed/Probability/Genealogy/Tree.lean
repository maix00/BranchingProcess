import ThesisSpeed.Probability.Timing.Measurability
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Deterministic Ulam--Harris trees, marked trees, and pre-sampled fields

Three objects are kept apart.

* `GenealogicalTree α` is a deterministic rooted tree of `List α` addresses.
  It is a structure with tree axioms, not an arbitrary set of addresses.
* `MarkedTree α X` pairs one such realized tree with a mark on every realized
  node.
* `PreSampledField Mark` is the full address field `List ℕ → Mark` used to
  pre-sample marks at *all* addresses, including reserve branches never used
  by the walk.

The generation filtration is defined on the pre-sampled field; a mark at
depth `d` is revealed when generation `d + 1` is observed.
-/

open MeasureTheory

namespace ThesisSpeed

variable {Mark : Type*} [MeasurableSpace Mark]

abbrev TreeNode := List ℕ

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

/-- Marks attached to every address before any realized-tree restriction.
This is the pre-sampled field on which the generation filtration lives. -/
abbrev PreSampledField (Mark : Type*) := TreeNode → Mark

/-- Node addresses are countable and carry the discrete σ-algebra. -/
instance : MeasurableSpace TreeNode := ⊤

/-- Information revealed by generation `n`: all marks at addresses of
depth strictly below `n`. -/
@[instance_reducible] def generationSpace (n : ℕ) :
    MeasurableSpace (PreSampledField Mark) :=
  MeasurableSpace.generateFrom
    {s | ∃ u : TreeNode, u.length < n ∧
      ∃ t : Set Mark, MeasurableSet t ∧
        s = {ω : PreSampledField Mark | ω u ∈ t}}

/-- Before the root reproduces, no offspring mark is revealed. -/
theorem generationSpace_zero :
    generationSpace (Mark := Mark) 0 = ⊥ := by
  unfold generationSpace
  have hgen :
      {s : Set (PreSampledField Mark) | ∃ u : TreeNode, u.length < 0 ∧
        ∃ t : Set Mark, MeasurableSet t ∧
          s = {ω : PreSampledField Mark | ω u ∈ t}} = ∅ := by
    ext s
    simp
  rw [hgen, MeasurableSpace.generateFrom_empty]

/-- The generation information forms a filtration of the full product space. -/
def generationFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (PreSampledField Mark)) where
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
theorem mark_measurable_of_depth_lt (u : TreeNode) (n : ℕ)
    (hu : u.length < n) :
    Measurable[generationFiltration (Mark := Mark) n]
      (fun ω : PreSampledField Mark => ω u) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom ⟨u, hu, t, ht, rfl⟩

theorem mark_measurable_next (u : TreeNode) :
    Measurable[generationFiltration (Mark := Mark) (u.length + 1)]
      (fun ω : PreSampledField Mark => ω u) :=
  mark_measurable_of_depth_lt u _ (Nat.lt_succ_self _)

/-- Only marks of parents in generation `n` are supplied to a generation
update. All deeper marks are hidden behind a dummy value. -/
def frontierMarks [Inhabited Mark] (n : ℕ)
    (ω : PreSampledField Mark) : PreSampledField Mark :=
  fun u => if u.length = n then ω u else default

/-- The entire current frontier, regarded as a product-valued observation, is
measurable when generation `n + 1` has been exposed. -/
theorem frontierMarks_measurable [Inhabited Mark] (n : ℕ) :
    Measurable[generationFiltration (Mark := Mark) (n + 1)]
      (frontierMarks (Mark := Mark) n) := by
  apply (@measurable_pi_iff (PreSampledField Mark) TreeNode (fun _ => Mark)
    (generationFiltration (Mark := Mark) (n + 1))
    (fun _ => inferInstance) (frontierMarks (Mark := Mark) n)).2
  intro u
  by_cases hu : u.length = n
  · simpa [frontierMarks, hu] using
      (mark_measurable_of_depth_lt u (n + 1)
        (by rw [hu]; exact Nat.lt_succ_self n))
  · simp [frontierMarks, hu]

/-- A population state updated measurably from the current frontier is adapted.
This includes retained genealogical identities, not only their count. -/
theorem frontier_causal_state_adapted {State : Type*}
    [MeasurableSpace State] [Inhabited Mark]
    (state : ℕ → PreSampledField Mark → State)
    (step : State × PreSampledField Mark → State)
    (hstep : Measurable step)
    (hzero : Measurable[generationFiltration (Mark := Mark) 0] (state 0))
    (hrec : ∀ n ω, state (n + 1) ω =
      step (state n ω, frontierMarks n ω)) :
    ∀ n, Measurable[generationFiltration (Mark := Mark) n] (state n) :=
  causal_recursion_adapted (generationFiltration (Mark := Mark))
    state (frontierMarks (Mark := Mark)) step hstep hzero
    frontierMarks_measurable hrec

/-- A node selected using generation-`n` information has an observable mark,
provided its address lies among nodes whose marks have already been revealed.
This is the random-index measurability step used for reserve lineages. -/
theorem selected_mark_measurable (n : ℕ)
    (chosen : PreSampledField Mark → TreeNode)
    (hchosen : Measurable[generationFiltration (Mark := Mark) n] chosen)
    (hdepth : ∀ ω, (chosen ω).length < n) :
    Measurable[generationFiltration (Mark := Mark) n]
      (fun ω : PreSampledField Mark => ω (chosen ω)) := by
  intro t ht
  have hset :
      {ω : PreSampledField Mark | ω (chosen ω) ∈ t} =
        ⋃ u : TreeNode,
          {ω : PreSampledField Mark | chosen ω = u} ∩
            {ω : PreSampledField Mark | ω u ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hmark⟩
      simpa [hu] using hmark
  change MeasurableSet[generationFiltration (Mark := Mark) n]
    {ω : PreSampledField Mark | ω (chosen ω) ∈ t}
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length < n
  · exact (hchosen (measurableSet_singleton u)).inter
      ((mark_measurable_of_depth_lt u n hu) ht)
  · have hempty : {ω : PreSampledField Mark | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

/-- An unconditionally pre-defined lineage that extends one generation at a
time from its own currently revealed mark is adapted. The premise about
length rules out a retrospectively chosen ancestor. -/
theorem causal_lineage_adapted
    (path : ℕ → PreSampledField Mark → TreeNode)
    (step : TreeNode × Mark → TreeNode)
    (hstep : Measurable step)
    (hroot : Measurable[generationFiltration (Mark := Mark) 0] (path 0))
    (hdepth : ∀ n ω, (path n ω).length = n)
    (hrec : ∀ n ω, path (n + 1) ω =
      step (path n ω, ω (path n ω))) :
    ∀ n, Measurable[generationFiltration (Mark := Mark) n] (path n) := by
  intro n
  induction n with
  | zero => exact hroot
  | succ n ih =>
      have hold : Measurable[generationFiltration (Mark := Mark) (n + 1)]
          (path n) :=
        ih.mono (generationFiltration (Mark := Mark) |>.mono (Nat.le_succ n)) le_rfl
      have hmark : Measurable[generationFiltration (Mark := Mark) (n + 1)]
          (fun ω : PreSampledField Mark => ω (path n ω)) :=
        selected_mark_measurable (n + 1) (path n) hold
          (fun ω => by rw [hdepth n ω]; exact Nat.lt_succ_self n)
      have hpair : Measurable[generationFiltration (Mark := Mark) (n + 1)]
          (fun ω : PreSampledField Mark => (path n ω, ω (path n ω))) :=
        hold.prodMk hmark
      convert hstep.comp hpair using 1
      funext ω
      exact hrec n ω

/-- The split is declared when the offspring mark at the parent has been
revealed. Generation zero cannot declare a split. -/
def splitDeclaration (path : ℕ → PreSampledField Mark → TreeNode)
    (splitMark : Set Mark) : ℕ → Set (PreSampledField Mark)
  | 0 => ∅
  | n + 1 => {ω | ω (path n ω) ∈ splitMark}

/-- The first observable split generation is a stopping time for the actual
pre-sampled-tree generation filtration. -/
theorem first_split_generation_isStoppingTime
    (path : ℕ → PreSampledField Mark → TreeNode)
    (hpath : ∀ n, Measurable[generationFiltration (Mark := Mark) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n)
    (splitMark : Set Mark) (hsplit : MeasurableSet splitMark) :
    IsStoppingTime (generationFiltration (Mark := Mark))
      (firstDeclaredSuccess (splitDeclaration path splitMark)) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  cases n with
  | zero =>
      change MeasurableSet[generationFiltration (Mark := Mark) 0]
        (∅ : Set (PreSampledField Mark))
      exact (generationSpace (Mark := Mark) 0).measurableSet_empty
  | succ n =>
      have hold : Measurable[generationFiltration (Mark := Mark) (n + 1)]
          (path n) :=
        (hpath n).mono
          (generationFiltration (Mark := Mark) |>.mono (Nat.le_succ n)) le_rfl
      exact (selected_mark_measurable (n + 1) (path n) hold
        (fun ω => by rw [hdepth n ω]; exact Nat.lt_succ_self n)) hsplit

end ThesisSpeed
