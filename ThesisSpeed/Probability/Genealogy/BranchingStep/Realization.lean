import ThesisSpeed.Probability.Genealogy.BranchingStep.Field

/-!
# Which nodes a step field realizes

A slot of a branching step may be absent, so a step field is not itself a tree.
`branchingStepPresentAlong ω v p` says that every child slot on the remaining
path `p` is present, carrying the current address `v` along; the root case
`branchingRealizedNode step u` is the realizability predicate of the address
`u`. The `Fin` form is the paper's `∀ j < |u|` statement with no out-of-range
guard. Realized nodes are marked in `RealizedTree.lean`.
-/

namespace ThesisSpeed

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

end ThesisSpeed
