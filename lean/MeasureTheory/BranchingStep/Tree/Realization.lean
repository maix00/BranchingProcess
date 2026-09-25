import MeasureTheory.BranchingStep.Field

/-!
# Which nodes a step field realizes

A slot of a branching step may be absent, so a step field is not itself a tree.
`presentAlong ω v p` says that every child slot on the remaining
path `p` is present, carrying the current address `v` along; the root case
`realizedNode step u` is the realizability predicate of the address
`u`. The `Fin` form is the paper's `∀ j < |u|` statement with no out-of-range
guard. Realized nodes are marked in `Tree/Realized.lean`.
-/

namespace MeasureTheory

namespace BranchingStep

open MeasureTheory.UlamHarris



/-- Being realized along the remaining path `p` from the address `v`: every
child slot on the path is present, with the current address carried along. -/
def presentAlong {α X : Type*} (step : StepField α X) :
    TreeNode α → TreeNode α → Prop
  | _, [] => True
  | v, i :: p => present (step v) i ∧
      presentAlong step (v ++ [i]) p

/-- A node is realized when every child slot on its root path is present. -/
def realizedNode {α X : Type*}
    (step : StepField α X) (u : TreeNode α) : Prop :=
  presentAlong step [] u

@[simp] theorem presentAlong_nil {α X : Type*} (step : StepField α X)
    (v : TreeNode α) : presentAlong step v [] := trivial

theorem presentAlong_cons {α X : Type*} (step : StepField α X)
    (v : TreeNode α) (i : α) (p : TreeNode α) :
    presentAlong step v (i :: p) ↔
      present (step v) i ∧
        presentAlong step (v ++ [i]) p :=
  Iff.rfl

theorem presentAlong_append_singleton {α X : Type*}
    (step : StepField α X) :
    ∀ (v p : TreeNode α) (i : α),
      presentAlong step v (p ++ [i]) ↔
        presentAlong step v p ∧
          present (step (v ++ p)) i
  | v, [], i => by simp [presentAlong]
  | v, j :: p, i => by
      have ih := presentAlong_append_singleton step (v ++ [j]) p i
      have hpath : v ++ (j :: p) = (v ++ [j]) ++ p := by simp
      simp only [List.cons_append, presentAlong_cons, hpath]
      rw [ih, and_assoc]

theorem presentAlong_append {α X : Type*}
    (step : StepField α X) :
    ∀ (v p q : TreeNode α),
      presentAlong step v (p ++ q) ↔
        presentAlong step v p ∧
          presentAlong step (v ++ p) q
  | v, [], q => by simp [presentAlong]
  | v, j :: p, q => by
      have ih := presentAlong_append step (v ++ [j]) p q
      have hpath : v ++ (j :: p) = (v ++ [j]) ++ p := by simp
      simp only [List.cons_append, presentAlong_cons, hpath]
      rw [ih, and_assoc]

theorem presentAlong_rebase {α X : Type*}
    (step : StepField α X) :
    ∀ (u v p : TreeNode α),
      presentAlong (fun w => step (u ++ w)) v p ↔
        presentAlong step (u ++ v) p
  | u, v, [] => by simp [presentAlong]
  | u, v, k :: p => by
      have ih := presentAlong_rebase step u (v ++ [k]) p
      have hpath : u ++ (v ++ [k]) = (u ++ v) ++ [k] := by simp
      simp only [presentAlong_cons]
      rw [ih, hpath]

theorem realizedNode_nil {α X : Type*} (step : StepField α X) :
    realizedNode step [] := trivial

theorem realizedNode_append_singleton_iff
    {α X : Type*} (step : StepField α X) (u : TreeNode α) (i : α) :
    realizedNode step (u ++ [i]) ↔
      realizedNode step u ∧
        present (step u) i := by
  simpa [realizedNode] using
    presentAlong_append_singleton step [] u i

theorem realizedNode_append_iff
    {α X : Type*} (step : StepField α X) (u v : TreeNode α) :
    realizedNode step (u ++ v) ↔
      realizedNode step u ∧
        realizedNode (fun w => step (u ++ w)) v := by
  have h := presentAlong_append step [] u v
  have h' := (presentAlong_rebase step u [] v).symm
  simp only [realizedNode, List.nil_append, List.append_nil] at h h' ⊢
  rw [h]
  exact and_congr_right fun _ => h'

/-- Realization as a `Fin`-indexed conjunction: index `j` constrains the child
slot at depth `j` of the address. This is the `Fin` form of the paper's
`∀ j < |u|` statement, so no out-of-range guard is needed. -/
theorem presentAlong_iff_forall_fin {α X : Type*}
    (step : StepField α X) (v p : TreeNode α) :
    presentAlong step v p ↔
      ∀ j : Fin p.length, present (step (v ++ p.take j)) (p[j]) := by
  induction p generalizing v with
  | nil =>
      constructor
      · intro _ j
        exact j.elim0
      · intro _
        trivial
  | cons i p ih =>
      change (present (step v) i ∧
          presentAlong step (v ++ [i]) p) ↔
        ∀ j : Fin (p.length + 1),
          present (step (v ++ (i :: p).take j)) ((i :: p)[j])
      rw [Fin.forall_fin_succ]
      refine and_congr ?_ ?_
      · simp
      · rw [ih (v := v ++ [i])]
        apply forall_congr'
        intro k
        simp

theorem realizedNode_iff_forall_fin {α X : Type*}
    (step : StepField α X) (u : TreeNode α) :
    realizedNode step u ↔
      ∀ j : Fin u.length, present (step (u.take j)) (u[j]) := by
  simpa [realizedNode] using
    presentAlong_iff_forall_fin step ([] : TreeNode α) u

end BranchingStep

end MeasureTheory
