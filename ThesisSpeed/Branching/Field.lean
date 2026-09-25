import ThesisSpeed.Tree.Basic
import ThesisSpeed.Branching.Step

/-!
# Branching step fields

`BranchingStepField α X` is the primitive field of branching steps indexed by
the addresses `TreeNode α`, with child labels in the same type `α`. A slot
may be absent, so potential nodes need not exist. Everything else in this
directory — the realized tree, the accumulated marks, and the marked tree — is
derived from such a field, so no separate tree-valued wrapper type is
introduced.
-/

namespace ThesisSpeed

/-- The branching step field of the paper: one branching step at every
address. The address labels and the child labels are the same type `α`. -/
abbrev BranchingStepField (α : Type*) (X : Type*) :=
  TreeNode α → BranchingStep α X

end ThesisSpeed
