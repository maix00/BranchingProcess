import ThesisSpeed.Probability.Genealogy.BranchingStep.Field
import Mathlib.Algebra.BigOperators.Fin

/-!
# Accumulated marks along a path

`branchingStepAccumulatedMarkFrom ω v p` accumulates the increments along the
remaining path `p` while the walk stands at the address `v`: the current
address is carried along explicitly, so no index arithmetic (`take`,
`getElem!`) is needed. `branchingStepAccumulatedMark` is the special case that
starts at the root and is total on all addresses: absent slots contribute
zero, so it is the algebraic extension of the displacement. The paper's sum
over the prefixes is kept as a bridge lemma, in a `Finset.range` and a `Fin`
form.
-/

namespace ThesisSpeed

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
@[simp] theorem branchingStepAccumulatedMarkFrom_nil {α : Type*} {X : Type*}
    [AddCommMonoid X] (ω : BranchingStepField α X) (v : TreeNode α) :
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

end ThesisSpeed
