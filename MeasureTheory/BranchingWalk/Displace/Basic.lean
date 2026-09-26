import MeasureTheory.BranchingWalk.Basic
import MeasureTheory.BranchingWalk.Step.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Displacement along a path

`displace β v p` is the displacement along the remaining path `p` while the
walk stands at the address `v`: the current
address is carried along explicitly, so no index arithmetic (`take`,
`getElem!`) is needed. `displaceRoot` is the special case that
starts at the root and is total on all addresses: absent slots contribute
zero, so it is the algebraic extension of the displacement. The paper's sum
over the prefixes is kept as a bridge lemma, in a `Finset.range` and a `Fin`
form.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris



/-- The displacement along the remaining path `p` while the walk is at the
address `v`. The current address is carried along explicitly, so no index
arithmetic (`take`, `getElem!`) is needed. -/
def displace {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) : TreeNode α → TreeNode α → X
  | _, [] => 0
  | v, i :: p => value' (β v) i +
      displace β (v ++ [i]) p

/-- The total displacement along a root path. Absent slots contribute
zero, so this is an algebraic extension; the partial version that records
absence is `displaceRoot?`. The paper's sum over the prefixes
of `u` is the bridge lemma `displaceRoot_eq_sum`. -/
def displaceRoot {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (u : TreeNode α) : X :=
  displace β [] u

@[simp] theorem displace_nil {α : Type*} {X : Type*}
    [AddCommMonoid X] (β : StepField α X) (v : TreeNode α) :
    displace β v [] = 0 := rfl

theorem displace_cons {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v : TreeNode α) (i : α) (p : TreeNode α) :
    displace β v (i :: p) =
      value' (β v) i +
        displace β (v ++ [i]) p := rfl

/-- The displacement splits an appended path, moving the starting address by
the first part. -/
theorem displace_append {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v p q : TreeNode α) :
    displace β v (p ++ q) =
      displace β v p +
        displace β (v ++ p) q := by
  induction p generalizing v with
  | nil => simp [displace]
  | cons i p ih =>
      have hpath : v ++ (i :: p) = (v ++ [i]) ++ p := by simp
      rw [List.cons_append, displace_cons,
        displace_cons, ih (v := v ++ [i]), hpath, add_assoc]

/-- Re-basing the step field below a prefix `u` is the same as moving the
starting address by `u`. -/
theorem displace_rebase {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (u v p : TreeNode α) :
    displace (fun w => β (u ++ w)) v p =
      displace β (u ++ v) p := by
  induction p generalizing v with
  | nil => rfl
  | cons i p ih =>
      have hpath : u ++ (v ++ [i]) = (u ++ v) ++ [i] := by simp
      rw [displace_cons, displace_cons,
        ih (v := v ++ [i]), hpath]

/-- The paper's defining formula, in the form that carries the starting
address. For `j < p.length` the option `p[j]?` is `some p_j`; the `getD 0`
guards the out-of-range indices. -/
theorem displace_eq_sum {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v : TreeNode α) (p : TreeNode α) :
    displace β v p =
      ∑ j ∈ Finset.range p.length,
        (Option.map (value' (β (v ++ p.take j))) (p[j]?)).getD 0 := by
  induction p generalizing v with
  | nil => simp [displace]
  | cons i p ih =>
      rw [displace_cons, ih (v := v ++ [i]),
        List.length_cons, Finset.sum_range_succ']
      have hzero : (Option.map (value'
            (β (v ++ (i :: p).take 0))) ((i :: p)[0]?)).getD 0 =
          value' (β v) i := by simp
      have hshift : (∑ k ∈ Finset.range p.length,
            (Option.map (value'
              (β (v ++ (i :: p).take (k + 1)))) ((i :: p)[k + 1]?)).getD 0) =
          ∑ k ∈ Finset.range p.length,
            (Option.map (value' (β ((v ++ [i]) ++ p.take k)))
              (p[k]?)).getD 0 := by
        apply Finset.sum_congr rfl
        intro k _
        have hpath : v ++ (i :: p.take k) = (v ++ [i]) ++ p.take k := by simp
        rw [List.take_succ_cons, List.getElem?_cons_succ, hpath]
      rw [hshift, hzero]
      exact add_comm _ _

theorem displaceRoot_nil {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) :
    displaceRoot β [] = 0 := rfl

theorem displaceRoot_singleton {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (i : α) :
    displaceRoot β [i] = value' (β []) i := by
  simp [displaceRoot, displace]

theorem displaceRoot_append_singleton {α : Type*} {X : Type*}
    [AddCommMonoid X]
    (β : StepField α X) (u : TreeNode α) (i : α) :
    displaceRoot β (u ++ [i]) =
      displaceRoot β u + value' (β u) i := by
  simp [displaceRoot, displace_append,
    displace]

theorem displaceRoot_append_two {α : Type*} {X : Type*}
    [AddCommMonoid X]
    (β : StepField α X) (u : TreeNode α)
    (i j : α) :
    displaceRoot β (u ++ [i, j]) =
      displaceRoot β u +
        value' (β u) i +
        value' (β (u ++ [i])) j := by
  rw [show u ++ [i, j] = (u ++ [i]) ++ [j] by simp]
  rw [displaceRoot_append_singleton]
  rw [displaceRoot_append_singleton]

/-- The paper's sum over the prefixes of `u`. -/
theorem displaceRoot_eq_sum {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (u : TreeNode α) :
    displaceRoot β u =
      ∑ j ∈ Finset.range u.length,
        (Option.map (value' (β (u.take j))) (u[j]?)).getD 0 := by
  simpa [displaceRoot] using
    displace_eq_sum β [] u

/-- The same sum indexed by `Fin p.length`, in the form that carries the
starting address. Every index comes with its own bound, so the summand is the
slot at that index and no `getD` guard is needed. -/
theorem displace_eq_sum_fin {α : Type*} {X : Type*}
    [AddCommMonoid X]
    (β : StepField α X) (v p : TreeNode α) :
    displace β v p =
      ∑ j : Fin p.length, value' (β (v ++ p.take j)) (p[j]) := by
  induction p generalizing v with
  | nil => simp [displace]
  | cons i p ih =>
      change value' (β v) i +
          displace β (v ++ [i]) p =
        ∑ j : Fin (p.length + 1),
          value' (β (v ++ (i :: p).take j)) ((i :: p)[j])
      rw [Fin.sum_univ_succ, ih (v := v ++ [i])]
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro k _
        congr 2
        simp

/-- The paper's sum over the prefixes, indexed by `Fin u.length` instead of
`Finset.range u.length`. -/
theorem displaceRoot_eq_sum_fin {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (u : TreeNode α) :
    displaceRoot β u =
      ∑ j : Fin u.length, value' (β (u.take j)) (u[j]) := by
  simpa [displaceRoot] using
    displace_eq_sum_fin β ([] : TreeNode α) u

theorem displaceRoot_append {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) (u v : TreeNode α) :
    displaceRoot β (u ++ v) =
      displaceRoot β u +
        displaceRoot (fun w => β (u ++ w)) v := by
  simp only [displaceRoot]
  rw [displace_append,
    displace_rebase β u [] v, List.append_nil]
  rfl

end BranchingWalk

end MeasureTheory
