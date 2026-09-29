module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Combinatorics.BranchingWalk.Step.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Displacement along a path

`displace β v p` is the displacement from the address `v` to the address
`v ++ p`: it sums the zero-defaulted marks of the slots of `p`, reading each
slot at the address it is met at. The current address is carried along
explicitly, so no index arithmetic (`take`, `getElem!`) is needed. Absent slots
contribute zero, so it is the algebraic extension of the displacement.

The root displacement is `displace β [] u`, written out at the call sites
rather than packaged in a second definition. The sum over prefixes
is kept as a bridge lemma, in a `Finset.range` and a `Fin` form. The partial
recursion that records absence is `displace? β v p`, with the root form
`displace? β [] u`. Root-indexed displacement is the single-root displacement
read at one fixed root, so it is not defined here either: the
`ProbabilityTheory.BranchingRandomWalk.RootIndexed` layer wraps these
definitions root by root.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris



/-- The displacement from the address `v` along the remaining path `p`. The
current address is carried along explicitly, so no index arithmetic (`take`,
`getElem!`) is needed. -/
def displace {α : Type*} {X : Type*} [AddCommMonoid X]
    (β : StepField α X) : TreeNode α → TreeNode α → X
  | _, [] => 0
  | v, i :: p => value' (β v) i +
      displace β (v ++ [i]) p

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

/-- The prefix-sum formula, in the form that carries the starting
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

/-- Increment of one step from the root: the displacement of `u ++ [i]` is the
displacement of `u` plus the mark of the slot at `i`. -/
theorem displace_append_singleton {α : Type*} {X : Type*}
    [AddCommMonoid X]
    (β : StepField α X) (u : TreeNode α) (i : α) :
    displace β [] (u ++ [i]) =
      displace β [] u + value' (β u) i := by
  rw [displace_append, List.nil_append, displace_cons, displace_nil, add_zero]

/-- Increment of two steps from the root, in the order in which the two slots
are met. -/
theorem displace_append_two {α : Type*} {X : Type*}
    [AddCommMonoid X]
    (β : StepField α X) (u : TreeNode α)
    (i j : α) :
    displace β [] (u ++ [i, j]) =
      displace β [] u +
        value' (β u) i +
        value' (β (u ++ [i])) j := by
  rw [show u ++ [i, j] = (u ++ [i]) ++ [j] by simp]
  rw [displace_append_singleton]
  rw [displace_append_singleton]

end Branching

end Combinatorics

/-!
# The partial displacement

`displace? β v p` is the same path recursion as
`displace`, but it computes in `Option X`: as soon
as one slot on the path is absent it returns `none`. Being a direct recursion,
it needs neither `classical` nor a decision procedure for
`surviveAlong β v p`. The main lemma binds the three readings — the partial
mark has a value, the path is realized, and that value is the total mark — and
prefix sums are kept as bridge lemmas in both indexings.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris



/-- The partial displacement along the remaining path `p` from the address
`v`; `none` as soon as one slot on the path is absent. -/
def displace? {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) : TreeNode α → TreeNode α → Option X
  | _, [] => some 0
  | v, i :: p =>
      (β v i).bind fun x =>
        (displace? β (v ++ [i]) p).map fun y => x + y

@[simp] theorem displace?_nil {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v : TreeNode α) :
    displace? β v [] = some 0 := rfl

theorem displace?_cons {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v : TreeNode α) (i : α) (p : TreeNode α) :
    displace? β v (i :: p) =
      (β v i).bind fun x =>
        (displace? β (v ++ [i]) p).map fun y => x + y := rfl

theorem displace?_eq_none_iff {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v p : TreeNode α) :
    displace? β v p = none ↔
      ¬ surviveAlong β v p := by
  induction p generalizing v with
  | nil => simp [surviveAlong]
  | cons i p ih =>
      rw [displace?_cons, surviveAlong_cons]
      cases h : β v i with
      | none => simp [h, survive]
      | some x =>
          have hp : survive (β v) i := ⟨x, h⟩
          simp [hp, ih (v := v ++ [i]), Option.map_eq_none_iff]

/-- On a realized path the partial recursion returns the total displacement
mark. -/
theorem displace?_eq_some_of_survive {α X : Type*}
    [AddCommMonoid X] (β : StepField α X) :
    ∀ (v p : TreeNode α), surviveAlong β v p →
      displace? β v p =
        some (displace β v p)
  | v, [], _ => rfl
  | v, i :: p, h => by
      obtain ⟨x, hx⟩ := h.1
      have ih := displace?_eq_some_of_survive β (v ++ [i]) p h.2
      rw [displace?_cons, displace_cons,
        value'_some (β v) i x hx, hx, ih]
      simp

/-- The three readings of the partial mark — it has a value, the path is
realized, and that value is the total displacement — are one statement. -/
theorem displace?_eq_some_iff {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v p : TreeNode α) (x : X) :
    displace? β v p = some x ↔
      surviveAlong β v p ∧
        displace β v p = x := by
  constructor
  · intro h
    by_cases hp : surviveAlong β v p
    · have htot := displace?_eq_some_of_survive β v p hp
      rw [htot] at h
      exact ⟨hp, Option.some.inj h⟩
    · have hnone := (displace?_eq_none_iff β v p).mpr hp
      rw [hnone] at h
      exact absurd h (by simp)
  · rintro ⟨hp, rfl⟩
    exact displace?_eq_some_of_survive β v p hp

theorem displace?_isSome_iff {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v p : TreeNode α) :
    (displace? β v p).isSome ↔
      surviveAlong β v p := by
  cases h : displace? β v p with
  | none => simp [(displace?_eq_none_iff β v p).mp h]
  | some x =>
      have hp : surviveAlong β v p :=
        ((displace?_eq_some_iff β v p x).mp h).1
      simp [hp]

/-- The partial mark in range-indexed sum form: it is `some x`
exactly when the address is realized and the displacement equals `x`.
The `getD 0` guard absorbs the indices outside the range; realizability is
carried separately by the first conjunct. -/
theorem displace?_eq_some_sum_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (v p : TreeNode α) (x : X) :
    displace? step v p = some x ↔
      surviveAlong step v p ∧
        (∑ j ∈ Finset.range p.length,
          (Option.map (value' (step (v ++ p.take j))) (p[j]?)).getD 0) = x := by
  rw [displace?_eq_some_iff, displace_eq_sum]

/-- The partial mark in the `Fin`-indexed sum form, from the root. -/
theorem displace?_eq_some_sum_fin_iff {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (x : X) :
    displace? step [] u = some x ↔
      (∀ j : Fin u.length, survive (step (u.take j)) (u[j])) ∧
        (∑ j : Fin u.length, value' (step (u.take j)) (u[j])) = x := by
  rw [displace?_eq_some_iff, surviveAlong_root_iff_forall_fin,
    displace_eq_sum_fin]
  simp only [List.nil_append]

/-- Appending one step from the root: the partial mark at `u ++ [i]` is `some`
of the incremented total exactly when `u` is realized and the slot at `i` is
survive. This replaces the earlier statement that wrapped the total definition
in an `if`, which forced a `Classical.propDecidable` instance into the
conclusion. -/
theorem displace?_append_singleton
    {α X : Type*} [AddCommMonoid X]
    (step : StepField α X) (u : TreeNode α) (i : α) :
    displace? step [] (u ++ [i]) =
        some (displace step [] u + value' (step u) i) ↔
      surviveAlong step [] u ∧ survive (step u) i := by
  rw [displace?_eq_some_iff, surviveAlong_root_append_singleton_iff,
    displace_append_singleton]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

end Branching

end Combinatorics

end
