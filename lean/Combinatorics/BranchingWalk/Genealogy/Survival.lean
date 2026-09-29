import Combinatorics.BranchingWalk.Walk.Basic

/-!
# Survival of branching walks

Survival is a property of a branching walk, independent of positions. A walk
has a surviving descendant at depth `n` when some realized address has length
`n`. Permanent survival means one infinite slot sequence has every finite
prefix realized. Without finite branching, merely having descendants at every
depth is weaker.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

namespace RootIndexed.BranchingWalk

/-- A specified root has a surviving descendant in generation `n`. -/
def SurvivesToGeneration {Root α Mark Position : Type*}
    (walk : RootIndexed.BranchingWalk Root α Mark Position)
    (root : Root) (n : ℕ) : Prop :=
  ∃ u : TreeNode α, u.length = n ∧ surviveAlong (walk.step root) [] u

/-- A specified root has a surviving descendant at arbitrarily large depths.

This is a statement about unbounded tree height. Without a finite-branching
hypothesis it does not assert that these descendants lie on one common
infinite lineage. -/
def HasArbitrarilyDeepDescendant {Root α Mark Position : Type*}
    (walk : RootIndexed.BranchingWalk Root α Mark Position)
    (root : Root) : Prop :=
  ∀ n, walk.SurvivesToGeneration root n

/-- The first `n` entries of an infinite sequence of child slots. -/
def lineagePrefix {α : Type*} (lineage : ℕ → α) (n : ℕ) : TreeNode α :=
  match n with
  | 0 => []
  | n + 1 => lineagePrefix lineage n ++ [lineage n]

/-- A specified root has a single infinite lineage all of whose finite
prefixes survive. -/
def HasInfiniteLineage {Root α Mark Position : Type*}
    (walk : RootIndexed.BranchingWalk Root α Mark Position)
    (root : Root) : Prop :=
  ∃ lineage : ℕ → α, ∀ n,
    surviveAlong (walk.step root) [] (lineagePrefix lineage n)

/-- Permanent survival means existence of one infinite surviving lineage. -/
abbrev SurvivesForever {Root α Mark Position : Type*}
    (walk : RootIndexed.BranchingWalk Root α Mark Position)
    (root : Root) : Prop :=
  walk.HasInfiniteLineage root

theorem HasInfiniteLineage.hasArbitrarilyDeepDescendant
    {Root α Mark Position : Type*}
    (walk : RootIndexed.BranchingWalk Root α Mark Position)
    (root : Root) (h : walk.HasInfiniteLineage root) :
    walk.HasArbitrarilyDeepDescendant root := by
  obtain ⟨lineage, hlineage⟩ := h
  intro n
  have hlen : (lineagePrefix lineage n).length = n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [lineagePrefix, ih]
  exact ⟨lineagePrefix lineage n, hlen, hlineage n⟩

/-- In a finitely branching walk, unbounded tree height yields one infinite
surviving lineage (König's lemma). -/
theorem hasArbitrarilyDeepDescendant_iff_hasInfiniteLineage
    {Root α Mark Position : Type*}
    (walk : RootIndexed.BranchingWalk Root α Mark Position) (root : Root)
    (hfinite : ∀ r u, {i : α | survive (walk.step r u) i}.Finite) :
    walk.HasArbitrarilyDeepDescendant root ↔ walk.HasInfiniteLineage root := by
  classical
  constructor
  · intro h
    let step := walk.step root
    let Good : TreeNode α → Prop := fun u =>
      ∀ n, ∃ v, n ≤ v.length ∧ surviveAlong step [] (u ++ v)
    have hgood0 : Good [] := by
      intro n
      obtain ⟨u, hu, hs⟩ := h n
      exact ⟨u, by omega, by simpa using hs⟩
    have hstep : ∀ u, Good u → ∃ i, Good (u ++ [i]) := by
      intro u hu
      by_contra hnone
      have hnot : ∀ i, ¬ Good (u ++ [i]) := by
        intro i hi
        exact hnone ⟨i, hi⟩
      have hbound : ∀ i, ∃ b, ∀ v, b ≤ v.length →
          ¬ surviveAlong step [] (u ++ [i] ++ v) := by
        intro i
        have hi := hnot i
        dsimp [Good] at hi
        push Not at hi
        exact hi
      let Active := {i : α // survive (step u) i}
      letI : Fintype Active := (hfinite root u).fintype
      let bound : Active → ℕ := fun i => Classical.choose (hbound i.1)
      have bound_spec (i : Active) (v : TreeNode α)
          (hv : bound i ≤ v.length) :
          ¬ surviveAlong step [] (u ++ [i.1] ++ v) :=
        Classical.choose_spec (hbound i.1) v hv
      let maxBound := Finset.univ.sup bound
      obtain ⟨v, hvlen, hsurvive⟩ := hu (maxBound + 1)
      cases v with
      | nil => simp at hvlen
      | cons i tail =>
        have hsurvive' : surviveAlong step [] (u ++ [i] ++ tail) := by
          simpa [List.append_assoc] using hsurvive
        have hprefix : surviveAlong step [] (u ++ [i]) :=
          surviveAlong_prefix step (u ++ [i]) tail hsurvive'
        have hchild : survive (step u) i :=
          (surviveAlong_root_append_singleton_iff step u i).mp hprefix |>.2
        let child : Active := ⟨i, hchild⟩
        have hiBound : bound child ≤ maxBound :=
          Finset.le_sup (Finset.mem_univ child)
        have htail : bound child ≤ tail.length := by
          dsimp at hvlen
          omega
        have hbad := bound_spec child tail htail
        exact hbad hsurvive'
    let State := {u : TreeNode α // Good u}
    let child : State → α := fun s => Classical.choose (hstep s.1 s.2)
    have child_good (s : State) : Good (s.1 ++ [child s]) :=
      Classical.choose_spec (hstep s.1 s.2)
    let next : State → State := fun s => ⟨s.1 ++ [child s], child_good s⟩
    let states : ℕ → State := Nat.rec ⟨[], hgood0⟩ (fun _ s => next s)
    let lineage : ℕ → α := fun n => child (states n)
    have hstate : ∀ n, (states n).1 = lineagePrefix lineage n := by
      intro n
      induction n with
      | zero => simp [states, lineagePrefix]
      | succ n ih =>
        change (next (states n)).1 = lineagePrefix lineage (n + 1)
        simp only [next, lineagePrefix, lineage]
        rw [ih]
    refine ⟨lineage, ?_⟩
    intro n
    obtain ⟨v, _, hsurvive⟩ := (states n).2 0
    have hpref := surviveAlong_prefix step (states n).1 v hsurvive
    simpa [hstate n] using hpref
  · exact HasInfiniteLineage.hasArbitrarilyDeepDescendant walk root

theorem hasInfiniteLineage_iff_forall_survivesToGeneration
    {α Mark Position : Type*} [Finite α]
    (walk : Combinatorics.Branching.BranchingWalk α Mark Position) :
    walk.HasInfiniteLineage PUnit.unit ↔
      ∀ n, walk.SurvivesToGeneration PUnit.unit n := by
  exact (hasArbitrarilyDeepDescendant_iff_hasInfiniteLineage
    walk PUnit.unit (fun _ _ => Set.toFinite _)).symm

end RootIndexed.BranchingWalk

namespace BranchingWalk

/-- Permanent survival for a single-root branching walk. -/
def SurvivesForever {α Mark Position : Type*}
    (walk : BranchingWalk α Mark Position) : Prop :=
  RootIndexed.BranchingWalk.SurvivesForever walk PUnit.unit

end BranchingWalk

namespace Walk

/-- An increment-path realization survives forever. -/
theorem ofIncrements_survivesForever {Mark Position : Type*}
    (initial : Position) (increment : ℕ → Mark) :
    (ofIncrements initial increment).SurvivesForever := by
  refine ⟨fun _ => PUnit.unit, ?_⟩
  intro n
  change surviveAlong (stepFieldOfIncrements increment) []
    (RootIndexed.BranchingWalk.lineagePrefix (fun _ : ℕ => PUnit.unit) n)
  exact surviveAlong_stepFieldOfIncrements increment [] _

end Walk
end Combinatorics.Branching
