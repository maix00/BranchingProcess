module

public import Combinatorics.BranchingWalk.Walk.Basic
public import Mathlib.Order.KonigLemma

/-!
# Survival of branching walks

Survival is a property of a branching walk, independent of positions. A walk
has a surviving descendant at depth `n` when some realized address has length
`n`. Permanent survival means one infinite slot sequence has every finite
prefix realized. Without finite branching, merely having descendants at every
depth is weaker.
-/

@[expose] public section

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
    let Level : ℕ → Type _ := fun n =>
      {u : TreeNode α // u.length = n ∧ surviveAlong step [] u}
    let project : {i j : ℕ} → (hij : i ≤ j) → Level j → Level i :=
      fun {i j} hij u => ⟨u.1.take i, by
        refine ⟨?_, ?_⟩
        · rw [List.length_take, u.2.1, Nat.min_eq_left hij]
        · apply surviveAlong_prefix step (u.1.take i) (u.1.drop i)
          simpa using u.2.2⟩
    have project_refl : ∀ ⦃i⦄ (u : Level i), project rfl.le u = u := by
      intro i u
      apply Subtype.ext
      simp [project, u.2.1]
    have project_trans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k) (u : Level k),
        project hij (project hjk u) = project (hij.trans hjk) u := by
      intro i j k hij hjk u
      apply Subtype.ext
      simp [project, List.take_take, Nat.min_eq_left hij]
    have level_nonempty : ∀ n, Nonempty (Level n) := by
      intro n
      obtain ⟨u, hu, hs⟩ := h n
      exact ⟨⟨u, hu, hs⟩⟩
    have level_zero_finite : Finite (Level 0) := by
      have hnil : ∀ u : Level 0, u.1 = [] := by
        intro u
        cases hu : u.1 with
        | nil => rfl
        | cons a as =>
            have hlen := u.2.1
            rw [hu] at hlen
            cases hlen
      have level_zero_subsingleton : Subsingleton (Level 0) := ⟨fun u v => by
        apply Subtype.ext
        rw [hnil u, hnil v]⟩
      exact @Finite.of_subsingleton (Level 0) level_zero_subsingleton
    have project_fibers_finite : ∀ i (u : Level i),
        {v : Level (i + 1) | project (Nat.le_add_right i 1) v = u}.Finite := by
      intro i u
      let children : Set α := {j | survive (step u.1) j}
      have hchildren : children.Finite := hfinite root u.1
      apply Set.Finite.of_injOn
        (f := fun v : Level (i + 1) => v.1[i]'(by rw [v.2.1]; omega))
        (s := {v : Level (i + 1) | project (Nat.le_add_right i 1) v = u})
        (t := children)
      · intro v hv
        change survive (step u.1) (v.1[i]'(by rw [v.2.1]; omega))
        have hproject : v.1.take i = u.1 := by
          simpa [project] using congrArg Subtype.val hv
        have hi : i < v.1.length := by
          rw [v.2.1]
          omega
        have hslot :=
          (surviveAlong_root_iff_forall_fin step v.1).mp v.2.2 ⟨i, hi⟩
        simpa [hproject] using hslot
      · intro v hv w hw hslot
        apply Subtype.ext
        change v.1[i]'(by rw [v.2.1]; omega) =
          w.1[i]'(by rw [w.2.1]; omega) at hslot
        have hvproject : v.1.take i = u.1 := by
          simpa [project] using congrArg Subtype.val hv
        have hwproject : w.1.take i = u.1 := by
          simpa [project] using congrArg Subtype.val hw
        have hvlen : v.1.length = i + 1 := v.2.1
        have hwlen : w.1.length = i + 1 := w.2.1
        have hvrepr : v.1 = v.1.take i ++ [v.1[i]] := by
          calc
            v.1 = v.1.take (i + 1) := by simp [hvlen]
            _ = v.1.take i ++ [v.1[i]] :=
              (List.take_concat_get' v.1 i (by rw [hvlen]; omega)).symm
        have hwrepr : w.1 = w.1.take i ++ [w.1[i]] := by
          calc
            w.1 = w.1.take (i + 1) := by simp [hwlen]
            _ = w.1.take i ++ [w.1[i]] :=
              (List.take_concat_get' w.1 i (by rw [hwlen]; omega)).symm
        rw [hvrepr, hwrepr, hvproject, hwproject, hslot]
      · exact hchildren
    obtain ⟨prefixes, hcoherent⟩ :=
      @exists_seq_forall_proj_of_forall_finite Level level_zero_finite level_nonempty
        project project_refl project_trans project_fibers_finite
    let lineage : ℕ → α := fun n =>
      (prefixes (n + 1)).1[n]'(by rw [(prefixes (n + 1)).2.1]; omega)
    have hprefix : ∀ n, (prefixes n).1 = lineagePrefix lineage n := by
      intro n
      induction n with
      | zero =>
          have hlen := (prefixes 0).2.1
          have hnil : (prefixes 0).1 = [] := by
            cases h : (prefixes 0).1 with
            | nil => rfl
            | cons a as => simp [h] at hlen
          simpa [lineagePrefix] using hnil
      | succ n ih =>
          have hproject := congrArg Subtype.val
            (hcoherent (i := n) (j := n + 1) (Nat.le_add_right n 1))
          have htake : (prefixes (n + 1)).1.take n = (prefixes n).1 := by
            simpa [project] using hproject
          have hlen := (prefixes (n + 1)).2.1
          have hindex : n < (prefixes (n + 1)).1.length := by
            rw [hlen]
            omega
          have hrepr : (prefixes (n + 1)).1 =
              (prefixes (n + 1)).1.take n ++
                [(prefixes (n + 1)).1[n]'(by rw [hlen]; omega)] := by
            calc
              (prefixes (n + 1)).1 = (prefixes (n + 1)).1.take (n + 1) := by
                simp [hlen]
              _ = (prefixes (n + 1)).1.take n ++ [(prefixes (n + 1)).1[n]] :=
                (List.take_concat_get' _ n hindex).symm
          rw [hrepr, htake, ih]
          simp [lineage, lineagePrefix]
    refine ⟨lineage, ?_⟩
    intro n
    rw [← hprefix n]
    exact (prefixes n).2.2
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

/-- For a singleton-slot walk, having a surviving particle at every
generation is equivalent to one infinite surviving lineage.  The finite
branching hypothesis is automatic here: there is at most one possible child
at each node. -/
theorem survivesForever_iff_survivesEveryGeneration
    {Mark Position : Type*} (walk : Walk Mark Position) :
    walk.SurvivesForever ↔
      ∀ n, surviveAlong (walk.step PUnit.unit) [] (lineNode n) := by
  change walk.HasInfiniteLineage PUnit.unit ↔ _
  rw [RootIndexed.BranchingWalk.hasInfiniteLineage_iff_forall_survivesToGeneration]
  constructor
  · intro h n
    obtain ⟨u, hu, hs⟩ := h n
    rw [eq_lineNode_length u, hu] at hs
    exact hs
  · intro h n
    exact ⟨lineNode n, lineNode_length n, h n⟩

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

end
