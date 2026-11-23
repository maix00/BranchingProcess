/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Ray
public import Probability.BranchingProcess.Spine.Observation

/-!
# Reading states along the realized distinguished ray

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `statePath d t n` reads the distinguished state at depth `n` of `t`.
* `measurable_statePath` proves that the entire sequence is measurable.
* `existsUnique_distinguished_generation` proves that the realized ray meets
  each generation in exactly one distinguished coordinate.
* `statePath_eq_of_isRay` identifies the observations with the actual node
  states whenever the ray prefixes are exactly all distinguished nodes.

This reads the existing tagged tree in Zhan Shi, *Branching Random Walks*
(2015), Chapter 4, §4.4, Theorem 4.4(ii), (4.10),
DOI 10.1007/978-3-319-25372-5. It introduces no additional tree or ray law.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.UlamHarris

/-- The sequence of states read from distinguished nodes of each generation. -/
noncomputable def statePath {S T ι : Type*} (d : T)
    (t : List ι → Option (S ⊕ T)) (n : ℕ) : T :=
  distinguishedState d (fun p : Unit × (Fin n → ι) => t (List.ofFn p.2))

/-- Reading the complete sequence of distinguished states is measurable. -/
theorem measurable_statePath {S T ι : Type*} [Countable ι]
    [MeasurableSpace S] [MeasurableSpace T] (d : T) :
    Measurable (statePath (S := S) (ι := ι) d) := by
  apply measurable_pi_iff.mpr
  intro n
  exact (measurable_distinguishedState d).comp (by fun_prop)

/-- A realized distinguished ray meets each generation at precisely one coordinate. -/
theorem existsUnique_distinguished_generation {S T ι : Type*}
    (t : List ι → Option (S ⊕ T)) (f : ℕ → ι)
    (hf : IsRay (distinguishedNodes t) f)
    (hcarrier : distinguishedNodes t = Set.range (lineagePrefix f)) (n : ℕ) :
    ∃! p : Unit × (Fin n → ι), (t (List.ofFn p.2)).any Sum.isRight = true := by
  let i : Fin n → ι := fun j =>
    (lineagePrefix f n).get (Fin.cast (length_lineagePrefix f n).symm j)
  have hi : List.ofFn i = lineagePrefix f n :=
    (List.ofFn_congr (length_lineagePrefix f n) (lineagePrefix f n).get).symm.trans
      (List.ofFn_get _)
  refine ⟨((), i), by simpa only [distinguishedNodes, Set.mem_ofPred_eq, hi] using hf n, ?_⟩
  intro j hj
  have hnode : List.ofFn j.2 ∈ distinguishedNodes t := hj
  rw [hcarrier] at hnode
  obtain ⟨m, hm⟩ := hnode
  have hmn : m = n := by simpa using congrArg List.length hm
  rw [hmn] at hm
  apply Prod.ext (Subsingleton.elim _ _)
  apply List.ofFn_injective
  exact hm.symm.trans hi.symm

/-- On a realized distinguished ray the observation is its actual node state. -/
theorem statePath_eq_of_isRay {S T ι : Type*} (d : T)
    (t : List ι → Option (S ⊕ T)) (f : ℕ → ι)
    (hf : IsRay (distinguishedNodes t) f)
    (hcarrier : distinguishedNodes t = Set.range (lineagePrefix f)) (n : ℕ) :
    t (lineagePrefix f n) = some (Sum.inr (statePath d t n)) := by
  classical
  have hn := hf n
  change (t (lineagePrefix f n)).any Sum.isRight = true at hn
  obtain ⟨s, hs⟩ : ∃ s, t (lineagePrefix f n) = some (Sum.inr s) := by
    cases he : t (lineagePrefix f n) with
    | none => simp [he] at hn
    | some a => cases a with
      | inl a => simp [he] at hn
      | inr s => exact ⟨s, rfl⟩
  let i : Fin n → ι := fun j =>
    (lineagePrefix f n).get (Fin.cast (length_lineagePrefix f n).symm j)
  have hi : List.ofFn i = lineagePrefix f n :=
    (List.ofFn_congr (length_lineagePrefix f n) (lineagePrefix f n).get).symm.trans
      (List.ofFn_get _)
  have hread : statePath d t n = s := by
    apply distinguishedState_eq d _ ((), i) s (by simpa [hi] using hs)
    intro j hji hj
    have hu := existsUnique_distinguished_generation t f hf hcarrier n
    exact hji (hu.unique hj (by simpa only [distinguishedNodes, Set.mem_ofPred_eq, hi] using hf n))
  rw [hread]
  exact hs

end ProbabilityTheory.BranchingProcess.Spine

end
