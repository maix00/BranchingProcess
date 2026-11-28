/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Observation
public import Combinatorics.UlamHarris.Ray

/-!
# Measurable path observations of a tree with a distinguished ray

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `statePath` and `measurable_statePath` read distinguished states by generation.
* `existsUnique_distinguished_generation` identifies the unique depth-n node.
* `statePath_eq_of_isRay` identifies the observations with an actual ray.
* `spinePrefix`, `measurable_spinePrefix`, `spinePrefix_eq_of_isRay` read its
  length-n address; `spineRay`, `measurable_spineRay`, `spineRay_eq_of_isRay`
  read its infinite child-index sequence.

These are deterministic observations of the typed tree in Zhan Shi,
*Branching Random Walks* (2015), Theorem 4.3, DOI 10.1007/978-3-319-25372-5.
They are independent of the local bias and of any harmonic weight.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingProcess.Spine
open MeasureTheory Combinatorics.UlamHarris
open scoped ENNReal

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

/-- Read the unique distinguished address through generation `n`, with a fixed
child-index default on exceptional trees. This reuses `distinguishedState`. -/
noncomputable def spinePrefix {S T ι : Type*} (defaultChild : ι)
    (t : List ι → Option (S ⊕ T)) (n : ℕ) : Fin n → ι :=
  distinguishedState (fun _ : Fin n => defaultChild)
    (fun p : Unit × (Fin n → ι) => (t (List.ofFn p.2)).map
      (Sum.map (fun _ : S => ()) (fun _ : T => p.2)))

@[fun_prop]
theorem measurable_spinePrefix {S T ι : Type*} [Countable ι]
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace ι] (defaultChild : ι) (n : ℕ) :
    Measurable (spinePrefix (S := S) (T := T) defaultChild · n) := by
  unfold spinePrefix
  apply (measurable_distinguishedState _).comp
  apply measurable_pi_iff.mpr
  intro p
  exact (measurable_option_map (measurable_const.sumMap measurable_const)).comp
    (measurable_pi_apply (List.ofFn p.2))

/-- The address observation is the prefix of the already realized ray. -/
theorem spinePrefix_eq_of_isRay {S T ι : Type*} (defaultChild : ι)
    (t : List ι → Option (S ⊕ T)) (f : ℕ → ι)
    (hf : IsRay (distinguishedNodes t) f)
    (hc : distinguishedNodes t = Set.range (lineagePrefix f)) (n : ℕ) :
    List.ofFn (spinePrefix defaultChild t n) = lineagePrefix f n := by
  obtain ⟨p, hp, hu⟩ := existsUnique_distinguished_generation t f hf hc n
  obtain ⟨v, hv⟩ : ∃ v, t (List.ofFn p.2) = some (Sum.inr v) := by
    cases he : t (List.ofFn p.2) with
    | none => simp [he] at hp
    | some a => cases a with
      | inl a => simp [he] at hp
      | inr v => exact ⟨v, rfl⟩
  have hr : spinePrefix defaultChild t n = p.2 := by
    apply distinguishedState_eq _ _ p p.2
    · simp only [hv, Option.map_some, Sum.map_inr]
    · intro q hqp hq
      cases he : t (List.ofFn q.2) with
      | none => simp [he] at hq
      | some a => cases a with
        | inl a => simp [he] at hq
        | inr a => exact hqp (hu q (by simp [he]))
  have hnode : List.ofFn p.2 ∈ distinguishedNodes t := hp
  rw [hc] at hnode
  obtain ⟨k, hk⟩ := hnode
  have hkn : k = n := by simpa using congrArg List.length hk
  rw [hkn] at hk
  rw [hr]
  exact hk.symm

/-- A measurable full spine sequence read from the same tagged tree. -/
noncomputable def spineRay {S T ι : Type*} (defaultChild : ι)
    (t : List ι → Option (S ⊕ T)) (n : ℕ) : ι :=
  spinePrefix defaultChild t (n + 1) (Fin.last n)

@[fun_prop]
theorem measurable_spineRay {S T ι : Type*} [Countable ι]
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace ι] (defaultChild : ι) :
    Measurable (spineRay (S := S) (T := T) defaultChild) := by
  apply measurable_pi_iff.mpr
  intro n
  exact (measurable_pi_apply (Fin.last n)).comp (measurable_spinePrefix defaultChild (n + 1))

/-- Reading addresses recovers the existing ray, independently of the exceptional default. -/
theorem spineRay_eq_of_isRay {S T ι : Type*} (defaultChild : ι)
    (t : List ι → Option (S ⊕ T)) (f : ℕ → ι)
    (hf : IsRay (distinguishedNodes t) f)
    (hc : distinguishedNodes t = Set.range (lineagePrefix f)) : spineRay defaultChild t = f := by
  funext n
  change spinePrefix defaultChild t (n + 1) (Fin.last n) = f n
  have hlast := congrArg (fun u : List ι => u.getLastD defaultChild)
    (spinePrefix_eq_of_isRay defaultChild t f hf hc (n + 1))
  simpa only [List.ofFn_succ', List.concat_eq_append, lineagePrefix_succ,
    List.getLastD_concat] using hlast


end ProbabilityTheory.BranchingProcess.Spine

end
