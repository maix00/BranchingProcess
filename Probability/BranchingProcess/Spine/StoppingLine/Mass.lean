/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Density.Weight
public import Probability.BranchingProcess.State.Observation.History
public import Combinatorics.UlamHarris.Line.Truncation
public import Probability.Process.Tree.Line.Basic

/-!
# Ancestral mass on a line and its generation truncations

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine.StoppingLine`:

* `mass h L` is the sum of normalized ancestral weights on `L`.
* `measurable_mass` observes this mass for countable slots and any random line.
* `generationMass h L n` is its contribution at depth `n`.
* `unexitedMass h L n` sums weights at depth `n` before any
  strict ancestor has reached `L`.
* `mass_eq_tsum_generation` identifies `W_L = ∑_n A_n`.
* `mass_truncate` identifies the existing combinatorial cut exactly:
  `W_(L_n) = ∑_(k<n) A_k + U_n`, for every realized line.
* `truncatedMass_empty` recovers the ordinary generation density.
* `truncatedMass_zero` gives the deterministic normalization `S_0 = 1`.
* `truncatedMass h L n` is the real mass
  `∑_(k<n) (generationMass h L k).toReal + (unexitedMass h L n).toReal`.

These read the original tree and reuse `addressWeight`, including its ancestral
eligibility guard; no auxiliary population process is defined. The decomposition
is that of J. D. Biggins and A. E. Kyprianou, *Measure change in multitype branching*
(2004), §14, Lemma 14.3, pp. 578–579, DOI 10.1239/aap/1086957585.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine.StoppingLine

open Classical MeasureTheory Finset
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S]

/-- Normalized ancestral mass on a line of the existing original state tree. -/
noncomputable def mass (h : S → ℝ≥0∞)
    (L : (List ι → Option S) → Set (Unit × List ι)) (t : List ι → Option S) : ℝ≥0∞ :=
  ∑' u : List ι, if ((), u) ∈ L t then
    addressWeight h u.length u.get (State.treeHistory u.length t) else 0

/-- The part of the line mass lying in a single generation. -/
noncomputable def generationMass (h : S → ℝ≥0∞)
    (L : (List ι → Option S) → Set (Unit × List ι)) (n : ℕ) (t : List ι → Option S) : ℝ≥0∞ :=
  ∑' z : Fin n → ι, if ((), List.ofFn z) ∈ L t then
    addressWeight h n z (State.treeHistory n t) else 0

/-- Generation mass before any strict ancestor has reached the line. -/
noncomputable def unexitedMass (h : S → ℝ≥0∞)
    (L : (List ι → Option S) → Set (Unit × List ι)) (n : ℕ) (t : List ι → Option S) : ℝ≥0∞ := by
  classical
  exact ∑' z : Fin n → ι, @ite ℝ≥0∞
    (∀ k < n, ((), (List.ofFn z).take k) ∉ L t) (Classical.propDecidable _)
    (addressWeight h n z (State.treeHistory n t)) 0

/-- Frozen masses before depth `n`, together with the still unexited generation. -/
noncomputable def truncatedMass (h : S → ℝ≥0∞)
    (L : (List ι → Option S) → Set (Unit × List ι)) (n : ℕ) (t : List ι → Option S) : ℝ :=
  ∑ k ∈ range n, (generationMass h L k t).toReal +
    (unexitedMass h L n t).toReal


/-- The line mass is measurable, independently of harmonicity or any law. -/
@[fun_prop] theorem measurable_mass [Countable ι] {h : S → ℝ≥0∞} (hh : Measurable h)
    {L : (List ι → Option S) → Set (Unit × List ι)} (hL : ProbabilityTheory.Tree.IsRandomLine L) :
    Measurable (mass h L) := by
  apply Measurable.tsum
  intro u
  exact ((measurable_addressWeight hh u.length u.get).comp
    (State.measurable_treeHistory u.length)).ite
      (hL.measurableSet_mem ((), u)) measurable_const

omit [MeasurableSpace S] in
/-- Regroup the same node weights by their generations, using the native
list/finite-tuple equivalence rather than another population representation. -/
theorem mass_eq_tsum_generation (h : S → ℝ≥0∞)
    (L : (List ι → Option S) → Set (Unit × List ι)) (t : List ι → Option S) :
    mass h L t = ∑' n, generationMass h L n t := by
  let f (p : Sigma (fun n : ℕ => Fin n → ι)) : ℝ≥0∞ :=
    if ((), List.ofFn p.2) ∈ L t then addressWeight h p.1 p.2 (State.treeHistory p.1 t) else 0
  have he := (List.equivSigmaTuple (α := ι)).tsum_eq f
  have hs := tsum_sigma' f
  have hterm (u : List ι) : f (List.equivSigmaTuple u) =
      if ((), u) ∈ L t then
        addressWeight h u.length u.get (State.treeHistory u.length t) else 0 := by
    change (if ((), List.ofFn u.get) ∈ L t then
      addressWeight h u.length u.get (State.treeHistory u.length t) else 0) = _
    rw [List.ofFn_get]
  calc
    _ = ∑' u : List ι, f (List.equivSigmaTuple u) := tsum_congr fun u => (hterm u).symm
    _ = _ := he.trans hs

omit [MeasurableSpace S] in
/-- The frozen-mass decomposition is exactly the weight of the existing
combinatorial generation truncation, not a different cut construction. -/
theorem mass_truncate (h : S → ℝ≥0∞)
    (L : (List ι → Option S) → Set (Unit × List ι)) (t : List ι → Option S)
    (hL : Combinatorics.UlamHarris.RootIndexed.IsLine (L t)) (n : ℕ) :
    mass h (fun x => Combinatorics.UlamHarris.RootIndexed.Line.truncate (L x) n) t =
      ∑ k ∈ range n, generationMass h L k t + unexitedMass h L n t := by
  let L' := fun x => Combinatorics.UlamHarris.RootIndexed.Line.truncate (L x) n
  have hlo (k : ℕ) (hk : k < n) : generationMass h L' k t =
      generationMass h L k t := by
    unfold generationMass
    apply tsum_congr
    intro z
    have hm := Combinatorics.UlamHarris.RootIndexed.Line.mem_truncate_iff_of_lt hL
      (u := ((), List.ofFn z)) (by simpa only [List.length_ofFn] using hk)
    simp only [L', hm]
  have heq : generationMass h L' n t = unexitedMass h L n t := by
    unfold generationMass unexitedMass
    apply tsum_congr
    intro z
    have hm : ((), List.ofFn z) ∈ L' t ↔
        ∀ k < n, ((), (List.ofFn z).take k) ∉ L t := by
      dsimp only [L']
      rw [Combinatorics.UlamHarris.RootIndexed.Line.truncate,
        Combinatorics.UlamHarris.RootIndexed.Line.mem_firstEntrance_iff]
      simp only [Set.mem_union, Set.mem_ofPred_eq, List.length_ofFn, or_true, true_and,
        not_or]
      constructor
      · intro hm k hk
        exact (hm k hk).1
      · intro hm k hk
        refine ⟨hm k hk, ?_⟩
        simp only [List.length_take, List.length_ofFn, Nat.min_eq_left (Nat.le_of_lt hk)]
        omega
    by_cases hc : ∀ k < n, ((), (List.ofFn z).take k) ∉ L t <;> simp [hm, hc]
  have hzero (k : ℕ) (hk : k ∉ range (n + 1)) : generationMass h L' k t = 0 := by
    have hkn : n < k := by
      simp only [mem_range] at hk
      omega
    have hnot (z : Fin k → ι) : ((), List.ofFn z) ∉ L' t := by
      intro hz
      have hd := Combinatorics.UlamHarris.RootIndexed.Line.truncate_depth_le hz
      simp only [List.length_ofFn] at hd
      omega
    simp only [generationMass, hnot, ite_false, tsum_zero]
  rw [mass_eq_tsum_generation, tsum_eq_sum hzero, sum_range_succ, heq]
  congr 1
  exact sum_congr rfl fun k hk => hlo k (mem_range.mp hk)

omit [MeasurableSpace S] in
/-- Frozen line mass starts at the normalized root weight. -/
@[simp] theorem truncatedMass_zero (h : S → ℝ≥0∞)
    (L : (List ι → Option S) → Set (Unit × List ι)) (t : List ι → Option S) :
    truncatedMass h L 0 t = 1 := by
  simp [truncatedMass, unexitedMass, addressWeight, tsum_fintype]


omit [MeasurableSpace S] in
/-- With no stopping boundary, the same construction is the generation mass. -/
@[simp] theorem truncatedMass_empty (h : S → ℝ≥0∞) (n : ℕ)
    (t : List ι → Option S) :
    truncatedMass h (fun _ => ∅) n t = (totalWeight h n (State.treeHistory n t)).toReal := by
  simp [truncatedMass, generationMass, unexitedMass, totalWeight]

end ProbabilityTheory.BranchingProcess.Spine.StoppingLine
