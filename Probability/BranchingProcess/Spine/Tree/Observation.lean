/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Ray
public import Probability.BranchingProcess.Spine.Tree.Observation.Path

/-!
# Harmonic-tree history and realized-spine observations

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `untypedHistory n t` records all states through generation `n` after
  erasing role tags; `measurable_untypedHistory` proves its measurability.
  Its comap sigma algebra is the tree information used in Shi (4.9).

* `ae_treeKernel_spineRay` proves this measurable observation is almost surely
  the actual realized spine: `distinguishedNodes t = range(prefix(spineRay t))`.
* `ae_treeKernel_spinePrefix` proves
  `spinePrefix t n = z ↔ t(ofFn z) has the distinguished role`, almost surely.


This reads the existing tagged tree in Zhan Shi, *Branching Random Walks*
(2015), Chapter 4, §4.4, Theorem 4.4(ii), (4.10),
DOI 10.1007/978-3-319-25372-5. It introduces no additional tree or ray law.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.UlamHarris
open scoped ENNReal

/-- The finite tree history after forgetting ordinary/distinguished roles. -/
def untypedHistory {S ι : Type*} {h : S → ℝ≥0∞} (n : ℕ)
    (t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
    (k : Finset.Iic n) (p : Unit × (Fin k.1 → ι)) : Option S :=
  (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)

@[fun_prop]
theorem measurable_untypedHistory {S ι : Type*} [MeasurableSpace S]
    {h : S → ℝ≥0∞} (n : ℕ) : Measurable (untypedHistory (ι := ι) (h := h) n) := by
  have hm : Measurable (fun o : Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      o.map (Sum.elim id Subtype.val)) :=
    measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
  unfold untypedHistory
  fun_prop

/-- The canonical tree's measurable address observation is its actual distinguished ray. -/
theorem ae_treeKernel_spineRay {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : ProbabilityTheory.Kernel S (Combinatorics.Branching.Step ι S))
    [ProbabilityTheory.IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (defaultChild : ι) :
    ∀ᵐ t ∂treeKernel Q hh harmonic (some (Sum.inr s)),
      IsRay (distinguishedNodes t) (spineRay defaultChild t) ∧
        distinguishedNodes t = Set.range (lineagePrefix (spineRay defaultChild t)) := by
  filter_upwards [ae_treeKernel_unique_spine Q hh harmonic s] with t ht
  obtain ⟨f, ⟨hf, hc⟩, _⟩ := ht
  rw [spineRay_eq_of_isRay defaultChild t f hf hc]
  exact ⟨hf, hc⟩

/-- The measurable prefix observation and distinguished-node event describe the same spine. -/
theorem ae_treeKernel_spinePrefix {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : ProbabilityTheory.Kernel S (Combinatorics.Branching.Step ι S))
    [ProbabilityTheory.IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (defaultChild : ι) :
    ∀ᵐ t ∂treeKernel Q hh harmonic (some (Sum.inr s)), ∀ n (z : Fin n → ι),
      spinePrefix defaultChild t n = z ↔ (t (List.ofFn z)).any Sum.isRight = true := by
  filter_upwards [ae_treeKernel_unique_spine Q hh harmonic s] with t ht
  obtain ⟨f, ⟨hf, hc⟩, _⟩ := ht
  intro n z
  have hpref := spinePrefix_eq_of_isRay defaultChild t f hf hc n
  have hp : (t (List.ofFn (spinePrefix defaultChild t n))).any Sum.isRight = true := by
    rw [hpref]
    exact hf n
  constructor
  · intro hz
    exact hz ▸ hp
  · intro hz
    obtain ⟨p, hpt, hu⟩ := existsUnique_distinguished_generation t f hf hc n
    exact congrArg Prod.snd ((hu ((), spinePrefix defaultChild t n) hp).trans (hu ((), z) hz).symm)

end ProbabilityTheory.BranchingProcess.Spine

end
