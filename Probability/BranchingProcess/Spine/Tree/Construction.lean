/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Family.Marginals
public import Probability.BranchingProcess.Spine.LocalBias.Normalization
public import Probability.BranchingProcess.Spine.LocalBias.Tree
public import Probability.BranchingProcess.State.Kernel
public import Probability.Kernel.Sum

/-!
# Normal and distinguished particles on the canonical state tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `reproductionKernel Q h` acts on `S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}`.
  Normal parents use `Q(s)` and produce normal children. Distinguished parents
  use the joint bias `Q(s,dξ) h(ξ_i)/h(s)` and distinguish exactly child `i`.
* `reproductionKernel_normal` and `reproductionKernel_distinguished` give the
  two reproduction laws.
* `reproductionKernel_distinguished_map` proves that erasing the roles gives
  the biased family marginal, with density `∑_i h(ξ_i)/h(s)`.
* `reproductionKernel_isMarkovKernel` proves normalization from harmonicity
  on the positive finite-weight domain only.
* `treeKernel Q hh harmonic` constructs the entire typed tree with the existing
  state-dependent Ionescu--Tulcea process. `treeKernel.isMarkovKernel` and
  `treeKernel_root` give its probability and initial-state properties.

This specializes the single `LocalBias` construction to the mean-harmonic
density `h(child)/h(parent)`, implementing the normal/special reproduction algorithm of Zhan Shi,
*Branching Random Walks* (2015), Chapter 4, §4.4 after (4.8),
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
The tree-marginal density and path decomposition are separate assertions;
construction alone does not identify them. Normal particles may have zero weight.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

/-- Original reproduction for normal particles, joint family/child bias for distinguished ones. -/
noncomputable def reproductionKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (h : S → ℝ≥0∞) :
    Kernel (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) (Step ι (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞})) :=
  LocalBias.reproductionKernel Q (LocalBias.ofWeight h)

omit [MeasurableSingletonClass ι] in
@[simp] theorem reproductionKernel_normal (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    (h : S → ℝ≥0∞) (s : S) :
    reproductionKernel Q h (Sum.inl s) = (Q s).map (Step.map Sum.inl) := by
  exact LocalBias.reproductionKernel_normal Q (LocalBias.ofWeight h) s

@[simp] theorem reproductionKernel_distinguished (Q : Kernel S (Step ι S))
    [IsSFiniteKernel Q] {h : S → ℝ≥0∞} (hh : Measurable h)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    reproductionKernel Q h (Sum.inr s) = (biasedFamilyChild Q h s).map
      (fun p => Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2) := by
  have hP : MeasurableSet {s | h s ≠ 0 ∧ h s ≠ ∞} :=
    (hh (MeasurableSet.singleton 0).compl).inter (hh (MeasurableSet.singleton ∞).compl)
  exact LocalBias.reproductionKernel_distinguished Q (LocalBias.ofWeight h) hP s

/-- Forgetting the distinguished child's role gives precisely the biased family law. -/
theorem reproductionKernel_distinguished_map (Q : Kernel S (Step ι S))
    [IsSFiniteKernel Q] {h : S → ℝ≥0∞} (hh : Measurable h)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    (reproductionKernel Q h (Sum.inr s)).map (Step.map (Sum.elim id Subtype.val)) =
      biasedFamily Q h s := by
  have hP : MeasurableSet {s | h s ≠ 0 ∧ h s ≠ ∞} :=
    (hh (MeasurableSet.singleton 0).compl).inter (hh (MeasurableSet.singleton ∞).compl)
  rw [reproductionKernel_distinguished Q hh,
    Measure.map_map (Step.map_measurable (measurable_id.sumElim measurable_subtype_coe))
      (Step.distinguishChild_measurable hP)]
  have heq : (Step.map (Sum.elim id Subtype.val) ∘
      (fun p : Step ι S × ι => Step.distinguishChild
        (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2)) = Prod.fst := by
    funext p
    exact Step.distinguishChild_map _ _ _
  rw [heq]
  exact (Kernel.map_apply _ measurable_fst _).symm

/-- Harmonicity is required only at states that can carry the distinguished particle. -/
theorem reproductionKernel_isMarkovKernel (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    IsMarkovKernel (reproductionKernel Q h) :=
  LocalBias.reproductionKernel_isMarkovKernel Q (LocalBias.ofWeight h)
    (LocalBias.ofWeight_isAdmissible Q hh harmonic)

/-- The canonical complete tree with normal and distinguished states. -/
noncomputable def treeKernel (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    Kernel (Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
      (List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞})) :=
  LocalBias.treeKernel Q (LocalBias.ofWeight h)
    (LocalBias.ofWeight_isAdmissible Q hh harmonic)

instance treeKernel.isMarkovKernel (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    IsMarkovKernel (treeKernel Q hh harmonic) :=
  LocalBias.treeKernel.isMarkovKernel Q (LocalBias.ofWeight h)
    (LocalBias.ofWeight_isAdmissible Q hh harmonic)

theorem treeKernel_root (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞})) :
    (treeKernel Q hh harmonic s).map (fun t => t []) = Measure.dirac s :=
  LocalBias.treeKernel_root Q (LocalBias.ofWeight h)
    (LocalBias.ofWeight_isAdmissible Q hh harmonic) s

end ProbabilityTheory.BranchingProcess.Spine

end
