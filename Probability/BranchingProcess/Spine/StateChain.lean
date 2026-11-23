/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Family.Marginals
public import Probability.BranchingProcess.Spine.Observation
public import Probability.BranchingProcess.Spine.Tree.Construction
public import Probability.Kernel.DoobTransform.Trajectory
public import Probability.Kernel.DoobTransform.Restriction

/-!
# The state chain associated with the spine transition

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `eligibleStateKernel Q hh` is the generic Doob transform of the mean
  offspring kernel, restricted to `E = {s | 0 < h(s) < ∞}`.
* `eligibleStateKernel_isMarkovKernel`: the offspring harmonicity
  `E_s[∑ᵢ h(ξᵢ)] = h(s)` on `E` makes this kernel Markov.
* `eligibleStateKernel_map`: forgetting the eligible-state subtype gives
  exactly the selected-child marginal `spineChildKernel Q h`.
* `reproductionKernel_distinguished_state` identifies the observed actual
  distinguished offspring law with the same generic Doob transition.
* `partialTraj_spineChildKernel`: when `h` is finite and positive everywhere,
  the finite state-chain law has density `h(x_b)/h(x_a)` relative to the
  finite histories of the mean offspring kernel.

These are direct applications of the independent Doob-transform API.
The complete realized-tree path identification is proved separately in
`Spine/Tree/PathLaw.lean` from the conditional reproduction laws. Compare
Zhan Shi, *Branching Random Walks*, LNM 2151 (2015), Chapter 4, §4.4,
Theorem 4.4(ii) and (4.8), DOI 10.1007/978-3-319-25372-5.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching Finset
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι] [Countable ι]

/-- The spine transition on finite positive-weight states uses the generic Doob kernel. -/
noncomputable def eligibleStateKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h) :
    Kernel {s // h s ≠ 0 ∧ h s ≠ ∞} {s // h s ≠ 0 ∧ h s ≠ ∞} :=
  Kernel.doobTransformOnPositive (meanChildKernel Q) hh

omit [MeasurableSpace ι] in
/-- Mean-harmonic offspring weights normalize the eligible spine transition. -/
theorem eligibleStateKernel_isMarkovKernel (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    IsMarkovKernel (eligibleStateKernel Q hh) := by
  apply Kernel.doobTransformOnPositive_isMarkovKernel
  intro s hs ht
  exact (lintegral_meanChildKernel Q hh s).trans (harmonic s hs ht)

/-- The abstract chain's transition is the concrete joint bias's selected-child marginal. -/
theorem eligibleStateKernel_map [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    (eligibleStateKernel Q hh s).map Subtype.val = spineChildKernel Q h s.1 := by
  rw [spineChildKernel_eq_doobTransform Q hh]
  exact Kernel.doobTransformOnPositive_map _ hh
    (fun s hs ht => (lintegral_meanChildKernel Q hh s).trans (harmonic s hs ht)) s

/-- The finite spine-state path density is inherited from the general Doob identity. -/
theorem partialTraj_spineChildKernel [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (hzero : ∀ s, h s ≠ 0) (htop : ∀ s, h s ≠ ∞)
    {a b : ℕ} (hab : a ≤ b) (x : Iic a → S) :
    Kernel.partialTraj (X := fun _ => S) (Kernel.historyKernel (spineChildKernel Q h)) a b x =
      (Kernel.partialTraj (X := fun _ => S)
        (Kernel.historyKernel (meanChildKernel Q)) a b x).withDensity
        (fun y => h (y ⟨b, by simp⟩) / h (x ⟨a, by simp⟩)) := by
  rw [spineChildKernel_eq_doobTransform Q hh]
  exact Kernel.partialTraj_doobTransform _ hh hzero htop hab x

/-- The actual distinguished offspring observation has the generic Doob transition. -/
theorem reproductionKernel_distinguished_state {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (d s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    (reproductionKernel Q h (Sum.inr s)).map (distinguishedState d) =
      eligibleStateKernel Q hh s := by
  classical
  let E := {s // h s ≠ 0 ∧ h s ≠ ∞}
  have hP : MeasurableSet {s | h s ≠ 0 ∧ h s ≠ ∞} :=
    (hh (MeasurableSet.singleton 0).compl).inter
      (hh (MeasurableSet.singleton ∞).compl)
  have he : MeasurableEmbedding (fun a : E => some a.1) :=
    measurableEmbedding_option_some.comp (MeasurableEmbedding.subtype_coe hP)
  apply he.map_injective
  rw [reproductionKernel_distinguished Q hh,
    Measure.map_map (measurable_distinguishedState d)
      (Step.distinguishChild_measurable hP),
    Measure.map_map he.measurable ((measurable_distinguishedState d).comp
      (Step.distinguishChild_measurable hP))]
  have hsel := ae_biasedFamilyChild_eligible Q hh s.1 s.2.1 s.2.2
    (harmonic s.1 s.2.1 s.2.2)
  have hobs : (fun p : Step ι S × ι =>
      some ((distinguishedState d
        (Step.distinguishChild
          (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2)).1)) =ᵐ[biasedFamilyChild Q h s]
      fun p => p.1 p.2 := by
    filter_upwards [hsel] with p hp
    obtain ⟨v, hv, hz, ht⟩ := hp
    have hd : distinguishedState d (Step.distinguishChild
        (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2) = (⟨v, hz, ht⟩ : E) := by
      apply distinguishedState_eq d _ p.2 _
        (Step.distinguishChild_selected _ _ _ hv ⟨hz, ht⟩)
      intro j hji
      rw [Step.distinguishChild_other _ _ _ _ hji]
      cases p.1 j <;> simp
    simp [hd, hv]
  change (biasedFamilyChild Q h s).map (fun p => some ((distinguishedState d
    (Step.distinguishChild
      (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2)).1)) = _
  rw [Measure.map_congr hobs]
  have hr := eligibleStateKernel_map Q hh harmonic s
  have hr' := congrArg (Measure.map (some : S → Option S)) hr
  rw [Measure.map_map measurable_option_some measurable_subtype_coe] at hr'
  rw [show (eligibleStateKernel Q hh s).map (fun a => some a.1) =
    (spineChildKernel Q h s).map some from hr']
  rw [spineChildKernel, Kernel.comapRight_apply,
    measurableEmbedding_option_some.map_comap,
    Kernel.map_apply _ (measurable_from_prod_countable_left
      (fun i => measurable_pi_apply i))]
  symm
  apply Measure.restrict_eq_self_of_ae_mem
  apply (ae_map_iff (measurable_from_prod_countable_left
    (fun i => measurable_pi_apply i)).aemeasurable
    measurableEmbedding_option_some.measurableSet_range).mpr
  filter_upwards [hsel] with p hp
  obtain ⟨v, hv, _, _⟩ := hp
  exact ⟨v, hv.symm⟩

end ProbabilityTheory.BranchingProcess.Spine

end
