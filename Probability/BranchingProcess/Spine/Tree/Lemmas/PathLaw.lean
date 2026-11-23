/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingProcess.Spine.Tree.Observation
import Probability.BranchingProcess.Spine.StateChain

/-!
# Support for identifying the realized spine's state law

## Internal proof declarations

* `generationKernel_distinguished_state` identifies the next observed state
  with `Kʰ(s,·)` when the current population has one distinguished state `s`.
* `ae_pathKernel_unique_distinguished` transfers the realized-ray uniqueness
  to each generation of the same canonical process.

These lemmas assemble the tagged reproduction rules for the path-law theorem
in `Spine/Tree/PathLaw.lean`; they follow Zhan Shi, *Branching Random Walks*
(2015), §4.4, Theorem 4.4(ii), (4.10), DOI 10.1007/978-3-319-25372-5.
-/

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris Finset Preorder
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.Spine

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
private lemma measurableSet_normal_family {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] :
    MeasurableSet {ξ : Step ι (A ⊕ B) | ∀ j, (ξ j).any Sum.isRight ≠ true} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact ((MeasurableSet.singleton true).preimage
    ((show Measurable (fun o : Option (A ⊕ B) => o.any Sum.isRight) from
      measurable_option_elim false (measurable_const.sumElim measurable_const)).comp
        (measurable_pi_apply j))).compl

omit [MeasurableSingletonClass ι] in
private lemma ae_normal_children (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (o : Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
    (hn : o.any Sum.isRight ≠ true) :
    ∀ᵐ ξ ∂Kernel.optionElim (Measure.dirac (fun _ : ι => none))
      (reproductionKernel Q h) o, ∀ j, (ξ j).any Sum.isRight ≠ true := by
  cases o with
  | none =>
    rw [Kernel.optionElim_none]
    exact (ae_dirac_iff measurableSet_normal_family).mpr (by simp)
  | some o =>
    rw [Kernel.optionElim_some]
    cases o with
    | inl s =>
      rw [reproductionKernel_normal]
      apply (ae_map_iff (Step.map_measurable measurable_inl).aemeasurable
        measurableSet_normal_family).mpr
      apply ae_of_all
      intro ξ j
      cases he : ξ j <;> simp [Step.map, he]
    | inr s => simp at hn

lemma generationKernel_distinguished_state (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (d : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ)
    (x : (Unit × (Fin n → ι)) → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
    (p : Unit × (Fin n → ι)) (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    (hp : x p = some (Sum.inr s))
    (ho : ∀ q, q ≠ p → (x q).any Sum.isRight ≠ true) :
    letI := reproductionKernel_isMarkovKernel Q hh harmonic
    (State.generationKernel (reproductionKernel Q h) n x).map (distinguishedState d) =
      eligibleStateKernel Q hh s := by
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  let brood (y : (Unit × (Fin (n + 1) → ι)) → Option E) (j : ι) :=
    y (p.1, Fin.snoc p.2 j)
  have hb : Measurable brood := by fun_prop
  have hm : (State.generationKernel (reproductionKernel Q h) n x).map brood =
      reproductionKernel Q h (Sum.inr s) := by
    rw [State.generationKernel_childFamily, hp, Kernel.optionElim_some]
  have huniq : ∀ᵐ ξ ∂reproductionKernel Q h (Sum.inr s),
      ∃! j, (ξ j).any Sum.isRight = true := by
    have hP : MeasurableSet {s | h s ≠ 0 ∧ h s ≠ ∞} :=
      (hh (MeasurableSet.singleton 0).compl).inter
        (hh (MeasurableSet.singleton ∞).compl)
    rw [reproductionKernel_distinguished Q hh]
    apply (ae_map_iff (Step.distinguishChild_measurable hP).aemeasurable
      measurableSet_unique_distinguished).mpr
    filter_upwards [ae_biasedFamilyChild_eligible Q hh s.1 s.2.1 s.2.2
      (harmonic s.1 s.2.1 s.2.2)] with z hz
    obtain ⟨v, hv, hzero, htop⟩ := hz
    have hu := Step.distinguishChild_unique (fun s => h s ≠ 0 ∧ h s ≠ ∞)
      z.1 z.2 hv ⟨hzero, htop⟩
    convert hu using 1
    ext j
    cases he : Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) z.1 z.2 j with
    | none => simp
    | some a => cases a <;> simp
  rw [← hm] at huniq
  have hu := ae_of_ae_map hb.aemeasurable huniq
  have hn : ∀ᵐ y ∂State.generationKernel (reproductionKernel Q h) n x,
      ∀ q, q ≠ p → ∀ j, (y (q.1, Fin.snoc q.2 j)).any Sum.isRight ≠ true := by
    apply ae_all_iff.mpr
    intro q
    by_cases hqp : q = p
    · filter_upwards [] with y
      intro hne
      exact False.elim (hne hqp)
    · have hhq := ae_normal_children Q (x q) (ho q hqp)
      rw [← State.generationKernel_childFamily (reproductionKernel Q h) n x q] at hhq
      have hq := ae_of_ae_map
        (show Measurable (fun next : (Unit × (Fin (n + 1) → ι)) → Option E =>
          fun j => next (q.1, Fin.snoc q.2 j)) from by fun_prop).aemeasurable hhq
      filter_upwards [hq] with y hy
      intro _
      exact hy
  have heq : distinguishedState d =ᵐ[State.generationKernel (reproductionKernel Q h) n x]
      fun y => distinguishedState d (brood y) := by
    filter_upwards [hu, hn] with y hy hyn
    obtain ⟨j, hj, hju⟩ := hy
    obtain ⟨v, hv⟩ : ∃ v, brood y j = some (Sum.inr v) := by
      cases he : brood y j with
      | none => simp [he] at hj
      | some a => cases a with
        | inl a => simp [he] at hj
        | inr v => exact ⟨v, rfl⟩
    have hbstate : distinguishedState d (brood y) = v := by
      apply distinguishedState_eq d _ j v hv
      intro k hkj hk
      exact hkj (hju k hk)
    rw [hbstate]
    apply distinguishedState_eq d y (p.1, Fin.snoc p.2 j) v hv
    intro q hq htag
    by_cases hparent : (q.1, Fin.init q.2) = p
    · have he : q = (p.1, Fin.snoc p.2 (q.2 (Fin.last n))) := by
        rw [← hparent]
        simp
      have hjq : q.2 (Fin.last n) = j := hju _ (by simpa only [brood, ← he] using htag)
      exact hq (he.trans (by rw [hjq]))
    · have hz := hyn (q.1, Fin.init q.2) hparent (q.2 (Fin.last n))
      simp only [Fin.snoc_init_self] at hz
      exact hz htag
  rw [Measure.map_congr heq]
  change (State.generationKernel (reproductionKernel Q h) n x).map
    (distinguishedState d ∘ brood) = _
  rw [← Measure.map_map (measurable_distinguishedState d) hb,
    hm, reproductionKernel_distinguished_state Q hh harmonic d s]

lemma ae_pathKernel_unique_distinguished (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    letI := reproductionKernel_isMarkovKernel Q hh harmonic
    ∀ᵐ x ∂State.pathKernel (reproductionKernel Q h) (some (Sum.inr s)),
      ∀ n, ∃! p : Unit × (Fin n → ι), (x n p).any Sum.isRight = true := by
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  have hG : MeasurableSet {x : Π n : ℕ,
      (Unit × (Fin n → ι)) → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) |
      ∀ n, ∃! p, (x n p).any Sum.isRight = true} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_unique_distinguished.preimage (measurable_pi_apply n)
  rw [← State.treeKernel_generations (reproductionKernel Q h) (some (Sum.inr s))]
  apply (ae_map_iff
    (show Measurable (fun t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      fun n (p : Unit × (Fin n → ι)) => t (List.ofFn p.2)) from by fun_prop).aemeasurable hG).mpr
  filter_upwards [ae_treeKernel_unique_spine Q hh harmonic s] with t ht
  obtain ⟨f, ⟨hf, hcarrier⟩, _⟩ := ht
  exact fun n => existsUnique_distinguished_generation t f hf hcarrier n

end ProbabilityTheory.BranchingProcess.Spine
