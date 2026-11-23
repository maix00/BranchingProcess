/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Construction

/-!
# First-generation density of the distinguished tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `treeKernel_firstFamily` identifies the root's untyped offspring-family
  marginal under the canonical distinguished tree with
  `Q(s,dξ) (∑_i h(ξ_i))/h(s)`.

* `lintegral_treeKernel_firstSpineChild` gives the fixed-index identity
  `E[1_{w₁=i} g(ξ)] = E_Q(s)[h(ξ_i) g(ξ)/h(s)]` on that same tree.
  It is the first-generation case of (4.12), before summing over indices.

This is the first-generation case of Zhan Shi, *Branching Random Walks*
(2015), Chapter 4, §4.4, Theorem 4.3 and its proof,
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
The law on the left is extracted from the already constructed entire tree;
it is not a separately defined tilted family law. Here `h` is the full
reproductive weight, including Shi's exponential and region factors.
Higher-generation densities require the subsequent induction over the same law.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

/-- Erasing the first generation's role tags gives exactly its total-weight density. -/
theorem treeKernel_firstFamily {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    (treeKernel Q hh harmonic (some (Sum.inr s))).map
      (fun t => Step.map (Sum.elim id Subtype.val) (fun j => t [j])) =
      (Q s).withDensity (fun ξ => (∑' i, (ξ i).elim 0 h) / h s) := by
  let : IsMarkovKernel (reproductionKernel Q h) :=
    reproductionKernel_isMarkovKernel Q hh harmonic
  have herase : Measurable (Step.map (ι := ι)
      (Sum.elim id (Subtype.val : {s // h s ≠ 0 ∧ h s ≠ ∞} → S))) :=
    Step.map_measurable (measurable_id.sumElim measurable_subtype_coe)
  change (State.treeKernel (reproductionKernel Q h) (some (Sum.inr s))).map
    ((Step.map (Sum.elim id Subtype.val)) ∘ (fun t => fun j => t [j])) = _
  rw [← Measure.map_map herase (by fun_prop), State.treeKernel_children,
    Kernel.optionElim_some, reproductionKernel_distinguished_map Q hh,
    biasedFamily_eq_withDensity Q hh]
  apply Kernel.withDensity_apply
  exact (Measurable.tsum (fun i => (measurable_option_elim 0 hh).comp
    ((measurable_pi_apply i).comp measurable_snd))).div (hh.comp measurable_fst)

/-- The fixed first spine-child identity, before summing over child indices. -/
theorem lintegral_treeKernel_firstSpineChild {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (i : ι)
    {g : Step ι S → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t, if (t [i]).any Sum.isRight = true then
      g (Step.map (Sum.elim id Subtype.val) (fun j => t [j])) else 0
      ∂treeKernel Q hh harmonic (some (Sum.inr s))) =
      ∫⁻ ξ, ((ξ i).elim 0 h / h s) * g ξ ∂Q s := by
  classical
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  let G (ξ : Step ι E) := if (ξ i).any Sum.isRight = true then
    g (Step.map (Sum.elim id Subtype.val) ξ) else 0
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false
      (show Measurable (Sum.isRight : E → Bool) from
        measurable_const.sumElim measurable_const)
  have hG : Measurable G :=
    (hg.comp (Step.map_measurable
      (measurable_id.sumElim measurable_subtype_coe))).ite
      ((MeasurableSet.singleton true).preimage (htag.comp (measurable_pi_apply i)))
      measurable_const
  have hP : MeasurableSet {s | h s ≠ 0 ∧ h s ≠ ∞} :=
    (hh (MeasurableSet.singleton 0).compl).inter (hh (MeasurableSet.singleton ∞).compl)
  have hindex : Measurable (fun p : Step ι S × ι => if p.2 = i then g p.1 else 0) :=
    (hg.comp measurable_fst).ite
      ((MeasurableSet.singleton i).preimage measurable_snd) measurable_const
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  calc
    _ = ∫⁻ ξ, G ξ ∂reproductionKernel Q h (Sum.inr s) := by
      have hm := lintegral_map hG (show Measurable
        (fun t : List ι → Option E => fun j => t [j]) from by fun_prop)
        (μ := State.treeKernel (reproductionKernel Q h) (some (Sum.inr s)))
      rw [State.treeKernel_children, Kernel.optionElim_some] at hm
      exact hm.symm
    _ = ∫⁻ p, G (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2)
        ∂biasedFamilyChild Q h s := by
      rw [reproductionKernel_distinguished Q hh,
        lintegral_map hG (Step.distinguishChild_measurable hP)]
    _ = ∫⁻ p, (if p.2 = i then g p.1 else 0) ∂biasedFamilyChild Q h s := by
      apply lintegral_congr_ae
      filter_upwards [ae_biasedFamilyChild_eligible Q hh s.1 s.2.1 s.2.2
        (harmonic s.1 s.2.1 s.2.2)] with p hp
      obtain ⟨t, ht, hz, hfin⟩ := hp
      dsimp only [G]
      rw [Step.distinguishChild_map]
      by_cases hi : p.2 = i
      · rw [← hi, Step.distinguishChild_selected _ _ _ ht ⟨hz, hfin⟩]
        simp
      · rw [Step.distinguishChild_other _ _ _ _ (Ne.symm hi)]
        cases p.1 i <;> simp [hi]
    _ = _ := by
      rw [lintegral_biasedFamilyChild Q hh hindex]
      rw [tsum_eq_single i]
      · simp
      · intro j hji
        simp [hji]

end ProbabilityTheory.BranchingProcess.Spine

end
