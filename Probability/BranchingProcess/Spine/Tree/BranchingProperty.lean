/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Descendants.Disintegration
public import Probability.BranchingProcess.Spine.Tree.Construction

/-!
# Recursive branching at a fixed first spine child

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `lintegral_treeKernel_fixedChild_subtrees` proves
  `E[1_{w₁=i} g(ξ,(Tⱼ)ⱼ)] = E_Q[s][h(ξᵢ)/h(s) E[g(ξ,(Tⱼ)ⱼ) | ξ,w₁=i]]`.
  The inner law is the product of canonical tree laws started at
  `distinguishChild {0<h<∞} ξ i`: ordinary children remain ordinary and the
  eligible chosen child is distinguished. The descendant trees retain their
  role tags, so later spine events can enter `g`.

This is the recursive split along the first edge of the fixed ancestral path
in Zhan Shi, *Branching Random Walks* (2015), §4.5, proof of Theorem 4.3
between (4.12) and (4.13),
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
It is derived from the canonical whole-tree disintegration and the existing
joint family/child bias. No independent auxiliary tree law is defined.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

/-- Keep the first spine index while disintegrating all complete child subtrees.
This is the first-edge recursive split in Zhan Shi, *Branching Random Walks*
(2015), §4.5, proof of Theorem 4.3 between (4.12) and (4.13). -/
theorem lintegral_treeKernel_fixedChild_subtrees {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (i : ι)
    {g : Step ι S × (ι → List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞})) → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ t, if (t [i]).any Sum.isRight = true then
      g (Step.map (Sum.elim id Subtype.val) (fun j => t [j]), fun j u => t (j :: u))
      else 0 ∂treeKernel Q hh harmonic (some (Sum.inr s))) =
      ∫⁻ ξ, ((ξ i).elim 0 h / h s) *
        ∫⁻ trees, g (ξ, trees) ∂Measure.infinitePi (fun j =>
          treeKernel Q hh harmonic
            (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) ξ i j)) ∂Q s := by
  classical
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  let κ : Kernel (Step ι E) (ι → List ι → Option E) :=
    Kernel.infinitePi (fun j => (treeKernel Q hh harmonic).comap
      (fun ξ : Step ι E => ξ j) (measurable_pi_apply j))
  have herase : Measurable (Step.map (ι := ι)
      (Sum.elim id (Subtype.val : {s // h s ≠ 0 ∧ h s ≠ ∞} → S))) :=
    Step.map_measurable (measurable_id.sumElim measurable_subtype_coe)
  have hbase : Measurable (fun p : Step ι E × (ι → List ι → Option E) =>
      g (Step.map (Sum.elim id Subtype.val) p.1, p.2)) :=
    hg.comp ((herase.comp measurable_fst).prodMk measurable_snd)
  let A (ξ : Step ι E) := ∫⁻ trees,
    g (Step.map (Sum.elim id Subtype.val) ξ, trees) ∂κ ξ
  have hA : Measurable A := hbase.lintegral_kernel_prod_right'
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false
      (show Measurable (Sum.isRight : E → Bool) from
        measurable_const.sumElim measurable_const)
  have hB : MeasurableSet {ξ : Step ι E | (ξ i).any Sum.isRight = true} :=
    (MeasurableSet.singleton true).preimage (htag.comp (measurable_pi_apply i))
  let G (p : Step ι E × (ι → List ι → Option E)) :=
    if (p.1 i).any Sum.isRight = true then
      g (Step.map (Sum.elim id Subtype.val) p.1, p.2) else 0
  have hG : Measurable G := hbase.ite (hB.preimage measurable_fst) measurable_const
  have houter : Measurable (fun ξ : Step ι E =>
      if (ξ i).any Sum.isRight = true then A ξ else 0) := hA.ite hB measurable_const
  have hP : MeasurableSet {s | h s ≠ 0 ∧ h s ≠ ∞} :=
    (hh (MeasurableSet.singleton 0).compl).inter (hh (MeasurableSet.singleton ∞).compl)
  have hfixed : Measurable (fun p : Step ι S × ι =>
      A (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 i)) :=
    hA.comp ((Step.distinguishChild_measurable hP).comp
      (measurable_fst.prodMk measurable_const))
  have hindex : Measurable (fun p : Step ι S × ι => if p.2 = i then
      A (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 i) else 0) :=
    hfixed.ite ((MeasurableSet.singleton i).preimage measurable_snd) measurable_const
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  have hsplit : (treeKernel Q hh harmonic (some (Sum.inr s))).map
      (fun t => ((fun j => t [j]), fun j (u : List ι) => t (j :: u))) =
      reproductionKernel Q h (Sum.inr s) ⊗ₘ κ :=
    State.treeKernel_children_subtrees (reproductionKernel Q h) (some (Sum.inr s))
  calc
    _ = ∫⁻ p, G p ∂reproductionKernel Q h (Sum.inr s) ⊗ₘ κ := by
      have hm := lintegral_map hG (show Measurable
        (fun t : List ι → Option E => ((fun j => t [j]), fun j u => t (j :: u))) from
          by fun_prop) (μ := treeKernel Q hh harmonic (some (Sum.inr s)))
      rw [hsplit] at hm
      exact hm.symm
    _ = ∫⁻ ξ, (if (ξ i).any Sum.isRight = true then A ξ else 0)
        ∂reproductionKernel Q h (Sum.inr s) := by
      rw [Measure.lintegral_compProd hG]
      apply lintegral_congr
      intro ξ
      by_cases hi : (ξ i).any Sum.isRight = true
      · simp only [G, ite_eq_left hi]
        rfl
      · simp only [G, ite_eq_right hi]
        exact lintegral_zero
    _ = ∫⁻ p, (if (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2 i).any
        Sum.isRight = true then
        A (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 p.2) else 0)
        ∂biasedFamilyChild Q h s := by
      rw [reproductionKernel_distinguished Q hh,
        lintegral_map houter (Step.distinguishChild_measurable hP)]
    _ = ∫⁻ p, (if p.2 = i then
        A (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) p.1 i) else 0)
        ∂biasedFamilyChild Q h s := by
      apply lintegral_congr_ae
      filter_upwards [ae_biasedFamilyChild_eligible Q hh s.1 s.2.1 s.2.2
        (harmonic s.1 s.2.1 s.2.2)] with p hp
      obtain ⟨t, ht, hz, hfin⟩ := hp
      by_cases hi : p.2 = i
      · rw [← hi, Step.distinguishChild_selected _ _ _ ht ⟨hz, hfin⟩]
        simp
      · rw [Step.distinguishChild_other _ _ _ _ (Ne.symm hi)]
        cases p.1 i <;> simp [hi]
    _ = ∫⁻ ξ, ((ξ i).elim 0 h / h s) *
        A (Step.distinguishChild (fun s => h s ≠ 0 ∧ h s ≠ ∞) ξ i) ∂Q s := by
      rw [lintegral_biasedFamilyChild Q hh hindex, tsum_eq_single i]
      · simp
      · intro j hji
        simp [hji]
    _ = _ := by
      apply lintegral_congr
      intro ξ
      congr 1
      dsimp only [A]
      rw [Step.distinguishChild_map]
      rfl

end ProbabilityTheory.BranchingProcess.Spine

end
