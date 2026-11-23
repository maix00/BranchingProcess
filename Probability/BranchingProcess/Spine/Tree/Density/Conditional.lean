/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Density.FiniteGeneration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!
# Conditional location of the spine given the untyped tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `condLExp_treeKernel_fixedAddress` proves
  `P(wₙ=z | Hₙ) = W_z(Hₙ)/∑_u W_u(Hₙ)` almost surely for the canonical
  distinguished tree. Here `Hₙ = untypedHistory n`; the information includes
  the entire untyped tree through depth `n`, rather than only the spine path.
* `ae_treeKernel_totalWeight` proves `0 < ∑_u W_u(Hₙ) < ∞` almost surely
  under the changed tree law, so this conditional ratio is well-defined.

This is Zhan Shi, *Branching Random Walks* (2015), §4.4, Theorem 4.4(i),
(4.9), proved in §4.5 using (4.12), DOI 10.1007/978-3-319-25372-5.
The proof uses Mathlib's `rnDeriv_map`, `Measure.rnDeriv_restrict_self`,
and `Measure.rnDeriv_withDensity`; no separate conditional-law construction
or Radon--Nikodym implementation is introduced.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching Finset Preorder
open scoped ENNReal

/-- Shi Theorem 4.4(i), (4.9), conditioned on the full untyped finite tree. -/
theorem condLExp_treeKernel_fixedAddress {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ) (z : Fin n → ι) :
    let P := treeKernel Q hh harmonic (some (Sum.inr s))
    P⁻[(fun t => if (t (List.ofFn z)).any Sum.isRight = true then 1 else 0) |
      MeasurableSpace.comap (untypedHistory (h := h) n) inferInstance] =ᵐ[P]
      fun t => addressWeight h n z (untypedHistory n t) /
        totalWeight h n (untypedHistory n t) := by
  let P := treeKernel Q hh harmonic (some (Sum.inr s))
  let H := untypedHistory (ι := ι) (h := h) n
  let μ := (State.treeKernel Q (some s.1)).map
    (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) => t (List.ofFn p.2))
  let ν := P.map H
  let A := {t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) |
    (t (List.ofFn z)).any Sum.isRight = true}
  have hH : Measurable H := measurable_untypedHistory n
  have ht : Measurable (fun t : List ι → Option S =>
      fun k : Iic n => fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) := by fun_prop
  have hM : Measurable (totalWeight (ι := ι) h n) := measurable_totalWeight hh n
  have hw : Measurable (addressWeight h n z) := measurable_addressWeight hh n z
  have hratio : Measurable (fun x => addressWeight h n z x / totalWeight h n x) := hw.div hM
  have htag : Measurable (fun o : Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      o.any Sum.isRight) := measurable_option_elim false
        (measurable_const.sumElim measurable_const)
  have hA : MeasurableSet A := (MeasurableSet.singleton true).preimage
    (htag.comp (measurable_pi_apply _))
  have hlaw : ν = μ.withDensity (totalWeight h n) :=
    treeKernel_finiteHistory Q hh harmonic s n
  have hfixed : (P.restrict A).map H = μ.withDensity (addressWeight h n z) :=
    treeKernel_fixedAddress_measure Q hh harmonic s n z
  have hmass : (∫⁻ x, totalWeight h n x ∂μ) = 1 := by
    rw [lintegral_map hM ht]
    exact lintegral_totalWeight Q hh harmonic s n
  have hfinite : ∀ᵐ x ∂μ, totalWeight h n x ≠ ∞ :=
    (ae_lt_top hM (hmass.trans_ne (by simp))).mono (fun _ hx => hx.ne)
  have hcancel : (fun x => totalWeight h n x *
      (addressWeight h n z x / totalWeight h n x)) =ᵐ[μ] addressWeight h n z := by
    filter_upwards [hfinite] with x hx
    by_cases hzero : totalWeight h n x = 0
    · have hwzero : addressWeight h n z x = 0 := le_antisymm
        (hzero ▸ le_tsum (fun u => addressWeight h n u x) z) bot_le
      simp only [hzero, hwzero, zero_mul]
    · exact ENNReal.mul_div_cancel hzero hx
  have hdensity : ν.withDensity (fun x => addressWeight h n z x / totalWeight h n x) =
      (P.restrict A).map H := by
    rw [hlaw, ← withDensity_mul μ hM hratio, hfixed]
    exact withDensity_congr_ae hcancel
  have hRn : ((P.restrict A).map H).rnDeriv ν =ᵐ[ν]
      (fun x => addressWeight h n z x / totalWeight h n x) := by
    rw [← hdensity]
    exact Measure.rnDeriv_withDensity ν hratio
  have hmap := rnDeriv_map (Measure.absolutelyContinuous_restrict (μ := P) (s := A)) hH
  have hself := Measure.rnDeriv_restrict_self P hA
  have hconditional := condLExp_congr_ae
    (mΩ := MeasurableSpace.comap H inferInstance) hself
  have hindicator : A.indicator (1 : (List ι →
      Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞})) → ℝ≥0∞) =
      (fun t => if (t (List.ofFn z)).any Sum.isRight = true then 1 else 0) := by
    funext t
    by_cases ht : (t (List.ofFn z)).any Sum.isRight = true <;> simp [A, ht]
  rw [hindicator] at hconditional
  exact (hmap.trans hconditional).symm.trans (ae_of_ae_map hH.aemeasurable hRn)

/-- The denominator in Shi (4.9) is positive and finite under the changed tree law. -/
theorem ae_treeKernel_totalWeight {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ) :
    ∀ᵐ t ∂treeKernel Q hh harmonic (some (Sum.inr s)),
      totalWeight h n (untypedHistory n t) ≠ 0 ∧
        totalWeight h n (untypedHistory n t) ≠ ∞ := by
  let μ := (State.treeKernel Q (some s.1)).map
    (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) => t (List.ofFn p.2))
  have hM : Measurable (totalWeight (ι := ι) h n) := measurable_totalWeight hh n
  have ht : Measurable (fun t : List ι → Option S =>
      fun k : Iic n => fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) := by fun_prop
  have hmass : (∫⁻ x, totalWeight h n x ∂μ) = 1 := by
    rw [lintegral_map hM ht]
    exact lintegral_totalWeight Q hh harmonic s n
  have hf : ∀ᵐ x ∂μ, totalWeight h n x ≠ ∞ :=
    (ae_lt_top hM (hmass.trans_ne (by simp))).mono (fun _ hx => hx.ne)
  have ha : ∀ᵐ x ∂μ.withDensity (totalWeight h n),
      totalWeight h n x ≠ 0 ∧ totalWeight h n x ≠ ∞ := by
    apply (ae_withDensity_iff hM).mpr
    filter_upwards [hf] with x hx hpos
    exact ⟨hpos, hx⟩
  have hlaw := treeKernel_finiteHistory Q hh harmonic s n
  change (treeKernel Q hh harmonic (some (Sum.inr s))).map (untypedHistory n) =
    μ.withDensity (totalWeight h n) at hlaw
  rw [← hlaw] at ha
  exact ae_of_ae_map (measurable_untypedHistory n).aemeasurable ha

end ProbabilityTheory.BranchingProcess.Spine

end
