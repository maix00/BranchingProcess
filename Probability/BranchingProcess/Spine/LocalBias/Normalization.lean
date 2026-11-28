/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.LocalBias.Basic

/-!
# State-dependent normalization of child weights

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine.LocalBias`:

* `weighted_isAdmissible` derives admissibility of `h(child)/a(s)` when
  `Mh(s)=a(s)` is finite positive on `D={0<h<∞}`.
* `normalizedWeight_isAdmissible` takes `a=Mh`, requiring only finite positive
  local means on `D`, with no harmonic or eigenfunction identity.
* `ofWeight_isAdmissible` specializes to `Mh=h`; the proof calls
  `weighted_isAdmissible` and does not duplicate normalization or support.

These specialize the local family/child change of law
in Zhan Shi, *Branching Random Walks* (2015), Theorem 4.3, (4.12)–(4.13),
DOI 10.1007/978-3-319-25372-5. No separate tree law is constructed.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

/-- A finite positive local normalizer supplies unit mass and eligible-child support. -/
theorem weighted_isAdmissible {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h normalizer : S → ℝ≥0∞} (hh : Measurable h) (ha : Measurable normalizer)
    (hmean : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = normalizer s)
    (hzero : ∀ s, h s ≠ 0 → h s ≠ ∞ → normalizer s ≠ 0)
    (htop : ∀ s, h s ≠ 0 → h s ≠ ∞ → normalizer s ≠ ∞) :
    (weighted (ι := ι) h normalizer).IsAdmissible Q := by
  have hm (i : ι) : Measurable (fun ξ : Step ι S => (ξ i).elim 0 h) :=
    (measurable_option_elim 0 hh).comp (measurable_pi_apply i)
  refine ⟨(hh (MeasurableSet.singleton 0).compl).inter
    (hh (MeasurableSet.singleton ∞).compl), ?_, ?_, ?_⟩
  · intro i
    exact ((hm i).comp measurable_snd).div (ha.comp measurable_fst)
  · intro s hs
    change (∫⁻ ξ, ∑' i, (ξ i).elim 0 h / normalizer s ∂Q s) = 1
    simp only [div_eq_mul_inv]
    simp_rw [ENNReal.tsum_mul_right]
    rw [lintegral_mul_const _ (Measurable.tsum hm), hmean s hs.1 hs.2,
      ENNReal.mul_inv_cancel (hzero s hs.1 hs.2) (htop s hs.1 hs.2)]
  · intro s hs
    have hf : ∀ᵐ ξ ∂Q s, (∑' i, (ξ i).elim 0 h) ≠ ∞ :=
      (ae_lt_top (Measurable.tsum hm) ((hmean s hs.1 hs.2).trans_ne (htop s hs.1 hs.2))).mono
        (fun _ ht => ht.ne)
    filter_upwards [hf] with ξ hξ
    intro i hi
    change (ξ i).elim 0 h / normalizer s ≠ 0 at hi
    cases he : ξ i with
    | none => simp [he] at hi
    | some t =>
      refine ⟨t, rfl, ?_, ?_⟩
      · intro hz
        apply hi
        simp [he, hz]
      · have hle := le_tsum (fun j => (ξ j).elim 0 h) i
        simp only [he, Option.elim_some] at hle
        exact ne_top_of_le_ne_top hξ hle

/-- A finite positive local mean normalizes the bias, without an eigenfunction assumption. -/
theorem normalizedWeight_isAdmissible {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (hmean : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) ≠ 0 ∧
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) ≠ ∞) :
    (normalizedWeight Q h).IsAdmissible Q := by
  have hm : Measurable (fun ξ : Step ι S => ∑' i, (ξ i).elim 0 h) :=
    Measurable.tsum fun i => (measurable_option_elim 0 hh).comp (measurable_pi_apply i)
  exact weighted_isAdmissible Q hh hm.lintegral_kernel (fun _ _ _ => rfl)
    (fun s hs ht => (hmean s hs ht).1) (fun s hs ht => (hmean s hs ht).2)

/-- Harmonic bias is a specialization of the state-dependent normalization theorem. -/
theorem ofWeight_isAdmissible {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι]
    (Q : Kernel S (Step ι S)) [IsSFiniteKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) :
    (ofWeight (ι := ι) h).IsAdmissible Q :=
  weighted_isAdmissible Q hh hh harmonic (fun _ hs _ => hs) (fun _ _ ht => ht)

end ProbabilityTheory.BranchingProcess.Spine.LocalBias
