/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Step.Noise.Restriction
public import Probability.Kernel.Survival.Return.Basic
public import Probability.Sequence.Maximal.QuadraticTail

/-!
# Long-horizon survival with correlated noise restrictions

## Public declarations

* `ProbabilityTheory.Kernel.eventually_pow_le_survival_restrictNoise`:
  suppose a family of measurable partial steps has an unmarked return-block
  probability at least `p > 0`, uniformly on a measurable return set.
  If the block lengths satisfy `bₙ ≤ C Lₙ²`, `Lₙ → ∞`, and the noise mark
  has vanishing quadratic tail, then eventually, simultaneously for every
  horizon `H` and every return state `x`,
  `(p/2)^(⌊H/bₙ⌋+1) ≤ P(survive H steps from x, Bⱼ ≤ αLₙ for j<H)`.

There is no independence assumption between the mark and the state update.
The IID noise law remains unchanged. The tail estimate is applied once per
return block; the existing return-kernel theorem performs the arbitrarily
long concatenation. This is the block step in B. Mallein, *Necessary and
sufficient conditions for the convergence of the consistent maximal
displacement of the branching random walk*, §2.2, Theorem 2.3 and proof of
Lemma 2.5, arXiv:1510.00602v2, specialized to zero quadratic tail constant.
-/

@[expose] public section
namespace ProbabilityTheory.Kernel
open MeasureTheory Filter
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

/-- Diffusive-block mark retention followed by return-kernel iteration.
Unlike a full-horizon union bound, this estimate allows arbitrary `total`. -/
theorem eventually_pow_le_survival_restrictNoise
    {S E : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (step : ℕ → S → E → Option S)
    (hs : ∀ n, Measurable (Function.uncurry (step n)))
    (core : ℕ → Set S) (hc : ∀ n, MeasurableSet (core n))
    {mark : E → ℝ} (hm : Measurable mark)
    (htail : HasVanishingQuadraticTail ν mark)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {length : ℕ → ℕ} {C α p : ℝ} (hα : 0 < α) (hp : 0 < p)
    (hlength : ∀ᶠ n in atTop, (length n : ℝ) ≤ C * scale n ^ 2)
    (hpos : ∀ᶠ n in atTop, 0 < length n)
    (hrow : ∀ᶠ n in atTop, ∀ x : core n,
      p ≤ (returnKernel (ofPartialStep ν (step n) (hs n))
        (core n) (hc n) (length n) x Set.univ).toReal) :
    ∀ᶠ n in atTop, ∀ total : ℕ, ∀ x : core n,
      ENNReal.ofReal (p / 2) ^ (total / length n + 1) ≤
        iidSequenceLaw ν {ω | SurvivesPrefix (step n) total (x : S) ω ∧
          ∀ j < total, mark (ω j) ≤ α * scale n} := by
  have hmark (j : ℕ) : HasLaw (fun ω : ℕ → E => mark (ω j))
      (ν.map mark) (iidSequenceLaw ν) := by
    constructor
    · exact (hm.comp (measurable_pi_apply j)).aemeasurable
    · rw [show (fun ω : ℕ → E => mark (ω j)) = mark ∘ (fun ω => ω j) from rfl,
        ← Measure.map_map hm (measurable_pi_apply j), iidSequenceLaw_map_apply]
  have ht : HasVanishingQuadraticTail (ν.map mark) id :=
    (hasVanishingQuadraticTail_map_iff mark hm id measurable_id).2 htail
  have hretain := eventually_measureReal_inter_marks_ge hmark ht hscale hα hp hlength
  filter_upwards [hretain, hpos, hrow] with n hn hlen hrowN
  let accepted := {z : E | mark z ≤ α * scale n}
  have ha : MeasurableSet accepted := measurableSet_le hm measurable_const
  let constrained := restrictNoise (step n) accepted
  have hcon : Measurable (Function.uncurry constrained) :=
    measurable_restrictNoise (step n) (hs n) ha
  let K := ofPartialStep ν constrained hcon
  have hret : ∀ x : core n,
      ENNReal.ofReal (p / 2) ≤ returnKernel K (core n) (hc n) (length n) x Set.univ := by
    intro x
    have hx := hrowN x
    rw [returnKernel_apply_univ,
      pow_apply_ofPartialStep_eq_iidSequenceLaw ν (step n) (hs n) (hc n)] at hx
    have h := hn {ω | EndsInPrefix (step n) (core n) (length n) (x : S) ω} hx
    rw [returnKernel_apply_univ,
      pow_apply_ofPartialStep_eq_iidSequenceLaw ν constrained hcon (hc n)]
    have he : {ω | EndsInPrefix constrained (core n) (length n) (x : S) ω} =
        {ω | EndsInPrefix (step n) (core n) (length n) (x : S) ω} ∩
          {ω | ∀ j < length n, mark (ω j) ≤ α * scale n} := by
      ext ω
      exact endsInPrefix_restrictNoise_iff (step n) accepted (core n) (length n) x ω
    rw [he, ← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h
  intro total x
  have h := pow_succ_div_le_remainingMass_of_returnKernel
    K (core n) (hc n) hlen total x (ENNReal.ofReal (p / 2)) hret
  rw [remainingMass, pow_apply_univ_ofPartialStep_eq_iidSequenceLaw
    ν constrained hcon] at h
  simpa only [constrained, survivesPrefix_restrictNoise_iff, accepted,
    Set.mem_ofPred_eq] using h

end ProbabilityTheory.Kernel
