/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Step.Noise.Restriction
public import Probability.Kernel.Step.Endpoint
public import Probability.Sequence.Maximal.QuadraticTail

/-!
# Uniform finite transitions under weak-tail noise restrictions

## Public declarations

* `ProbabilityTheory.Kernel.eventually_pow_restrictNoise_ge`: if `Lₙ→∞`,
  `mₙ≤CLₙ²` eventually and `t²ν(mark>t)→0`, then for `α,p>0`, eventually
  `Kʳ(x,A)≥p ⇒ K_restrictedʳ(x,A)≥p/2` simultaneously for all `r≤mₙ`,
  states `x` and measurable targets `A`. The restricted step rejects noise
  values with `mark>αLₙ` and otherwise keeps the original update.

No independence between the mark and update is required. The proof reuses
`eventually_measureReal_inter_marks_ge` and the native partial-step endpoint
law. This is the zero-tail-constant local-block argument in B. Mallein,
*Necessary and sufficient conditions for the convergence of the consistent
maximal displacement of the branching random walk*, §2.2, Theorem 2.3 and
proof of Lemma 2.5, arXiv:1510.00602v2.
-/

@[expose] public section
namespace ProbabilityTheory.Kernel
open MeasureTheory Filter
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

/-- Uniform mark retention for all shorter transition times and measurable
terminal sets. The mark restriction keeps the original joint noise law. -/
theorem eventually_pow_restrictNoise_ge
    {S E : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (step : ℕ → S → E → Option S)
    (hs : ∀ n, Measurable (Function.uncurry (step n)))
    {mark : E → ℝ} (hm : Measurable mark)
    (htail : HasVanishingQuadraticTail ν mark)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {length : ℕ → ℕ} {C α p : ℝ} (hα : 0 < α) (hp : 0 < p)
    (hlength : ∀ᶠ n in atTop, (length n : ℝ) ≤ C * scale n ^ 2) :
    ∀ᶠ n in atTop, ∀ m ≤ length n, ∀ x : S, ∀ target : Set S,
      MeasurableSet target →
      p ≤ ((ofPartialStep ν (step n) (hs n) ^ m) x target).toReal →
      ENNReal.ofReal (p / 2) ≤
        (ofPartialStep ν
          (restrictNoise (step n) {z | mark z ≤ α * scale n})
          (measurable_restrictNoise (step n) (hs n)
            (measurableSet_le hm measurable_const)) ^ m) x target := by
  have hmark (j : ℕ) : HasLaw (fun ω : ℕ → E => mark (ω j))
      (ν.map mark) (iidSequenceLaw ν) := by
    constructor
    · exact (hm.comp (measurable_pi_apply j)).aemeasurable
    · rw [show (fun ω : ℕ → E => mark (ω j)) = mark ∘ (fun ω => ω j) from rfl,
        ← Measure.map_map hm (measurable_pi_apply j), iidSequenceLaw_map_apply]
  have ht : HasVanishingQuadraticTail (ν.map mark) id :=
    (hasVanishingQuadraticTail_map_iff mark hm id measurable_id).2 htail
  have hretain := eventually_measureReal_inter_marks_ge hmark ht hscale hα hp hlength
  filter_upwards [hretain] with n hn
  intro m hmn x target htarget hmass
  rw [pow_apply_ofPartialStep_eq_iidSequenceLaw ν (step n) (hs n) htarget] at hmass
  have h := hn {ω | EndsInPrefix (step n) target m x ω} hmass
  rw [pow_apply_ofPartialStep_eq_iidSequenceLaw ν _ _ htarget]
  have he : {ω | EndsInPrefix
      (restrictNoise (step n) {z | mark z ≤ α * scale n}) target m x ω} =
      {ω | EndsInPrefix (step n) target m x ω ∧
        ∀ j < m, mark (ω j) ≤ α * scale n} := by
    ext ω
    exact endsInPrefix_restrictNoise_iff _ _ _ _ _ _
  rw [he, ← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  refine h.trans (measureReal_mono ?_)
  rintro ω ⟨hw, hmarks⟩
  exact ⟨hw, fun j hj => hmarks j (hj.trans_le hmn)⟩

end ProbabilityTheory.Kernel
