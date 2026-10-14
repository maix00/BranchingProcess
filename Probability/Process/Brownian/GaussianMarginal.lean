/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Nonatomic Brownian marginals

The public theorem in this file is:

- `ProbabilityTheory.IsPreBrownianReal.ae_eval_ne`:
  for $t>0$ and $a\in\mathbb R$, $\mathbb P(B_t=a)=0$.

The Gaussian marginal fact is the final step after Lévy's reflected-process
identity in the proof of equation (2.3) of Lemma 2.3 in Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to stay
positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- A Brownian marginal at positive time avoids every prescribed real
value almost surely. -/
theorem IsPreBrownianReal.ae_eval_ne
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {t : ℝ≥0} (ht : 0 < t) (a : ℝ) :
    ∀ᵐ ω ∂P, B t ω ≠ a := by
  have hnull : NullSingletonClass (gaussianReal 0 t) :=
    nullSingletonClass_gaussianReal ht.ne'
  exact (hB.hasLaw_eval t).ae_iff
    (measurableSet_setOfPred.1 (by
      convert (measurableSet_singleton a).compl using 1
      ext x
      simp)) |>.2
    (@Measure.ae_ne ℝ _ (gaussianReal 0 t) hnull a)

end ProbabilityTheory

end
