/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Probability.Distributions.CharacteristicFunction.CosineDefect

/-!
# Symmetrization of probability laws

The law of the difference of two independent copies is a standard way to
remove centering from characteristic-function arguments.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- The law of the difference of two independent variables with common law
`μ`. -/
noncomputable def symmetrizedMeasure (μ : Measure ℝ) : Measure ℝ :=
  μ ∗ μ.map (fun x : ℝ => -x)

/-- The characteristic function of the difference of two independent copies
is the squared modulus of the original characteristic function. -/
theorem charFun_symmetrizedMeasure {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (symmetrizedMeasure μ) t = (‖charFun μ t‖ ^ 2 : ℂ) := by
  have hneg : charFun (μ.map (fun x : ℝ => -x)) t = charFun μ (-t) := by
    have hmap : (fun x : ℝ => -x) = fun x => (-1 : ℝ) * x := by
      funext x
      ring_nf
    rw [hmap, charFun_map_mul, neg_one_mul]
  rw [symmetrizedMeasure, charFun_conv, hneg, charFun_neg, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  norm_cast

/-- The real part of the symmetrized characteristic function is the squared
modulus of the original one. -/
theorem charFun_symmetrizedMeasure_re {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (t : ℝ) :
    (charFun (symmetrizedMeasure μ) t).re = ‖charFun μ t‖ ^ 2 := by
  rw [charFun_symmetrizedMeasure]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- The cosine defect of the law of the difference of two iid variables is
exactly the squared-modulus defect of the original characteristic function.
The tail in a Tauberian application must therefore be taken under
`symmetrizedMeasure μ`. -/
theorem cosineDefectIntegral_symmetrizedMeasure
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cosineDefectIntegral (symmetrizedMeasure μ) t =
      1 - ‖charFun μ t‖ ^ 2 := by
  have hprob : IsProbabilityMeasure (symmetrizedMeasure μ) := by
    dsimp [symmetrizedMeasure]
    infer_instance
  rw [@cosineDefectIntegral_eq_one_sub_charFun_re _ hprob t,
    charFun_symmetrizedMeasure_re]

end ProbabilityTheory
