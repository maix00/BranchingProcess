/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lévy measure of the Brownian first-passage subordinator

The public declarations in this file are:

- `ProbabilityTheory.brownianFirstPassageLevyMeasure`:
  the measure with density
  $\mathbf 1_{(0,\infty)}(u)(2\pi)^{-1/2}u^{-3/2}\,du$.
- `ProbabilityTheory.brownianFirstPassageLevyMeasure_singleton`:
  $\nu(\{a\})=0$ for every real $a$.
- `ProbabilityTheory.brownianFirstPassageLevyMeasure_sigmaFinite`:
  the intensity is $\sigma$-finite.

This is the jump-length intensity in the Lévy decomposition of the
Brownian descending first-passage process cited in Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Lemma 2.3, equation (2.2), Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098, referring to Kiyosi Itô and
Henry P. McKean, *Diffusion Processes and Their Sample Paths* (1965),
§1.7. The identification of the first-passage process with this jump
intensity is a separate process-level assertion.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The positive half-stable Lévy intensity of Brownian first-passage
times, written as a density with respect to Lebesgue measure. -/
noncomputable def brownianFirstPassageLevyMeasure : Measure ℝ :=
  volume.withDensity fun u : ℝ =>
    ENNReal.ofReal (if 0 < u then (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
      u ^ (-(3 / 2 : ℝ)) else 0)

/-- The Brownian first-passage Lévy measure charges no fixed jump length. -/
theorem brownianFirstPassageLevyMeasure_singleton (a : ℝ) :
    brownianFirstPassageLevyMeasure {a} = 0 := by
  unfold brownianFirstPassageLevyMeasure
  exact measure_singleton a

/-- Finite density at every positive argument gives a σ-finite jump
intensity, despite its singularity as the argument tends to zero. -/
instance : SigmaFinite brownianFirstPassageLevyMeasure := by
  unfold brownianFirstPassageLevyMeasure
  infer_instance

theorem brownianFirstPassageLevyMeasure_sigmaFinite :
    SigmaFinite brownianFirstPassageLevyMeasure := inferInstance

end ProbabilityTheory

end
