/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.LevyMeasure.HalfSubordinator
public import Probability.RandomMeasure.Poisson.Support

/-!
# Fixed jump lengths in the Brownian first-passage Poisson source

The public theorem in this file is:

- `ProbabilityTheory.IsPoissonPointFamily.ae_no_brownianFirstPassage_mark`:
  for the Poisson intensity $dt\,\nu(du)$ with Brownian first-passage
  Lévy measure $\nu$, almost surely $N([0,1]\times\{a\})=0$ for every
  fixed jump length $a$.

This is the zero-atom step in the Lévy decomposition of Brownian
first-passage times cited in Erwin Bolthausen, *On a functional central
limit theorem for random walks conditioned to stay positive*,
Lemma 2.3, equation (2.2), Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098, referring to Kiyosi Itô and Henry P.
McKean, *Diffusion Processes and Their Sample Paths* (1965), §1.7.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- A Poisson realization of the Brownian first-passage Lévy intensity
has no point of any prescribed jump length. -/
theorem IsPoissonPointFamily.ae_no_brownianFirstPassage_mark
    {Ω : Type} [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → unitInterval × ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X
      ((volume : Measure unitInterval).prod
        brownianFirstPassageLevyMeasure) P)
    (a : ℝ) :
    ∀ᵐ ω ∂P,
      poissonRandomMeasure K X ω (Set.univ ×ˢ {a}) = 0 := by
  exact hd.ae_no_mark_at_value a
    (brownianFirstPassageLevyMeasure_singleton a)

end ProbabilityTheory

end
