/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLaw.Process
public import Probability.Process.Stable.PathLaw.FullProcess
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic

/-!
# Stable escape rates from tight random-walk sources

Let $\nu$ be an increment law, $\mu$ a strictly $\alpha$-stable law, and
$b_n>0$ a normalization. If $\nu$ is in the domain of attraction of $\mu$,
the normalized random-walk path laws are tight, and
$0<\mathbb P_\mu(X_1\le0)<1$, then there are a unit-interval stable path law
$P$ and $C<0$ such that

$$
\mathrm{IsStableClockProcessLaw}(\alpha,\mu,\mathrm{clock},P)
\quad\text{and}\quad
\lim_{a\downarrow0}a^\alpha\log P\{f:f(0)=0,\ \operatorname{diam}f([0,1])<2a\}=C.
$$

The theorem `exists_generatedStableProcess_escapeRate_of_tightSource` composes
the tight-source stable process construction in
`Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLaw.Process` with
the path-law escape-rate transfer in
`Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer`.
The stable-process tube event and rate predicate are defined in
`Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic`.

The stable functional-limit setting is treated in P. Embrechts, C. Klüppelberg,
and T. Mikosch, *Modelling Extremal Events for Insurance and Finance*,
Stochastic Modelling and Applied Probability 33, Springer (1997), Chapter 3,
Theorem 3.4.2, DOI 10.1007/978-3-642-33483-2. The Lean theorem keeps tightness
as an explicit premise and derives the tube escape rate by composing the
repository's stable path-law construction and stable-process escape-rate
transfer; the cited functional limit theorem is the surrounding invariance
principle, not the source of the escape-rate conclusion.
## Public declarations

- `exists_generatedStableProcess_escapeRate_of_tightSource` produces a
  unit-interval stable process law $P$ and a constant $C<0$ from a tight
  stable-domain random-walk source, with
  $a^\alpha\log P\{f:f(0)=0,\ \operatorname{diam}f([0,1])<2a\}\to C$
  as $a\downarrow0$ under the stated nondegeneracy assumption.

-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- A tight source path-law subsequence yields a full-time stable Lévy process
and its unit-interval escape-rate witness. -/
theorem exists_generatedStableProcess_escapeRate_of_tightSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hStable : IsStrictlyAlphaStable α μ)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ P : ProbabilityMeasure (CadlagPath unitInterval ℝ),
      ∃ hP : IsStableClockProcessLaw α μ unitInterval.clock (P : Measure _),
        ∃ C, HasStableProcessEscapeRate α μ
          ((iidUnitPathBlockProcess_isStableLevyProcess hP).unitIntervalPathLaw :
            Measure (CadlagPath unitInterval ℝ)) C := by
  obtain ⟨P, hP, _sub, _hsub, _hconv⟩ :=
    exists_stableClockProcessLaw_of_tightSource hDOA hStable htight
  let hX := iidUnitPathBlockProcess_isStableLevyProcess hP
  obtain ⟨C, hEscape⟩ :=
    hX.isStableClockProcessLaw_unitIntervalPathLaw
      |>.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  exact ⟨P, hP, C, hEscape⟩

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
