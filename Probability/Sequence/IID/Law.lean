/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID.Basic
public import MeasureTheory.Measure.Convolution.Power
public import Mathlib.Probability.HasLaw
import MeasureTheory.Measure.CharacteristicFunction.Convolution
import Probability.Sequence.IID.CharacteristicFunction

/-!
# Laws of independent sequences and their finite sums

## Public declarations

- `ProbabilityTheory.iIndepFun.hasLaw_iidSequenceLaw`: if each $X_n$ has law
  $\nu$ and $(X_n)_{n\in\mathbb N}$ is independent and measurable, then the
  sequence map $\omega\mapsto(X_n(\omega))_{n\in\mathbb N}$ has law
  $\nu^{\mathbb N}=\texttt{iidSequenceLaw}\,\nu$.
- `ProbabilityTheory.iidSequenceLaw_map_sum_range_eq_convPower`: for a real
  probability measure $\nu$ and $n\in\mathbb N$, the sum of the first $n$
  canonical coordinates has law $\nu^{*n}$:
  \[
    \operatorname{Law}\!\left(\sum_{k<n}X_k\right)
      =\nu^{*n},\qquad (X_k)_{k\ge0}\sim\texttt{iidSequenceLaw}\,\nu.
  \]
The sequence-law proof applies Mathlib's `iIndepFun.map_fun_eq_infinitePi_map`
and `HasLaw.map_eq`; the finite-sum identity combines the characteristic
function formula for IID sums with Mathlib's uniqueness theorem for
characteristic functions.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- An independent measurable sequence of random variables with common law
`ν` has pushforward law `iidSequenceLaw ν`. -/
theorem iIndepFun.hasLaw_iidSequenceLaw
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} {ν : Measure X}
    {coordinate : ℕ → Ω → X}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ n, Measurable (coordinate n))
    (hlaw : ∀ n, HasLaw (coordinate n) ν P) :
    HasLaw (fun ω n => coordinate n ω) (iidSequenceLaw ν) P := by
  refine ⟨(measurable_pi_iff.mpr hmeasurable).aemeasurable, ?_⟩
  change P.map (fun ω n => coordinate n ω) =
    Measure.infinitePi (fun _ : ℕ => ν)
  rw [hindep.map_fun_eq_infinitePi_map hmeasurable]
  congr 1
  funext n
  exact (hlaw n).map_eq

/-- The sum of the first `n` coordinates of the canonical i.i.d. sequence
has the `n`-fold convolution power of its common law. -/
theorem iidSequenceLaw_map_sum_range_eq_convPower
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (n : ℕ) :
    (iidSequenceLaw ν).map
      (fun sequence : ℕ → ℝ => ∑ k ∈ Finset.range n, sequence k) =
        MeasureTheory.Measure.convPower ν n := by
  apply Measure.ext_of_charFun
  ext t
  rw [iidSequenceLaw_charFun_sum, Measure.charFun_convPower]

end ProbabilityTheory

end
