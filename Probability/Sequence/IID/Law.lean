/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID.Basic
public import Mathlib.Probability.HasLaw

/-!
# Laws of independent sequences

## Public declarations

- `ProbabilityTheory.iIndepFun.hasLaw_iidSequenceLaw`: if each $X_n$ has law
  $\nu$ and $(X_n)_{n\in\mathbb N}$ is independent and measurable, then the
  sequence map $\omega\mapsto(X_n(\omega))_{n\in\mathbb N}$ has law
  $\nu^{\mathbb N}=\texttt{iidSequenceLaw}\,\nu$.
The proof applies Mathlib's `iIndepFun.map_fun_eq_infinitePi_map` and `HasLaw.map_eq`; this module records their common-law specialization for the repository's canonical IID sequence law.
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

end ProbabilityTheory

end
