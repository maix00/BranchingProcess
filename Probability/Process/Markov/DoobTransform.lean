/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.DoobTransform.Restriction
public import Probability.Process.Markov.Trajectory

/-!
# The Markov process on the eligible region of a Doob transform

## Public declarations

* `ProbabilityTheory.Kernel.doobTransformOnPositive_isMarkovChain`:
  if the measurable weight satisfies `K h = h` on `E = {0 < h < ∞}`,
  the native Ionescu--Tulcea coordinate process on `E`, started at any
  `x ∈ E`, is Markov with kernel `Kʰ|E` and its natural filtration.
  Its `m`-to-`n` conditional transition is `(Kʰ|E)^(n-m)`.

This is a specialization of the generic homogeneous Markov realization;
no second probability space or trajectory recursion is introduced.
For the Doob kernel see Zhan Shi, *Branching Random Walks*, LNM 2151
(2015), Chapter 4, §4.2, (4.3)–(4.4), DOI 10.1007/978-3-319-25372-5.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

/-- The normalized restriction has a complete Markov realization on eligible states. -/
theorem doobTransformOnPositive_isMarkovChain {S : Type*} [MeasurableSpace S]
    (K : Kernel S S) [IsSFiniteKernel K] {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ x, h x ≠ 0 → h x ≠ ∞ → (∫⁻ y, h y ∂K x) = h x)
    (x : {x // h x ≠ 0 ∧ h x ≠ ∞}) :
    letI := doobTransformOnPositive_isMarkovKernel K hh harmonic
    IsMarkovChain (fun n (w : ℕ → {x // h x ≠ 0 ∧ h x ≠ ∞}) => w n)
      Filtration.piLE
      (traj (X := fun _ => {x // h x ≠ 0 ∧ h x ≠ ∞})
        (historyKernel (doobTransformOnPositive K hh)) 0 (fun _ => x))
      (doobTransformOnPositive K hh) := by
  let := doobTransformOnPositive_isMarkovKernel K hh harmonic
  exact isMarkovChain_traj_historyKernel _ x

end ProbabilityTheory.Kernel

end
