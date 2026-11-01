/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Skorokhod.Basic
public import Mathlib.Topology.UnitInterval
public import Probability.Sequence.IID.Basic

/-!
# Laws of normalized random-walk paths in Skorokhod space

This file places the deterministic normalized step path under the canonical
i.i.d. increment law.  Its measurability uses the verified Skorokhod topology,
not the product measurable structure on an ambient function space.

## Public declarations

* `normalizedStepPathLaw ν scale n` is the image of `iidSequenceLaw ν` under
  `normalizedStepCadlagPathIcc scale n`; it is a probability measure when `ν`
  is.
* `hasLaw_normalizedStepCadlagPathIcc` states that the normalized step-path
  map has law `normalizedStepPathLaw ν scale n` under `iidSequenceLaw ν`.

In measure notation, \(\mathcal L_\nu(X_n)=
\mathrm{map}(X_n,\mathrm{iidSequenceLaw}(\nu))\), where
\(X_n(\xi)(t)=c_n^{-1}S_{\lfloor nt\rfloor}(\xi)\).
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Law of the normalized `n`-step càdlàg path under i.i.d. increments. -/
noncomputable def normalizedStepPathLaw (ν : Measure ℝ)
    (scale : ℕ → ℝ) (n : ℕ) :
    Measure (CadlagPath unitInterval ℝ) :=
  (iidSequenceLaw ν).map
    (normalizedStepCadlagPathIcc scale n)

noncomputable instance normalizedStepPathLaw.instIsProbabilityMeasure
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (n : ℕ) :
    IsProbabilityMeasure (normalizedStepPathLaw ν scale n) := by
  unfold normalizedStepPathLaw
  infer_instance

theorem hasLaw_normalizedStepCadlagPathIcc
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (n : ℕ) :
    HasLaw (normalizedStepCadlagPathIcc scale n)
      (normalizedStepPathLaw ν scale n) (iidSequenceLaw ν) where
  aemeasurable := (measurable_normalizedStepCadlagPathIcc scale n).aemeasurable
  map_eq := rfl

end ProbabilityTheory.RandomWalk
