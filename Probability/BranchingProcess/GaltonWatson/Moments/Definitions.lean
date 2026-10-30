/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.GaltonWatson.Generation

/-!
# Finite-slot Galton--Watson moment quantities

## Public declarations

- `offspringSlotWeight μ i` is the probability that child slot $i$ is present.
- `generationFirstMoment μ n` and `generationSecondMoment μ n` are the extended
  first and second moments $\mathbb E[Z_n]$ and $\mathbb E[Z_n^2]$ under the
  actual Galton--Watson process law.
- `generationSizeReal n β` is the real-valued generation-size observation.
- `offspringSlotPairWeight μ i j` is the probability that both indicated
  slots are present; `offspringMean μ` and
  `offspringSecondFactorialMoment μ` are respectively $\sum_i p_i$ and
  $\sum_{i\ne j}q_{ij}$.

The moment recurrences and applications are in `FirstMoment`, `SecondMoment`,
and `PaleyZygmund`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

noncomputable def offspringSlotWeight {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i : ι) : ℝ≥0∞ :=
  by
    classical
    exact ∫⁻ ξ : Combinatorics.Branching.Step ι PUnit.{1},
      (if Combinatorics.Branching.survive ξ i then 1 else 0) ∂(μ : Measure _)
/-- The first moment of a generation under the actual presampled
Galton--Watson law. -/
noncomputable def generationFirstMoment {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ β : Combinatorics.Branching.Process ι,
    ENat.toENNReal (β.generationSize n) ∂(law μ : Measure _)

/-- The second moment of a generation under the actual presampled
Galton--Watson law. -/
noncomputable def generationSecondMoment {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ β : Combinatorics.Branching.Process ι,
    ENat.toENNReal (β.generationSize n) ^ 2 ∂(law μ : Measure _)

/-- The real-valued generation-size observation. For a finite slot type every
generation is finite, so the `toReal` conversion agrees with its usual natural
number value. -/
noncomputable def generationSizeReal {ι : Type*}
    (n : ℕ) (β : Combinatorics.Branching.Process ι) : ℝ :=
  (ENat.toENNReal (β.generationSize n)).toReal
/-- A root-slot pair has this weight in the second-moment expansion. On the
diagonal this is the probability the slot is present; off the diagonal it is
the probability both slots are present. -/
noncomputable def offspringSlotPairWeight {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) (i j : ι) : ℝ≥0∞ :=
  by
    classical
    exact ∫⁻ ξ : Combinatorics.Branching.Step ι PUnit.{1},
      (if Combinatorics.Branching.survive ξ i then 1 else 0) *
        (if Combinatorics.Branching.survive ξ j then 1 else 0) ∂(μ : Measure _)

/-- Mean offspring number in a finite-slot configuration law, expressed as
the sum of its child-slot presence probabilities. -/
noncomputable def offspringMean {ι : Type*} [Fintype ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : ℝ≥0∞ :=
  ∑ i, offspringSlotWeight μ i

/-- Second factorial moment of the number of present offspring slots. -/
noncomputable def offspringSecondFactorialMoment {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
      ι PUnit.{1}) : ℝ≥0∞ :=
  ∑ i, ∑ j, if i = j then 0 else offspringSlotPairWeight μ i j

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
