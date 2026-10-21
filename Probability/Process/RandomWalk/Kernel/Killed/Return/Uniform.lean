/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Return.Basic
public import Probability.Kernel.Survival.Return

/-!
# Uniform iteration bounds for killed return kernels

These estimates turn uniform one-block return mass into lower bounds for
iterated return kernels and for the ambient killed walk. They apply to every
filtered family of real interval scales and do not depend on a Mogulskii
normalization or a moment assumption.

For scale $s_i>0$, let $R_i$ be the return kernel formed from the walk killed
outside $[s_i a,s_i b]$, with return interval $[s_i c,s_i d]$ and block length
$\ell_i$. If every row of $R_i$ has mass at least $p$, then
\[
p^k\leq \operatorname{remainingMass}(R_i,k,s_i x),
\qquad
p^{\lfloor N/\ell_i\rfloor+1}
 \leq \operatorname{remainingMass}(K_i,N,s_i x),
\]
where $K_i$ is the killed-walk kernel and $x\in[c,d]$.

The public declarations in `ProbabilityTheory.RandomWalk` are:

- `eventually_pow_le_remainingMass_returnKernel_Icc_of_normalized`: a
  uniform row bound on a scaled return interval gives the corresponding power
  lower bound for repeated return blocks.
- `eventually_pow_succ_div_le_remainingMass_killedIncrementKernel_Icc`: a
  one-block return bound controls killed-walk survival for arbitrary elapsed
  time, with one additional block for the terminal remainder.
- `eventually_natCast_mul_log_le_log_remainingMass_killedIncrementKernel_Icc`:
  the same arbitrary-time bound in extended-real logarithmic form.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A normalized uniform return estimate supplies the row bound needed to
iterate the scaled return kernel from every state in its actual subtype. -/
theorem eventually_pow_le_remainingMass_returnKernel_Icc_of_normalized
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (outerLower outerUpper returnLower returnUpper : ℝ)
    (scale : ι → ℝ) (length iterations : ι → ℕ) (lowerBound : ENNReal)
    (hscale : ∀ i, 0 < scale i)
    (hblock : ∀ᶠ i in l, ∀ x : Set.Icc returnLower returnUpper,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale i * outerLower) (scale i * outerUpper)) measurableSet_Icc
        (Set.Icc (scale i * returnLower) (scale i * returnUpper)) measurableSet_Icc
        (length i)
        ⟨scale i * x, by
          constructor <;> nlinarith [x.property.1, x.property.2,
            hscale i]⟩ univ) :
    ∀ᶠ i in l,
      ∀ x : Set.Icc (scale i * returnLower) (scale i * returnUpper),
        lowerBound ^ iterations i ≤ Kernel.remainingMass
          (returnKernel ν
            (Set.Icc (scale i * outerLower) (scale i * outerUpper)) measurableSet_Icc
            (Set.Icc (scale i * returnLower) (scale i * returnUpper)) measurableSet_Icc
            (length i)) (iterations i) x := by
  filter_upwards [hblock] with i hi
  intro x
  apply pow_le_remainingMass_returnKernel
  intro state
  let normalized : Set.Icc returnLower returnUpper :=
    ⟨(state : ℝ) / scale i, by
      constructor
      · exact (le_div_iff₀ (hscale i)).2
          (by simpa [mul_comm] using state.property.1)
      · exact (div_le_iff₀ (hscale i)).2
          (by simpa [mul_comm] using state.property.2)⟩
  have hrow := hi normalized
  have hstate : state =
      (⟨scale i * normalized, by
        constructor <;> nlinarith [normalized.property.1,
          normalized.property.2, hscale i]⟩ :
        Set.Icc (scale i * returnLower) (scale i * returnUpper)) := by
    apply Subtype.ext
    dsimp [normalized]
    field_simp [(hscale i).ne']
  rw [hstate]
  exact hrow

/-- A normalized uniform return estimate controls ambient killed-walk
survival for every total duration.  The exponent contains one additional
return block, which covers the incomplete final part of the duration. -/
theorem eventually_pow_succ_div_le_remainingMass_killedIncrementKernel_Icc
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (outerLower outerUpper returnLower returnUpper : ℝ)
    (scale : ι → ℝ) (length total : ι → ℕ) (lowerBound : ENNReal)
    (hscale : ∀ i, 0 < scale i)
    (hlength : ∀ᶠ i in l, 0 < length i)
    (hblock : ∀ᶠ i in l, ∀ x : Set.Icc returnLower returnUpper,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale i * outerLower) (scale i * outerUpper)) measurableSet_Icc
        (Set.Icc (scale i * returnLower) (scale i * returnUpper)) measurableSet_Icc
        (length i)
        ⟨scale i * x, by
          constructor <;> nlinarith [x.property.1, x.property.2,
            hscale i]⟩ univ) :
    ∀ᶠ i in l,
      ∀ x : Set.Icc (scale i * returnLower) (scale i * returnUpper),
        lowerBound ^ (total i / length i + 1) ≤ Kernel.remainingMass
          (killedIncrementKernel ν
            (Set.Icc (scale i * outerLower) (scale i * outerUpper))
            measurableSet_Icc) (total i) x := by
  filter_upwards [hlength, hblock] with i hlengthPos hi
  intro x
  apply Kernel.pow_succ_div_le_remainingMass_of_returnKernel
    (killedIncrementKernel ν
      (Set.Icc (scale i * outerLower) (scale i * outerUpper)) measurableSet_Icc)
    (Set.Icc (scale i * returnLower) (scale i * returnUpper))
    measurableSet_Icc hlengthPos (total i) x lowerBound
  intro state
  let normalized : Set.Icc returnLower returnUpper :=
    ⟨(state : ℝ) / scale i, by
      constructor
      · exact (le_div_iff₀ (hscale i)).2
          (by simpa [mul_comm] using state.property.1)
      · exact (div_le_iff₀ (hscale i)).2
          (by simpa [mul_comm] using state.property.2)⟩
  have hrow := hi normalized
  have hstate : state =
      (⟨scale i * normalized, by
        constructor <;> nlinarith [normalized.property.1,
          normalized.property.2, hscale i]⟩ :
        Set.Icc (scale i * returnLower) (scale i * returnUpper)) := by
    apply Subtype.ext
    dsimp [normalized]
    field_simp [(hscale i).ne']
  rw [hstate]
  exact hrow

/-- Extended-real logarithmic form of the uniform arbitrary-duration killed
survival estimate. -/
theorem eventually_natCast_mul_log_le_log_remainingMass_killedIncrementKernel_Icc
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (outerLower outerUpper returnLower returnUpper : ℝ)
    (scale : ι → ℝ) (length total : ι → ℕ) (lowerBound : ENNReal)
    (hscale : ∀ i, 0 < scale i)
    (hlength : ∀ᶠ i in l, 0 < length i)
    (hblock : ∀ᶠ i in l, ∀ x : Set.Icc returnLower returnUpper,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale i * outerLower) (scale i * outerUpper)) measurableSet_Icc
        (Set.Icc (scale i * returnLower) (scale i * returnUpper)) measurableSet_Icc
        (length i)
        ⟨scale i * x, by
          constructor <;> nlinarith [x.property.1, x.property.2,
            hscale i]⟩ univ) :
    ∀ᶠ i in l,
      ∀ x : Set.Icc (scale i * returnLower) (scale i * returnUpper),
        ((total i / length i + 1 : ℕ) : EReal) * ENNReal.log lowerBound ≤
          ENNReal.log (Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale i * outerLower) (scale i * outerUpper))
              measurableSet_Icc) (total i) x) := by
  have hprobability :=
    eventually_pow_succ_div_le_remainingMass_killedIncrementKernel_Icc
      ν outerLower outerUpper returnLower returnUpper scale length total
      lowerBound hscale hlength hblock
  filter_upwards [hprobability] with i hi
  intro x
  rw [← ENNReal.log_pow]
  exact ENNReal.log_monotone (hi x)

end ProbabilityTheory.RandomWalk
