module

public import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Return.Comparison
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Return

/-!
# Uniform Mogulskii bounds for return kernels

Finite reference estimates in corridors shrunken by a common margin are
transferred to every starting point of the return interval.  The resulting
uniform one-block estimate can then be iterated by the sub-Markov return
kernel.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A finite collection of Gaussian return estimates, all using the same
block scale and error, yields an eventual return-kernel lower bound uniform
over the full normalized return interval. -/
theorem eventually_uniform_returnKernel_of_finset_gaussianProduct
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscaleNonneg : ∀ n, 0 ≤ scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {outerLower outerUpper returnLower returnUpper coverMargin : ℝ}
    {endpointMargin blockRadius error : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (herror : 0 < error)
    (references : Finset ℝ) (target : ℝ → ℕ → ℝ)
    (hcover : ∀ x ∈ Set.Icc returnLower returnUpper,
      ∃ y ∈ references, |x - y| ≤ coverMargin)
    (hreference : ∀ y ∈ references,
      y ∈ Set.Icc (returnLower + coverMargin)
        (returnUpper - coverMargin))
    (houter : ∀ y ∈ references,
      y ∈ Set.Icc (outerLower + coverMargin)
        (outerUpper - coverMargin))
    (hstartMargin : ∀ y ∈ references, ∀ k < blocks,
      outerLower + coverMargin - y + endpointMargin +
            (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target y j ∧
        ∑ j ∈ Finset.range k, target y j <
          outerUpper - coverMargin - y - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hfinalMargin : ∀ y ∈ references,
      returnLower + coverMargin - y + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range blocks, target y j ∧
        ∑ j ∈ Finset.range blocks, target y j <
          returnUpper - coverMargin - y -
            (blocks : ℝ) * blockRadius)
    (lowerBound : ENNReal)
    (hgap : ∀ y ∈ references,
      lowerBound + ENNReal.ofReal
          (blocks * (constant / endpointMargin ^ 2 + error)) <
        ∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target y j - blockRadius) / Real.sqrt constant)
              ((target y j + blockRadius) / Real.sqrt constant))) :
    ∀ᶠ n in atTop, ∀ x : Set.Icc returnLower returnUpper,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale n * outerLower) (scale n * outerUpper)) measurableSet_Icc
        (Set.Icc (scale n * returnLower) (scale n * returnUpper)) measurableSet_Icc
        (blocks * diffusiveBlockLength constant scale n)
        ⟨scale n * x, by
          constructor <;> nlinarith [x.property.1, x.property.2,
            hscaleNonneg n]⟩ univ := by
  let errorMass := ENNReal.ofReal
    (blocks * (constant / endpointMargin ^ 2 + error))
  let referenceBound : ℝ → ENNReal := fun y => ∏ j : Fin blocks,
    gaussianReal 0 1
      (Set.Ioo
        ((target y j - blockRadius) / Real.sqrt constant)
        ((target y j + blockRadius) / Real.sqrt constant))
  have hliminf : ∀ (y : ℝ) (hy : y ∈ references),
      referenceBound y ≤ atTop.liminf (fun n =>
        returnKernel ν
          (Set.Icc (scale n * (outerLower + coverMargin))
            (scale n * (outerUpper - coverMargin))) measurableSet_Icc
          (Set.Icc (scale n * (returnLower + coverMargin))
            (scale n * (returnUpper - coverMargin))) measurableSet_Icc
          (blocks * diffusiveBlockLength constant scale n)
          ⟨scale n * y, by
            constructor <;> nlinarith [(hreference y hy).1,
              (hreference y hy).2, hscaleNonneg n]⟩ univ + errorMass) := by
    intro y hy
    simpa only [referenceBound, errorMass] using
      (gaussianProduct_le_liminf_returnKernel_add
        ν hν hscale hscaleNonneg hconstant hblocks
        (houter y hy) (hreference y hy) hendpointMargin hblockRadius herror
        (target y) (hstartMargin y hy) (hfinalMargin y hy))
  exact eventually_forall_le_returnKernel_Icc_apply_univ_of_finset_liminf
    ν outerLower outerUpper returnLower returnUpper coverMargin references
    scale (fun n => blocks * diffusiveBlockLength constant scale n)
    lowerBound errorMass referenceBound ENNReal.ofReal_ne_top hscaleNonneg
    hcover hreference hliminf (by
      intro y hy
      simpa only [referenceBound, errorMass] using hgap y hy)

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
