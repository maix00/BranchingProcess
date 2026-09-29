import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Return.Partition
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Partition.Quantitative

/-!
# Finite-partition lower bounds for corridor return kernels

The finite-dimensional Gaussian endpoint estimate is combined with the
quantitative within-block error while retaining a final endpoint constraint.
The resulting event is identified with one transition of the outer-killed,
inner-return block kernel.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- With a fixed block constant and explicit tightness control, a Gaussian
block product bounds the `liminf` mass of staying in an outer interval and
returning to an inner interval at the end of the block. -/
theorem gaussianProduct_le_liminf_returnKernel_add_of_eventually_control
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscaleNonneg : ∀ n, 0 ≤ scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {outerLower outerUpper returnLower returnUpper initial : ℝ}
    (hinitialOuter : initial ∈ Set.Icc outerLower outerUpper)
    (hinitialReturn : initial ∈ Set.Icc returnLower returnUpper)
    {endpointMargin blockRadius error : ℝ}
    (hblockRadius : 0 < blockRadius)
    (target : ℕ → ℝ)
    (hstartMargin : ∀ k < blocks,
      outerLower - initial + endpointMargin +
            (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          outerUpper - initial - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hfinalMargin :
      returnLower - initial + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range blocks, target j ∧
        ∑ j ∈ Finset.range blocks, target j <
          returnUpper - initial - (blocks : ℝ) * blockRadius)
    (hcontrol : ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      ∀ final : Set (ℕ → ℝ),
      (independentIncrementLaw ν)
          ({increment | ∀ j < blocks,
            partialSum
                (j * diffusiveBlockLength constant scale n) increment /
                scale n ∈
              Set.Ioo (lower j + endpointMargin)
                (upper j - endpointMargin)} ∩ final) ≤
        (independentIncrementLaw ν)
            ({increment | ∀ j < blocks,
              ∀ k ≤ diffusiveBlockLength constant scale n,
                partialSum
                    (j * diffusiveBlockLength constant scale n + k)
                      increment ∈
                  Set.Icc (scale n * lower j)
                    (scale n * upper j)} ∩ final) +
          ENNReal.ofReal
            (blocks * (constant / endpointMargin ^ 2 + error))) :
    (∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            ((target j - blockRadius) / Real.sqrt constant)
            ((target j + blockRadius) / Real.sqrt constant))) ≤
      atTop.liminf (fun n =>
        returnKernel ν
            (Set.Icc (scale n * outerLower) (scale n * outerUpper))
            measurableSet_Icc
            (Set.Icc (scale n * returnLower) (scale n * returnUpper))
            measurableSet_Icc
            (blocks * diffusiveBlockLength constant scale n)
            ⟨scale n * initial, by
              constructor <;> nlinarith [hinitialReturn.1, hinitialReturn.2,
                hscaleNonneg n]⟩ Set.univ +
          ENNReal.ofReal
            (blocks * (constant / endpointMargin ^ 2 + error))) := by
  let endpointLower : ℕ → ℝ := fun k =>
    if k < blocks then outerLower - initial + endpointMargin
    else returnLower - initial
  let endpointUpper : ℕ → ℝ := fun k =>
    if k < blocks then outerUpper - initial - endpointMargin
    else returnUpper - initial
  have hmargin : ∀ k ≤ blocks,
      endpointLower k + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          endpointUpper k - (blocks : ℝ) * blockRadius := by
    intro k hk
    by_cases hlt : k < blocks
    · simpa [endpointLower, endpointUpper, hlt] using hstartMargin k hlt
    · have heq : k = blocks := by omega
      simpa [endpointLower, endpointUpper, heq] using hfinalMargin
  have hendpoint := prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints
    ν hν.1 hν.2 hscale hconstant hblockRadius target
      endpointLower endpointUpper hmargin
  refine hendpoint.trans (Filter.liminf_le_liminf ?_)
  filter_upwards [hcontrol, hscale.eventually_pos,
      hscale.eventually_diffusiveBlockLength_pos hconstant]
    with n hn hscalePos hlength
  let length := diffusiveBlockLength constant scale n
  let final : Set (ℕ → ℝ) := {increment |
    partialSum (blocks * length) increment / scale n ∈
      Set.Ioo (returnLower - initial) (returnUpper - initial)}
  have htoStartFinal :
      {increment : ℕ → ℝ | ∀ k ≤ blocks,
          partialSum (k * length) increment / scale n ∈
            Set.Ioo (endpointLower k) (endpointUpper k)} ⊆
        ({increment | ∀ j < blocks,
          partialSum (j * length) increment / scale n ∈
            Set.Ioo
              (outerLower - initial + endpointMargin)
              (outerUpper - initial - endpointMargin)} ∩ final) := by
    intro increment hendpoints
    constructor
    · intro j hj
      simpa [endpointLower, endpointUpper, hj] using hendpoints j hj.le
    · have hlast := hendpoints blocks le_rfl
      simpa [final, endpointLower, endpointUpper] using hlast
  have hc := hn (fun _ => outerLower - initial)
    (fun _ => outerUpper - initial) final
  have htoReturn :
      ({increment : ℕ → ℝ | ∀ j < blocks, ∀ k ≤ length,
          partialSum (j * length + k) increment ∈
            Set.Icc (scale n * (outerLower - initial))
              (scale n * (outerUpper - initial))} ∩ final) ⊆
        {increment | (∀ j < blocks, ∀ k ≤ length,
          scale n * initial + partialSum (j * length + k) increment ∈
            Set.Icc (scale n * outerLower) (scale n * outerUpper)) ∧
          scale n * initial + partialSum (blocks * length) increment ∈
            Set.Icc (scale n * returnLower) (scale n * returnUpper)} := by
    rintro increment ⟨hcorridor, hfinal⟩
    constructor
    · intro j hj k hk
      have hp := hcorridor j hj k hk
      constructor
      · calc
          scale n * outerLower = scale n * initial +
              scale n * (outerLower - initial) := by ring
          _ ≤ scale n * initial +
              partialSum (j * length + k) increment :=
            by linarith [hp.1]
      · calc
          scale n * initial + partialSum (j * length + k) increment ≤
              scale n * initial + scale n * (outerUpper - initial) :=
            by linarith [hp.2]
          _ = scale n * outerUpper := by ring
    · have hfinal' := hfinal
      change partialSum (blocks * length) increment / scale n ∈
        Set.Ioo (returnLower - initial) (returnUpper - initial) at hfinal'
      constructor
      · have := (lt_div_iff₀ hscalePos).mp hfinal'.1
        nlinarith
      · have := (div_lt_iff₀ hscalePos).mp hfinal'.2
        nlinarith
  have hinitialOuterScaled : scale n * initial ∈
      Set.Icc (scale n * outerLower) (scale n * outerUpper) := by
    constructor <;> nlinarith [hinitialOuter.1, hinitialOuter.2]
  have hreturn := returnKernel_Icc_apply_univ_mul_eq_blockCorridors_endsIn
    ν hinitialOuterScaled
      (show scale n * initial ∈
        Set.Icc (scale n * returnLower) (scale n * returnUpper) by
          constructor <;> nlinarith [hinitialReturn.1, hinitialReturn.2])
      hblocks hlength
  calc
    _ ≤ (independentIncrementLaw ν)
        ({increment | ∀ j < blocks,
          partialSum (j * length) increment / scale n ∈
            Set.Ioo
              (outerLower - initial + endpointMargin)
              (outerUpper - initial - endpointMargin)} ∩ final) :=
      measure_mono htoStartFinal
    _ ≤ _ := by
      have hmono := measure_mono
        (μ := independentIncrementLaw ν) htoReturn
      have hadd :
          (independentIncrementLaw ν)
              ({increment : ℕ → ℝ | ∀ j < blocks, ∀ k ≤ length,
                partialSum (j * length + k) increment ∈
                  Set.Icc (scale n * (outerLower - initial))
                    (scale n * (outerUpper - initial))} ∩ final) +
              ENNReal.ofReal
                (blocks * (constant / endpointMargin ^ 2 + error)) ≤
            (independentIncrementLaw ν)
              {increment | (∀ j < blocks, ∀ k ≤ length,
                scale n * initial + partialSum (j * length + k) increment ∈
                  Set.Icc (scale n * outerLower) (scale n * outerUpper)) ∧
                scale n * initial + partialSum (blocks * length) increment ∈
                  Set.Icc (scale n * returnLower) (scale n * returnUpper)} +
              ENNReal.ofReal
                (blocks * (constant / endpointMargin ^ 2 + error)) := by
        exact add_le_add hmono le_rfl
      have hc' := hc.trans hadd
      rw [← hreturn] at hc'
      exact hc'

/-- Quantitative return-kernel lower bound obtained from the centered
unit-second-moment maximal inequality. -/
theorem gaussianProduct_le_liminf_returnKernel_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscaleNonneg : ∀ n, 0 ≤ scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {outerLower outerUpper returnLower returnUpper initial : ℝ}
    (hinitialOuter : initial ∈ Set.Icc outerLower outerUpper)
    (hinitialReturn : initial ∈ Set.Icc returnLower returnUpper)
    {endpointMargin blockRadius error : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (herror : 0 < error)
    (target : ℕ → ℝ)
    (hstartMargin : ∀ k < blocks,
      outerLower - initial + endpointMargin +
            (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          outerUpper - initial - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hfinalMargin :
      returnLower - initial + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range blocks, target j ∧
        ∑ j ∈ Finset.range blocks, target j <
          returnUpper - initial - (blocks : ℝ) * blockRadius) :
    (∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            ((target j - blockRadius) / Real.sqrt constant)
            ((target j + blockRadius) / Real.sqrt constant))) ≤
      atTop.liminf (fun n =>
        returnKernel ν
            (Set.Icc (scale n * outerLower) (scale n * outerUpper))
            measurableSet_Icc
            (Set.Icc (scale n * returnLower) (scale n * returnUpper))
            measurableSet_Icc
            (blocks * diffusiveBlockLength constant scale n)
            ⟨scale n * initial, by
              constructor <;> nlinarith [hinitialReturn.1, hinitialReturn.2,
                hscaleNonneg n]⟩ Set.univ +
          ENNReal.ofReal
            (blocks * (constant / endpointMargin ^ 2 + error))) := by
  apply gaussianProduct_le_liminf_returnKernel_add_of_eventually_control
    ν hν hscale hscaleNonneg hconstant hblocks hinitialOuter hinitialReturn
      hblockRadius target hstartMargin hfinalMargin
  exact eventually_normalizedEndpoints_inter_le_corridors_inter_add_explicitError
    ν hν hscale hconstant hendpointMargin herror blocks

end ProbabilityTheory.RandomWalk
