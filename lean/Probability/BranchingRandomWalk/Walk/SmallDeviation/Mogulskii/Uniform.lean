module

public import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Uniform
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Partition
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Partition.Quantitative
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.GaussianProduct

@[expose] public section

/-!
# Uniform finite-reference Mogulskii bounds

The diffusive block length used in the finite-dimensional lower bound is
chosen before the reference point.  Consequently a finite family of initial
positions can share one block scale, as required by the uniform killed-kernel
blocking argument.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A prescribed common within-block control transfers the Gaussian endpoint
bound to killed-kernel survival from one normalized initial position.  Keeping
the control as an explicit hypothesis makes the chosen block scale reusable
for several initial positions. -/
theorem gaussianProduct_le_liminf_remainingMass_add_of_eventually_control
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper initial endpointMargin blockRadius tolerance : ℝ}
    (hinitial : initial ∈ Set.Icc lower upper)
    (hblockRadius : 0 < blockRadius)
    (target : ℕ → ℝ)
    (hmargin : ∀ k ≤ blocks,
      lower - initial + endpointMargin + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          upper - initial - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hcontrol : ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      (independentIncrementLaw ν) {increment | ∀ j < blocks,
          partialSum
              (j * diffusiveBlockLength constant scale n) increment /
              scale n ∈
            Set.Ioo (lower j + endpointMargin) (upper j - endpointMargin)} ≤
        (independentIncrementLaw ν) {increment | ∀ j < blocks,
            ∀ k ≤ diffusiveBlockLength constant scale n,
              partialSum
                  (j * diffusiveBlockLength constant scale n + k) increment ∈
                Set.Icc (scale n * lower j) (scale n * upper j)} +
          ENNReal.ofReal tolerance) :
    (∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            ((target j - blockRadius) / Real.sqrt constant)
            ((target j + blockRadius) / Real.sqrt constant))) ≤
      atTop.liminf (fun n =>
        Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale n * lower) (scale n * upper))
              measurableSet_Icc)
            (blocks * diffusiveBlockLength constant scale n)
            (scale n * initial) +
          ENNReal.ofReal tolerance) := by
  have hendpoint :=
    prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints
      ν hν.1 hν.2 hscale hconstant hblockRadius target
      (fun _ => lower - initial + endpointMargin)
      (fun _ => upper - initial - endpointMargin) (by
        intro k hk
        have hm := hmargin k hk
        constructor <;> linarith)
  refine hendpoint.trans (Filter.liminf_le_liminf ?_)
  filter_upwards [hcontrol, hscale.eventually_pos,
      hscale.eventually_diffusiveBlockLength_pos hconstant]
    with n hn hscalePos hlength
  have hinitialScaled : scale n * initial ∈
      Set.Icc (scale n * lower) (scale n * upper) := by
    constructor <;> nlinarith [hinitial.1, hinitial.2]
  have hkernel :=
    killedIncrementKernel_Icc_remainingMass_mul_eq_blockCorridors
      ν (scale n * lower) (scale n * upper) (scale n * initial)
      hinitialScaled hblocks hlength
  have hevent :
      {increment : ℕ → ℝ | ∀ j < blocks,
          ∀ k ≤ diffusiveBlockLength constant scale n,
            partialSum
                (j * diffusiveBlockLength constant scale n + k) increment ∈
              Set.Icc (scale n * (lower - initial))
                (scale n * (upper - initial))} =
        {increment | ∀ j < blocks,
          ∀ k ≤ diffusiveBlockLength constant scale n,
            scale n * initial +
                partialSum
                  (j * diffusiveBlockLength constant scale n + k) increment ∈
              Set.Icc (scale n * lower) (scale n * upper)} := by
    ext increment
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor <;> intro h j hj k hk
    · have hp := h j hj k hk
      constructor <;> nlinarith
    · have hp := h j hj k hk
      constructor <;> nlinarith
  have hc := hn (fun _ => lower - initial) (fun _ => upper - initial)
  rw [hevent, ← hkernel] at hc
  calc
    (independentIncrementLaw ν) {increment | ∀ k ≤ blocks,
        partialSum (k * diffusiveBlockLength constant scale n) increment /
            scale n ∈
          Set.Ioo (lower - initial + endpointMargin)
            (upper - initial - endpointMargin)} ≤
      (independentIncrementLaw ν) {increment | ∀ j < blocks,
        partialSum (j * diffusiveBlockLength constant scale n) increment /
            scale n ∈
          Set.Ioo (lower - initial + endpointMargin)
            (upper - initial - endpointMargin)} := by
        apply measure_mono
        intro increment hincrement j hj
        exact hincrement j hj.le
    _ ≤ _ := hc

/-- A finite family of normalized initial positions shares one diffusive block
constant.  Each reference may use its own deterministic target increments;
the within-block error and its scale are common to the whole family. -/
theorem exists_diffusiveBlockConstant_finset_gaussianProduct_le_liminf_remainingMass_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper endpointMargin blockRadius tolerance : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (htolerance : 0 < tolerance)
    (references : Finset ℝ) (target : ℝ → ℕ → ℝ)
    (hinitial : ∀ y ∈ references, y ∈ Set.Icc lower upper)
    (hmargin : ∀ y ∈ references, ∀ k ≤ blocks,
      lower - y + endpointMargin + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target y j ∧
        ∑ j ∈ Finset.range k, target y j <
          upper - y - endpointMargin -
            (blocks : ℝ) * blockRadius) :
    ∃ constant > 0, ∀ y ∈ references,
      (∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target y j - blockRadius) / Real.sqrt constant)
              ((target y j + blockRadius) / Real.sqrt constant))) ≤
        atTop.liminf (fun n =>
          Kernel.remainingMass
              (killedIncrementKernel ν
                (Set.Icc (scale n * lower) (scale n * upper))
                measurableSet_Icc)
              (blocks * diffusiveBlockLength constant scale n)
              (scale n * y) +
            ENNReal.ofReal tolerance) := by
  obtain ⟨constant, hconstant, hcontrol⟩ :=
    exists_diffusiveBlockConstant_eventually_normalizedEndpoints_le_corridors_add
      ν hν hscale hblocks hendpointMargin htolerance
  refine ⟨constant, hconstant, ?_⟩
  intro y hy
  exact gaussianProduct_le_liminf_remainingMass_add_of_eventually_control
    ν hν hscale hconstant hblocks (hinitial y hy) hblockRadius
    (target y) (hmargin y hy) hcontrol

/-- A nonempty finite family of the Gaussian block products has a common
strictly positive lower bound.  The proof chooses an actual minimizing
reference point, so no extended-real infimum or compactness argument is
needed. -/
theorem exists_pos_le_finset_gaussianProduct
    {constant blockRadius : ℝ} (hconstant : 0 < constant)
    (hblockRadius : 0 < blockRadius) {blocks : ℕ}
    (references : Finset ℝ) (hreferences : references.Nonempty)
    (target : ℝ → ℕ → ℝ) :
    ∃ lowerBound : ENNReal, 0 < lowerBound ∧ ∀ y ∈ references,
      lowerBound ≤ ∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            ((target y j - blockRadius) / Real.sqrt constant)
            ((target y j + blockRadius) / Real.sqrt constant)) := by
  classical
  let product : ℝ → ENNReal := fun y => ∏ j : Fin blocks,
    gaussianReal 0 1
      (Set.Ioo
        ((target y j - blockRadius) / Real.sqrt constant)
        ((target y j + blockRadius) / Real.sqrt constant))
  obtain ⟨y, hy, hyMin⟩ := references.exists_min_image product hreferences
  refine ⟨product y, ?_, hyMin⟩
  exact prod_gaussian_Ioo_sub_add_pos hconstant hblockRadius
    (fun j : Fin blocks => target y j)

/-- Common-scale finite-reference bounds can be summarized by one positive
Gaussian lower bound.  This is the finite-dimensional positivity input used
when choosing the numerical one-block survival constant. -/
theorem exists_diffusiveBlockConstant_pos_le_finset_liminf_remainingMass_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper endpointMargin blockRadius tolerance : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (htolerance : 0 < tolerance)
    (references : Finset ℝ) (hreferences : references.Nonempty)
    (target : ℝ → ℕ → ℝ)
    (hinitial : ∀ y ∈ references, y ∈ Set.Icc lower upper)
    (hmargin : ∀ y ∈ references, ∀ k ≤ blocks,
      lower - y + endpointMargin + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target y j ∧
        ∑ j ∈ Finset.range k, target y j <
          upper - y - endpointMargin -
            (blocks : ℝ) * blockRadius) :
    ∃ constant > 0, ∃ lowerBound : ENNReal, 0 < lowerBound ∧
      (∀ y ∈ references,
        lowerBound ≤ ∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target y j - blockRadius) / Real.sqrt constant)
              ((target y j + blockRadius) / Real.sqrt constant))) ∧
      ∀ y ∈ references,
        (∏ j : Fin blocks,
            gaussianReal 0 1
              (Set.Ioo
                ((target y j - blockRadius) / Real.sqrt constant)
                ((target y j + blockRadius) / Real.sqrt constant))) ≤
          atTop.liminf (fun n =>
            Kernel.remainingMass
                (killedIncrementKernel ν
                  (Set.Icc (scale n * lower) (scale n * upper))
                  measurableSet_Icc)
                (blocks * diffusiveBlockLength constant scale n)
                (scale n * y) +
              ENNReal.ofReal tolerance) := by
  obtain ⟨constant, hconstant, hliminf⟩ :=
    exists_diffusiveBlockConstant_finset_gaussianProduct_le_liminf_remainingMass_add
      ν hν hscale hblocks hendpointMargin hblockRadius htolerance
      references target hinitial hmargin
  obtain ⟨lowerBound, hlowerBound, hlower⟩ :=
    exists_pos_le_finset_gaussianProduct hconstant hblockRadius
      references hreferences target
  exact ⟨constant, hconstant, lowerBound, hlowerBound, hlower, hliminf⟩

/-- The common-scale finite-reference estimate feeds directly into the
uniform survival comparison.  Once a number lies strictly below every finite
Gaussian product after paying the common error, it eventually bounds survival
from every normalized point of the original interval. -/
theorem exists_diffusiveBlockConstant_eventually_uniform_remainingMass_of_finset
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper coverMargin endpointMargin blockRadius tolerance : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (htolerance : 0 < tolerance)
    (references : Finset ℝ) (target : ℝ → ℕ → ℝ)
    (hcover : ∀ x ∈ Set.Icc lower upper,
      ∃ y ∈ references, |x - y| ≤ coverMargin)
    (hinitial : ∀ y ∈ references,
      y ∈ Set.Icc (lower + coverMargin) (upper - coverMargin))
    (hmargin : ∀ y ∈ references, ∀ k ≤ blocks,
      lower + coverMargin - y + endpointMargin +
            (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target y j ∧
        ∑ j ∈ Finset.range k, target y j <
          upper - coverMargin - y - endpointMargin -
            (blocks : ℝ) * blockRadius) :
    ∃ constant > 0, ∀ lowerBound : ENNReal,
      (∀ y ∈ references,
        lowerBound + ENNReal.ofReal tolerance <
          ∏ j : Fin blocks,
            gaussianReal 0 1
              (Set.Ioo
                ((target y j - blockRadius) / Real.sqrt constant)
                ((target y j + blockRadius) / Real.sqrt constant))) →
      ∀ᶠ n in atTop, ∀ x : Set.Icc lower upper,
        lowerBound ≤ Kernel.remainingMass
          (killedIncrementKernel ν
            (Set.Icc (scale n * lower) (scale n * upper))
            measurableSet_Icc)
          (blocks * diffusiveBlockLength constant scale n)
          (scale n * x) := by
  obtain ⟨constant, hconstant, href⟩ :=
    exists_diffusiveBlockConstant_finset_gaussianProduct_le_liminf_remainingMass_add
      ν hν hscale hblocks hendpointMargin hblockRadius htolerance
      references target hinitial hmargin
  refine ⟨constant, hconstant, ?_⟩
  intro lowerBound hgap
  exact eventually_forall_le_remainingMass_killedIncrementKernel_Icc_of_finset_liminf
    ν lower upper coverMargin references scale
      (fun n => blocks * diffusiveBlockLength constant scale n)
      lowerBound (ENNReal.ofReal tolerance)
      (fun y => ∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            ((target y j - blockRadius) / Real.sqrt constant)
            ((target y j + blockRadius) / Real.sqrt constant)))
      (by simp) (hscale.eventually_pos.mono fun _ hn => hn.le)
      hcover href hgap

/-- A finite family of normalized starting points with a common strict
interior margin eventually shares one positive killed-kernel survival bound.
The block constant, maximal-inequality error, and numerical lower bound are
chosen together, so no circular error hypothesis remains.  Boundary starting
points require a separate entrance estimate and are deliberately excluded
from this statement. -/
theorem exists_eventually_finset_pos_remainingMass_zeroTarget
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {endpointMargin blockRadius : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper : ℝ} (references : Finset ℝ)
    (hinitial : ∀ y ∈ references, y ∈ Set.Icc lower upper)
    (hmargin : ∀ y ∈ references,
      lower - y + endpointMargin + (blocks : ℝ) * blockRadius < 0 ∧
        0 < upper - y - endpointMargin -
          (blocks : ℝ) * blockRadius) :
    ∃ constant > 0, constant ≤ 1 ∧
      ∃ lowerBound : ENNReal, 0 < lowerBound ∧
        ∀ᶠ n in atTop, ∀ y ∈ references,
          lowerBound ≤ Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale n * lower) (scale n * upper))
              measurableSet_Icc)
            (blocks * diffusiveBlockLength constant scale n)
            (scale n * y) := by
  obtain ⟨constant, hconstant, hconstantOne, error, herror,
      lowerBound, hlowerBound, hgap⟩ :=
    exists_constant_error_lowerBound_lt_gaussianProduct
      hendpointMargin hblockRadius hblocks
  have hcontrol :=
    eventually_normalizedEndpoints_le_corridors_add_explicitError
      ν hν hscale hconstant hendpointMargin herror blocks
  let errorMass := ENNReal.ofReal
    (blocks * (constant / endpointMargin ^ 2 + error))
  let gaussianBound := ∏ _j : Fin blocks,
    gaussianReal 0 1
      (Set.Ioo
        (-blockRadius / Real.sqrt constant)
        (blockRadius / Real.sqrt constant))
  have hliminf : ∀ y ∈ references,
      gaussianBound ≤ atTop.liminf (fun n =>
        Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale n * lower) (scale n * upper))
              measurableSet_Icc)
            (blocks * diffusiveBlockLength constant scale n)
            (scale n * y) + errorMass) := by
    intro y hy
    simpa [gaussianBound, errorMass] using
      (gaussianProduct_le_liminf_remainingMass_add_of_eventually_control
        ν hν hscale hconstant hblocks (hinitial y hy) hblockRadius
        (fun _ => 0) (by
          intro k hk
          simpa using hmargin y hy) hcontrol)
  have hreference : ∀ y ∈ references, ∀ᶠ n in atTop,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale n * lower) (scale n * upper)) measurableSet_Icc)
        (blocks * diffusiveBlockLength constant scale n)
        (scale n * y) := by
    intro y hy
    have hgap' : lowerBound + errorMass < gaussianBound := by
      simpa [gaussianBound, errorMass] using hgap
    have hstrict : lowerBound + errorMass < atTop.liminf (fun n =>
        Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale n * lower) (scale n * upper))
              measurableSet_Icc)
            (blocks * diffusiveBlockLength constant scale n)
            (scale n * y) + errorMass) :=
      hgap'.trans_le (hliminf y hy)
    have herrorFinite : errorMass ≠ ⊤ := by
      exact ENNReal.ofReal_ne_top
    filter_upwards [eventually_lt_of_lt_liminf hstrict] with n hn
    exact ((ENNReal.add_lt_add_iff_right herrorFinite).1 hn).le
  refine ⟨constant, hconstant, hconstantOne,
    lowerBound, hlowerBound, ?_⟩
  exact references.eventually_all.2 hreference

end ProbabilityTheory.RandomWalk
