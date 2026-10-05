/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.CLT
public import Probability.ConvergenceInDistribution.Independence
public import Probability.ConvergenceInDistribution.Portmanteau

/-!
# Finite-dimensional Gaussian limits for Mogulskii blocks

The endpoint CLT is lifted to consecutive independent blocks.  These results
are finite-dimensional inputs for the path-level invariance principle; they
do not assert tightness in path space.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- Any fixed finite vector of consecutive diffusive block sums converges to
independent centered Gaussian increments. -/
theorem tendstoInDistribution_diffusiveBlockSums
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ) :
    TendstoInDistribution
      (fun n increment (j : Fin blocks) =>
        let length := diffusiveBlockLength constant scale n
        AdditivePath.blockSum (j * length) length increment / scale n)
      atTop
      (fun z (j : Fin blocks) => z j * Real.sqrt constant)
      (fun _ => independentIncrementLaw ν)
      (Measure.pi fun _ : Fin blocks => gaussianReal 0 1) := by
  let length : ℕ → ℕ := diffusiveBlockLength constant scale
  let X : ℕ → Fin blocks → (ℕ → ℝ) → ℝ := fun n j increment =>
    AdditivePath.blockSum (j * length n) (length n) increment / scale n
  let Z : Fin blocks → ℝ → ℝ := fun _ z => z * Real.sqrt constant
  have hbase := tendstoInDistribution_partialSum_diffusiveBlock_div_scale
    ν hcentered hsecondMoment hscale hconstant
  have hcoordinate (j : Fin blocks) :
      TendstoInDistribution (fun n => X n j) atTop (Z j)
        (fun _ => independentIncrementLaw ν) (gaussianReal 0 1) := by
    apply hbase.congr_map_eventually
    · filter_upwards [] with n
      have hblock := iidSequenceLaw_map_blockSum ν
        (j * length n) (length n)
      have hdiv : Measurable (fun x : ℝ => x / scale n) :=
        measurable_id.div_const _
      calc
        (independentIncrementLaw ν).map
            (fun increment => AdditivePath.displacement (length n) increment / scale n) =
          ((independentIncrementLaw ν).map (AdditivePath.displacement (length n))).map
            (fun x => x / scale n) := by
              simpa only [Function.comp_def] using
                (Measure.map_map hdiv
                  (displacement_measurable (length n))).symm
        _ = ((independentIncrementLaw ν).map
              (AdditivePath.blockSum (j * length n) (length n))).map
              (fun x => x / scale n) := by
                rw [show (independentIncrementLaw ν).map
                    (AdditivePath.blockSum (j * length n) (length n)) =
                    (independentIncrementLaw ν).map
                      (AdditivePath.displacement (length n)) by
                  simpa [independentIncrementLaw] using hblock]
        _ = (independentIncrementLaw ν).map (X n j) := by
          simpa only [X, Function.comp_def] using
            Measure.map_map hdiv
              (blockSum_measurable (j * length n) (length n))
    · intro n
      exact (blockSum_measurable (j * length n) (length n)).div_const _
        |>.aemeasurable
  have hindep (n : ℕ) : iIndepFun (X n) (independentIncrementLaw ν) := by
    have h := iIndepFun_consecutiveBlockSums ν blocks (length n)
    exact h.comp (fun _ x => x / scale n)
      (fun _ => measurable_id.div_const _)
  simpa only [X, Z, length] using TendstoInDistribution.pi_of_iIndepFun
    hcoordinate (fun _ => by fun_prop) hindep

/-- The limiting product-Gaussian probability of a finite open box is a
lower bound for the liminf of the corresponding normalized block-vector
probabilities. -/
theorem measure_gaussianBlockBox_le_liminf
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ)
    (lower upper : Fin blocks → ℝ) :
    (Measure.pi fun _ : Fin blocks => gaussianReal 0 1).map
        (fun z j => z j * Real.sqrt constant)
        (Set.univ.pi fun j => Set.Ioo (lower j) (upper j)) ≤
      atTop.liminf (fun n =>
        (independentIncrementLaw ν) {increment |
          ∀ j : Fin blocks,
            AdditivePath.blockSum
                (j * diffusiveBlockLength constant scale n)
                (diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower j) (upper j)}) := by
  let X : ℕ → (ℕ → ℝ) → (Fin blocks → ℝ) := fun n increment j =>
    AdditivePath.blockSum
        (j * diffusiveBlockLength constant scale n)
        (diffusiveBlockLength constant scale n) increment / scale n
  let Z : (Fin blocks → ℝ) → (Fin blocks → ℝ) := fun z j =>
    z j * Real.sqrt constant
  let G : Set (Fin blocks → ℝ) :=
    Set.univ.pi fun j => Set.Ioo (lower j) (upper j)
  have hG : IsOpen G := isOpen_set_pi Set.finite_univ fun j _ => isOpen_Ioo
  have hconv := tendstoInDistribution_diffusiveBlockSums ν hcentered
    hsecondMoment hscale hconstant blocks
  have hbound := hconv.measure_map_le_liminf_of_isOpen hG
  have hX (n : ℕ) : Measurable (X n) := by
    rw [measurable_pi_iff]
    intro j
    exact (blockSum_measurable
      (j * diffusiveBlockLength constant scale n)
      (diffusiveBlockLength constant scale n)).div_const _
  have hpreimage (n : ℕ) :
      X n ⁻¹' G = {increment |
        ∀ j : Fin blocks,
          AdditivePath.blockSum
              (j * diffusiveBlockLength constant scale n)
              (diffusiveBlockLength constant scale n) increment /
              scale n ∈ Set.Ioo (lower j) (upper j)} := by
    ext increment
    simp only [X, G, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioo, Set.mem_ofPred_eq]
  simpa only [X, Z, G, Measure.map_apply (hX _) hG.measurableSet,
    hpreimage] using hbound

/-- The product-Gaussian probability in the finite-dimensional lower bound
factors into the one-dimensional interval probabilities. -/
theorem measure_gaussianBlockBox_eq_prod
    {constant : ℝ} (hconstant : 0 < constant) {blocks : ℕ}
    (lower upper : Fin blocks → ℝ) :
    (Measure.pi fun _ : Fin blocks => gaussianReal 0 1).map
        (fun z j => z j * Real.sqrt constant)
        (Set.univ.pi fun j => Set.Ioo (lower j) (upper j)) =
      ∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo (lower j / Real.sqrt constant)
            (upper j / Real.sqrt constant)) := by
  have hsqrt : 0 < Real.sqrt constant := Real.sqrt_pos.2 hconstant
  have hG : MeasurableSet
      (Set.univ.pi fun j : Fin blocks => Set.Ioo (lower j) (upper j)) :=
    MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioo
  rw [Measure.map_apply (by fun_prop) hG]
  have hpreimage :
      (fun z : Fin blocks → ℝ => fun j => z j * Real.sqrt constant) ⁻¹'
          (Set.univ.pi fun j => Set.Ioo (lower j) (upper j)) =
        Set.univ.pi fun j =>
          (fun x : ℝ => x * Real.sqrt constant) ⁻¹'
            Set.Ioo (lower j) (upper j) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hpreimage, Measure.pi_pi]
  congr 1 with j
  apply measure_congr
  filter_upwards [] with x
  simp only [Set.mem_preimage, Set.mem_Ioo]
  exact propext ⟨fun h => ⟨(div_lt_iff₀ hsqrt).2 h.1,
      (lt_div_iff₀ hsqrt).2 h.2⟩,
    fun h => ⟨(div_lt_iff₀ hsqrt).1 h.1,
      (lt_div_iff₀ hsqrt).1 h.2⟩⟩

/-- Direct product form of the finite-dimensional open-box lower bound. -/
theorem prod_gaussian_Ioo_le_liminf_measure_diffusiveBlockSums
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ)
    (lower upper : Fin blocks → ℝ) :
    (∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo (lower j / Real.sqrt constant)
            (upper j / Real.sqrt constant))) ≤
      atTop.liminf (fun n =>
        (independentIncrementLaw ν) {increment |
          ∀ j : Fin blocks,
            AdditivePath.blockSum
                (j * diffusiveBlockLength constant scale n)
                (diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower j) (upper j)}) := by
  rw [← measure_gaussianBlockBox_eq_prod hconstant lower upper]
  exact measure_gaussianBlockBox_le_liminf ν hcentered hsecondMoment
    hscale hconstant blocks lower upper

end ProbabilityTheory.RandomWalk
