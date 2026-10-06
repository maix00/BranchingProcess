/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Block
public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.ConvergenceInDistribution.Independence
public import Topology.Algebra.BigOperators.PartialSum

/-!
# Finite-dimensional stable limits from independent blocks

This module assembles the one-dimensional domain-of-attraction block theorem
over a finite partition. It keeps the time-block lengths, normalization
ratios, and centering ratios explicit; regular-variation results can supply
those ratios in later applications.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional

private theorem partialSum_variableBlockSums {blocks : ℕ}
    (length : ℕ → ℕ) (increments : ℕ → ℝ) (j : Fin (blocks + 1)) :
    Fin.partialSum
        (fun k : Fin blocks =>
          AdditivePath.blockSum (AdditivePath.blockStart length k.val)
            (length k.val) increments) j =
      AdditivePath.displacement (AdditivePath.blockStart length j.val) increments := by
  induction j using Fin.induction with
  | zero => simp [AdditivePath.blockStart]
  | succ j ih =>
    rw [Fin.partialSum_succ, ih]
    simp only [Fin.val_castSucc, Fin.val_succ, AdditivePath.blockStart_succ]
    rw [← AdditivePath.displacement_add_eq_add_blockSum]

/-- A finite family of consecutive block sums converges jointly when each
block length diverges and its spatial and centering ratios converge. The
limiting coordinates are independent copies of the one-dimensional
domain-of-attraction limit, with the prescribed affine rescalings. -/
theorem tendstoInDistribution_consecutiveBlockSums
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {normalization center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit normalization center)
    (blocks : ℕ) (length : ℕ → ℕ → ℕ) (spatialScale : ℕ → ℝ)
    (ratio shift : Fin blocks → ℝ)
    (hblock : ∀ j : Fin blocks,
      Tendsto (fun n => length n j.val) atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : ∀ j : Fin blocks,
      Tendsto (fun n => normalization (length n j.val) / spatialScale n)
        atTop (nhds (ratio j)))
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n => center (length n j.val) / spatialScale n)
        atTop (nhds (shift j))) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin blocks) =>
        AdditivePath.blockSum (AdditivePath.blockStart (length n) j.val)
          (length n j.val) increments / spatialScale n)
      atTop
      (fun z j => ratio j * z j + shift j)
      (fun _ => iidSequenceLaw ν)
      (Measure.pi fun _ : Fin blocks => limit) := by
  let X : ℕ → Fin blocks → (ℕ → ℝ) → ℝ := fun n j increments =>
    AdditivePath.blockSum (AdditivePath.blockStart (length n) j.val)
      (length n j.val) increments / spatialScale n
  let Z : Fin blocks → ℝ → ℝ := fun j z => ratio j * z + shift j
  have hcoordinate (j : Fin blocks) :
      TendstoInDistribution (fun n => X n j) atTop (Z j)
        (fun _ => iidSequenceLaw ν) limit := by
    have hbase := h.tendstoInDistribution_partialSum_div
      (fun n => length n j.val) spatialScale
      (hblock j) hspatial (hratio j) (hcenter j)
    apply hbase.congr_map_eventually
    · filter_upwards [] with n
      let f : ℝ → ℝ := fun x => x / spatialScale n
      have hf : Measurable f := by fun_prop
      calc
        (iidSequenceLaw ν).map (fun increments =>
            AdditivePath.displacement (length n j.val) increments / spatialScale n) =
          ((iidSequenceLaw ν).map
            (AdditivePath.displacement (length n j.val))).map f := by
                simpa only [Function.comp_def, f] using
                  (Measure.map_map hf (displacement_measurable (length n j.val))).symm
        _ = ((iidSequenceLaw ν).map
            (AdditivePath.blockSum (AdditivePath.blockStart
              (length n) j.val) (length n j.val))).map f := by
              rw [← ProbabilityTheory.RandomWalk.iidSequenceLaw_map_blockSum]
        _ = (iidSequenceLaw ν).map (fun increments =>
            AdditivePath.blockSum (AdditivePath.blockStart
              (length n) j.val) (length n j.val) increments / spatialScale n) := by
                simpa only [Function.comp_def, f] using
                  Measure.map_map hf (blockSum_measurable
                    (AdditivePath.blockStart (length n) j.val)
                    (length n j.val))
    · intro n
      exact (blockSum_measurable (AdditivePath.blockStart (length n) j.val)
        (length n j.val)).div_const _ |>.aemeasurable
  have hindep (n : ℕ) :
      iIndepFun (fun j (increments : ℕ → ℝ) => X n j increments)
        (iidSequenceLaw ν) := by
    have hblocks := ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockSums ν
      (length n) blocks
    have hscaled := hblocks.comp (fun _ x => x / spatialScale n)
      (fun _ => measurable_id.div_const _)
    simpa [X, Function.comp_def] using hscaled
  simpa only [X, Z] using
    TendstoInDistribution.pi_of_iIndepFun
      hcoordinate (fun j => by fun_prop) hindep

/-- The endpoint positions of a finite random-walk partition converge to the
cumulative sums of the limiting independent block increments. -/
theorem tendstoInDistribution_consecutiveBlockEndpoints
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {normalization center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit normalization center)
    (blocks : ℕ) (length : ℕ → ℕ → ℕ) (spatialScale : ℕ → ℝ)
    (ratio shift : Fin blocks → ℝ)
    (hblock : ∀ j : Fin blocks,
      Tendsto (fun n => length n j.val) atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : ∀ j : Fin blocks,
      Tendsto (fun n => normalization (length n j.val) / spatialScale n)
        atTop (nhds (ratio j)))
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n => center (length n j.val) / spatialScale n)
        atTop (nhds (shift j))) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        AdditivePath.displacement (AdditivePath.blockStart (length n) j.val)
          increments / spatialScale n)
      atTop
      (fun z j => Fin.partialSum
        (fun k : Fin blocks => ratio k * z k + shift k) j)
      (fun _ => iidSequenceLaw ν)
      (Measure.pi fun _ : Fin blocks => limit) := by
  let X : ℕ → Fin blocks → (ℕ → ℝ) → ℝ := fun n j increments =>
    AdditivePath.blockSum (AdditivePath.blockStart (length n) j.val)
      (length n j.val) increments / spatialScale n
  let Z : Fin blocks → ℝ → ℝ := fun j z => ratio j * z + shift j
  have hblocks := tendstoInDistribution_consecutiveBlockSums h blocks length
    spatialScale ratio shift hblock hspatial hratio hcenter
  have hcontinuous : Continuous
      (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) :=
    Fin.continuous_partialSum blocks
  have hpartial := hblocks.continuous_comp hcontinuous
  apply hpartial.congr_eventually
  · filter_upwards [] with n
    filter_upwards [] with increments
    funext j
    change Fin.partialSum
        (fun k : Fin blocks => X n k increments) j =
      AdditivePath.displacement
        (AdditivePath.blockStart (length n) j.val) increments / spatialScale n
    have hscale : Fin.partialSum
        (fun k : Fin blocks =>
          AdditivePath.blockSum (AdditivePath.blockStart (length n) k.val)
            (length n k.val) increments / spatialScale n) j =
        Fin.partialSum
          (fun k : Fin blocks =>
            AdditivePath.blockSum (AdditivePath.blockStart (length n) k.val)
              (length n k.val) increments) j / spatialScale n := by
      calc
        Fin.partialSum (fun k : Fin blocks =>
            AdditivePath.blockSum (AdditivePath.blockStart (length n) k.val)
              (length n k.val) increments / spatialScale n) j =
            Fin.partialSum (fun k : Fin blocks =>
              (spatialScale n)⁻¹ * AdditivePath.blockSum
                (AdditivePath.blockStart (length n) k.val) (length n k.val)
                increments) j := by
                  congr 1
                  funext k
                  simp [div_eq_mul_inv, mul_comm]
        _ = (spatialScale n)⁻¹ * Fin.partialSum (fun k : Fin blocks =>
              AdditivePath.blockSum (AdditivePath.blockStart (length n) k.val)
                (length n k.val) increments) j := by
                  simpa [smul_eq_mul] using
                    (Fin.partialSum_smul (R := ℝ) (M := ℝ)
                      ((spatialScale n)⁻¹)
                      (fun k : Fin blocks =>
                        AdditivePath.blockSum (AdditivePath.blockStart (length n) k.val)
                          (length n k.val) increments) j)
        _ = Fin.partialSum (fun k : Fin blocks =>
              AdditivePath.blockSum (AdditivePath.blockStart (length n) k.val)
                (length n k.val) increments) j / spatialScale n := by
                  simp [div_eq_mul_inv, mul_comm]
    rw [hscale, partialSum_variableBlockSums]
  · intro n
    exact (Measurable.of_eval fun j : Fin (blocks + 1) =>
      (ProbabilityTheory.RandomWalk.displacement_measurable
        (AdditivePath.blockStart (length n) j.val)).div_const (spatialScale n)).aemeasurable

end ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional

end
