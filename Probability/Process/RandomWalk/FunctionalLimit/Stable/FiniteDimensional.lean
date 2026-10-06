/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.FiniteDimensional.IndependentBlocks
public import Probability.Process.Stable.Basic
public import Probability.Distributions.Stable.Attraction.NormingRatios.Index

/-!
# Stable finite-dimensional limits for random walks

This file identifies the endpoint-vector limit from the independent-block
domain-of-attraction theorem with the finite-dimensional laws of a process
having stable clock increments. The block-scale and centering limits remain
explicit inputs, so the result does not claim path-space tightness.
-/

open Filter MeasureTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

private theorem continuous_partialSum (blocks : ℕ) :
    Continuous (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ) := by
  rw [continuous_pi_iff]
  intro j
  induction j using Fin.induction with
  | zero => exact continuous_const
  | succ j ih =>
    have hc := ih.add (continuous_apply j)
    have heq : (fun x : Fin blocks → ℝ => Fin.partialSum x j.succ) =
        (fun x : Fin blocks → ℝ => Fin.partialSum x j.castSucc) +
          (fun x : Fin blocks → ℝ => x j) := by
      funext x
      simp only [Fin.partialSum_succ, Pi.add_apply]
    exact heq ▸ hc

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If each normalized random-walk block converges to the stable increment
scale prescribed by a clock, then the normalized endpoint vector converges in
distribution to the corresponding finite-dimensional vector of any process
with those stable clock increments. The centering term is required to vanish
at the spatial scale of each block.
-/
theorem tendstoInDistribution_endpoints_of_stableClock
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {Time : Type*} [Preorder Time] [OrderBot Time]
    {clock : Time → ℝ} {X : Time → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hX : HasStableClockIncrements α μ clock X P)
    (blocks : ℕ) (grid : Fin (blocks + 1) → Time)
    (hgrid : Monotone grid) (hgridStart : grid 0 = ⊥)
    (length : ℕ → ℕ → ℕ) (spatialScale : ℕ → ℝ)
    (hblock : ∀ j : Fin blocks,
      Tendsto (fun n => length n j.val) atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : ∀ j : Fin blocks,
      Tendsto (fun n => normalization (length n j.val) / spatialScale n)
        atTop (nhds ((clock (grid j.succ) - clock (grid j.castSucc)) ^ (1 / α))))
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n => center (length n j.val) / spatialScale n)
        atTop (nhds 0)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        AdditivePath.displacement (AdditivePath.blockStart (length n) j.val)
          increments / spatialScale n)
      atTop
      (fun ω j => X (grid j) ω)
      (fun _ => iidSequenceLaw ν) P := by
  let ratio : Fin blocks → ℝ := fun j =>
    (clock (grid j.succ) - clock (grid j.castSucc)) ^ (1 / α)
  let incrementVector : Ω → Fin blocks → ℝ := fun ω j =>
    X (grid j.succ) ω - X (grid j.castSucc) ω
  let partialSumMap : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ :=
    fun z j => Fin.partialSum z j
  let scaleVector : (Fin blocks → ℝ) → Fin blocks → ℝ :=
    fun z j => ratio j * z j
  let endpointMap : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ :=
    fun z j => Fin.partialSum (fun k => ratio k * z k) j
  have hpartial : Measurable partialSumMap := by
    exact (continuous_partialSum blocks).measurable
  have hscaleVector : Measurable scaleVector := by
    fun_prop
  have hratio' (j : Fin blocks) :
      Tendsto (fun n => normalization (length n j.val) / spatialScale n)
        atTop (nhds (ratio j)) := by
    simpa [ratio] using hratio j
  have hcenter' (j : Fin blocks) :
      Tendsto (fun n => center (length n j.val) / spatialScale n)
        atTop (nhds ((0 : ℝ))) := hcenter j
  have hblocks := tendstoInDistribution_consecutiveBlockEndpoints hDOA
    blocks length spatialScale ratio (fun _ => 0) hblock hspatial hratio' hcenter'
  have hincrements : HasLaw incrementVector
      (Measure.pi fun j : Fin blocks =>
        μ.map fun x =>
          (clock (grid j.succ) - clock (grid j.castSucc)) ^ (1 / α) * x) P := by
    simpa [incrementVector] using hX.increments_hasLaw_pi blocks grid hgrid
  have hendpoint_eq : (fun ω j => X (grid j) ω) =ᵐ[P]
      fun ω => partialSumMap (incrementVector ω) := by
    filter_upwards [hX.ae_start_eq_zero] with ω hω
    funext j
    have htel := Fin.partialSum_differences
      (fun i : Fin (blocks + 1) => X (grid i) ω) j
    have hbase : X (grid 0) ω = 0 := by
      simpa [hgridStart] using hω
    simpa [partialSumMap, incrementVector, hbase] using htel.symm
  have hpartialLaw : HasLaw (fun ω => partialSumMap (incrementVector ω))
      ((Measure.pi fun j : Fin blocks =>
        μ.map fun x => ratio j * x).map partialSumMap) P := by
    have hmap : HasLaw partialSumMap
        ((Measure.pi fun j : Fin blocks =>
          μ.map fun x => ratio j * x).map partialSumMap)
        (Measure.pi fun j : Fin blocks => μ.map fun x => ratio j * x) :=
      hasLaw_map hpartial.aemeasurable
    exact hmap.comp hincrements
  have hpiMap : (Measure.pi fun _ : Fin blocks => μ).map scaleVector =
      Measure.pi (fun j : Fin blocks => μ.map fun x => ratio j * x) := by
    simpa [scaleVector] using
      (Measure.pi_map_pi
        (fun j : Fin blocks => (by fun_prop : AEMeasurable
          (fun x : ℝ => ratio j * x) μ)))
  have hlimitLaw : (Measure.pi fun _ : Fin blocks => μ).map endpointMap =
      (Measure.pi fun j : Fin blocks =>
        μ.map fun x => ratio j * x).map partialSumMap := by
    have heq : endpointMap = partialSumMap ∘ scaleVector := by
      funext z
      funext j
      rfl
    calc
      (Measure.pi fun _ : Fin blocks => μ).map endpointMap =
          (Measure.pi fun _ : Fin blocks => μ).map
            (partialSumMap ∘ scaleVector) := by rw [heq]
      _ = ((Measure.pi fun _ : Fin blocks => μ).map scaleVector).map
          partialSumMap := (Measure.map_map hpartial hscaleVector).symm
      _ = (Measure.pi fun j : Fin blocks =>
          μ.map fun x => ratio j * x).map partialSumMap := by rw [hpiMap]
  have hendpointLaw' : HasLaw (fun ω j => X (grid j) ω)
      ((Measure.pi fun j : Fin blocks =>
        μ.map fun x => ratio j * x).map partialSumMap) P :=
    hpartialLaw.congr hendpoint_eq
  have hendpointLaw : HasLaw (fun ω j => X (grid j) ω)
      ((Measure.pi fun _ : Fin blocks => μ).map endpointMap) P := by
    refine ⟨hendpointLaw'.aemeasurable, ?_⟩
    rw [hlimitLaw]
    exact hendpointLaw'.map_eq
  have hblocks' : TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        AdditivePath.displacement (AdditivePath.blockStart (length n) j.val)
          increments / spatialScale n)
      atTop endpointMap (fun _ => iidSequenceLaw ν)
      (Measure.pi fun _ : Fin blocks => μ) := by
    simpa [endpointMap, ratio] using hblocks
  exact hblocks'.congr_limit_hasLaw hendpointLaw

/-- Stable norming supplies the spatial block ratios in
`tendstoInDistribution_endpoints_of_stableClock`. Only the centering error
still has to be checked at the block scale; no path-space tightness is claimed.
-/
theorem tendstoInDistribution_endpoints_of_stableNorming
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {Time : Type*} [Preorder Time] [OrderBot Time]
    {clock : Time → ℝ} {X : Time → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hX : HasStableClockIncrements α μ clock X P)
    (blocks : ℕ) (grid : Fin (blocks + 1) → Time)
    (hgrid : Monotone grid) (hgridStart : grid 0 = ⊥)
    (length : ℕ → ℕ → ℕ)
    (hblock : ∀ j : Fin blocks,
      Tendsto (fun n => length n j.val) atTop atTop)
    (hlengthRatio : ∀ j : Fin blocks,
      Tendsto (fun n => (length n j.val : ℝ) / (n : ℝ)) atTop
        (nhds (clock (grid j.succ) - clock (grid j.castSucc))))
    (hclockPositive : ∀ j : Fin blocks,
      0 < clock (grid j.succ) - clock (grid j.castSucc))
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n => center (length n j.val) / normalization n)
        atTop (nhds 0)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        AdditivePath.displacement (AdditivePath.blockStart (length n) j.val)
          increments / normalization n)
      atTop
      (fun ω j => X (grid j) ω)
      (fun _ => iidSequenceLaw ν) P := by
  have hspatial : ∀ᶠ n in atTop, normalization n ≠ 0 :=
    hDOA.eventually_scale_pos.mono fun _ hn => hn.ne'
  have hratio (j : Fin blocks) :
      Tendsto (fun n => normalization (length n j.val) / normalization n)
        atTop (nhds ((clock (grid j.succ) - clock (grid j.castSucc)) ^ (1 / α))) := by
    have h := IsInDomainOfAttractionAlong.tendsto_norming_ratio
      hX.strictlyStable.isAlphaStable hDOA
      (fun n => length n j.val)
      (clock (grid j.succ) - clock (grid j.castSucc)) (hclockPositive j)
      (hlengthRatio j)
    simpa [one_div] using h
  exact tendstoInDistribution_endpoints_of_stableClock hDOA hX blocks grid
    hgrid hgridStart length normalization hblock hspatial hratio hcenter

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
