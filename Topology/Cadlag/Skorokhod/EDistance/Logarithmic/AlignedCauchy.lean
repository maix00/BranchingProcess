/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.Topology
public import Topology.Cadlag.Skorokhod.TimeChange.Sequence
public import Topology.Cadlag.UniformLimit

/-!
# Uniform limits after logarithmic time-change alignment

Summably close time changes align a sequence of càdlàg paths into a uniformly
Cauchy sequence. Completeness of the logarithmic path metric additionally
requires controlling the tail time change, proved separately.
-/

@[expose] public section

open Filter
open scoped NNReal UniformConvergence

namespace Skorokhod

/-- Reparameterize the `n`th path by all preceding alignment clocks. -/
noncomputable def alignedPath {E : Type*} [TopologicalSpace E]
    (path : ℕ → CadlagPath unitInterval E) (clocks : ℕ → TimeChange) :
    ℕ → CadlagPath unitInterval E :=
  fun n => (TimeChange.cumulative clocks n).act (path n)

/-- One local alignment estimate is unchanged after applying the accumulated
time change to both paths. -/
theorem uniformEDist_alignedPath_succ_le {E : Type*} [EMetricSpace E]
    (path : ℕ → CadlagPath unitInterval E) (clocks : ℕ → TimeChange)
    (error : ℕ → ℝ≥0)
    (hclose : ∀ n, uniformEDist ((clocks n).act (path n.succ)) (path n) ≤ error n) :
    ∀ n, uniformEDist (alignedPath path clocks n)
      (alignedPath path clocks n.succ) ≤ error n := by
  intro n
  calc
    uniformEDist (alignedPath path clocks n)
        (alignedPath path clocks n.succ) =
        uniformEDist (path n) ((clocks n).act (path n.succ)) := by
          simp [alignedPath, TimeChange.cumulative_succ, TimeChange.trans_act,
            uniformEDist_act]
    _ = uniformEDist ((clocks n).act (path n.succ)) (path n) :=
      uniformEDist_comm _ _
    _ ≤ error n := hclose n

/-- If successive paths can be aligned with summably small uniform errors,
the aligned sequence is Cauchy in the space of all functions with its uniform
convergence structure. -/
theorem cauchySeq_alignedUniformFun {E : Type*} [EMetricSpace E]
    (path : ℕ → CadlagPath unitInterval E) (clocks : ℕ → TimeChange)
    (error : ℕ → ℝ≥0)
    (hclose : ∀ n, uniformEDist ((clocks n).act (path n.succ)) (path n) ≤ error n)
    (herror : Summable error) :
    CauchySeq (fun n : ℕ =>
      UniformFun.ofFun (alignedPath path clocks n : unitInterval → E)) := by
  apply cauchySeq_of_edist_le_of_summable error
  · intro n
    change uniformEDist (alignedPath path clocks n)
      (alignedPath path clocks n.succ) ≤ error n
    exact uniformEDist_alignedPath_succ_le path clocks error hclose n
  · exact herror

/-- A summably aligned sequence of càdlàg paths has a uniform limit which is
again càdlàg. This is the path-space limit step in the completeness argument;
the theorem does not yet assert convergence of the original, unaligned paths
in Billingsley's metric. -/
theorem exists_cadlag_uniformLimit_of_summably_aligned
    {E : Type*} [MetricSpace E] [CompleteSpace E]
    (path : ℕ → CadlagPath unitInterval E) (clocks : ℕ → TimeChange)
    (error : ℕ → ℝ≥0)
    (hclose : ∀ n, uniformEDist ((clocks n).act (path n.succ)) (path n) ≤ error n)
    (herror : Summable error) :
    ∃ limit : CadlagPath unitInterval E,
      TendstoUniformly (fun n t => alignedPath path clocks n t) limit atTop := by
  classical
  let alignedFun : ℕ → unitInterval →ᵤ E := fun n =>
    UniformFun.ofFun (fun t => alignedPath path clocks n t)
  have halignedCauchy : CauchySeq alignedFun := by
    simpa [alignedFun] using
      cauchySeq_alignedUniformFun path clocks error hclose herror
  obtain ⟨limitFun, hlimitFun⟩ := cauchySeq_tendsto_of_complete halignedCauchy
  have huniform : TendstoUniformly
      (fun n t => alignedPath path clocks n t) (UniformFun.toFun limitFun) atTop := by
    have h := (UniformFun.tendsto_iff_tendstoUniformly).mp hlimitFun
    change TendstoUniformly (UniformFun.toFun ∘ alignedFun)
      (UniformFun.toFun limitFun) atTop at h
    have hfun : UniformFun.toFun ∘ alignedFun =
        (fun n t => alignedPath path clocks n t) := by
      funext n t
      simp [alignedFun, UniformFun.toFun_ofFun]
    rw [hfun] at h
    exact h
  have hlimitCadlag : IsCadlag (UniformFun.toFun limitFun) :=
    IsCadlag.tendstoUniformly (fun n => (alignedPath path clocks n).isCadlag_toFun) ?_
  · exact ⟨⟨UniformFun.toFun limitFun, hlimitCadlag⟩, huniform⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendstoUniformly_iff.mp huniform ε hε).exists_forall_of_atTop
    refine ⟨N, ?_⟩
    intro n hn t
    exact (dist_comm _ _).trans_lt (hN n hn t)

end Skorokhod
