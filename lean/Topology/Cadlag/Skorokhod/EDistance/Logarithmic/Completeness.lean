/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.MetricSpace.Cauchy
public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.AlignedLimit

/-!
# Completeness of the logarithmic Skorokhod metric

Every Cauchy sequence has a summably aligned subsequence. Tail clock limits
undo the alignment and give a Billingsley limit of that subsequence; the
Cauchy property then gives convergence of the full sequence.
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace Skorokhod

/-- Every Cauchy sequence of càdlàg paths in Billingsley's logarithmic metric
converges to a càdlàg path. -/
theorem cauchySeq_tendsto_billingsleyPath
    {E : Type*} [MetricSpace E] [CompleteSpace E]
    (path : ℕ → BillingsleyPath E) (hpath : CauchySeq path) :
    ∃ limit : BillingsleyPath E, Tendsto path atTop (nhds limit) := by
  obtain ⟨index, clocks, error, alignedLimit, hindex, herror, hcost, haligned⟩ :=
    cauchySeq_subsequence_has_summableLogAlignment path hpath
  obtain ⟨limit, hsubsequence⟩ := summablyAligned_subsequence_tendsto_billingsley
    path index clocks error herror hcost alignedLimit haligned
  have hindexLower : ∀ n, n ≤ index n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have hstep : index n + 1 ≤ index (n + 1) :=
          Nat.succ_le_of_lt (hindex (Nat.lt_succ_self n))
        omega
  refine ⟨limit, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨N, hCauchy⟩ := (Metric.cauchySeq_iff.mp hpath) (ε / 2) hhalf
  have hsubEventually := Metric.tendsto_nhds.mp hsubsequence (ε / 2) hhalf
  obtain ⟨M, hM⟩ := eventually_atTop.1 hsubEventually
  let k := max N M
  have hkN : N ≤ index k := le_trans (le_max_left N M) (hindexLower k)
  have hnear : dist (path (index k)) limit < ε / 2 := hM k (le_max_right N M)
  apply eventually_atTop.2
  refine ⟨N, ?_⟩
  intro n hn
  calc
    dist (path n) limit ≤ dist (path n) (path (index k)) + dist (path (index k)) limit :=
      dist_triangle _ _ _
    _ < ε := by
      have hclose := hCauchy n hn (index k) hkN
      linarith

/-- Billingsley's logarithmic metric is complete when the state space is
complete. -/
noncomputable instance instCompleteSpaceBillingsleyPath
    {E : Type*} [MetricSpace E] [CompleteSpace E] : CompleteSpace (BillingsleyPath E) :=
  Metric.complete_of_cauchySeq_tendsto fun path hpath =>
    cauchySeq_tendsto_billingsleyPath path hpath

end Skorokhod
