/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.CauchySubsequence
public import Topology.Cadlag.Skorokhod.TimeChange.TailLimit

/-!
# Convergence of summably aligned paths

The uniformly convergent aligned paths give a Billingsley limit after
composing with the inverse of the limiting cumulative clock. Tail clocks
control the logarithmic part of the distance.
-/

@[expose] public section

open Filter
open scoped ENNReal NNReal UniformConvergence

namespace Skorokhod

/-- A summably aligned subsequence of càdlàg paths converges in Billingsley's
logarithmic metric after undoing the limiting cumulative time change. -/
theorem summablyAligned_subsequence_tendsto_billingsley
    {E : Type*} [MetricSpace E] [CompleteSpace E]
    (path : ℕ → BillingsleyPath E) (index : ℕ → ℕ)
    (clocks : ℕ → TimeChange) (error : ℕ → ℝ≥0)
    (herror : Summable error)
    (hcost : ∀ n, billingsleyCost
      (path (index n.succ)).toCadlagPath (path (index n)).toCadlagPath (clocks n) < error n)
    (alignedLimit : CadlagPath unitInterval E)
    (haligned : TendstoUniformly
      (fun n t => alignedPath (fun k => (path (index k)).toCadlagPath) clocks n t)
      alignedLimit atTop) :
    ∃ limit : BillingsleyPath E,
      Tendsto (fun n => path (index n)) atTop (nhds limit) := by
  classical
  let selectedPath : ℕ → CadlagPath unitInterval E :=
    fun n => (path (index n)).toCadlagPath
  have hstep (n : ℕ) : (clocks n).logDistortion ≤ error n := by
    have h := hcost n
    unfold billingsleyCost at h
    exact (le_max_left _ _).trans (le_of_lt h)
  obtain ⟨globalClock, hglobal⟩ :=
    TimeChange.exists_timeChange_limit_of_summable_logDistortion clocks error hstep herror
  let relativeClock (n : ℕ) : TimeChange :=
    globalClock.symm.trans (TimeChange.cumulative clocks n)
  let tailClock (n : ℕ) : TimeChange :=
    Classical.choose (TimeChange.exists_tailTimeChange_limit_of_summable_logDistortion
      clocks error hstep herror n)
  have htailUniform (n : ℕ) : TendstoUniformly
      (fun length t => TimeChange.segment clocks n length t) (tailClock n) atTop :=
    (Classical.choose_spec (TimeChange.exists_tailTimeChange_limit_of_summable_logDistortion
      clocks error hstep herror n)).1
  have htailDistortion (n : ℕ) : (tailClock n).logDistortion ≤
      ENNReal.ofReal ((∑' k, error (n + k) : ℝ≥0) : ℝ) :=
    (Classical.choose_spec (TimeChange.exists_tailTimeChange_limit_of_summable_logDistortion
      clocks error hstep herror n)).2
  let aligned : ℕ → CadlagPath unitInterval E := fun n =>
    alignedPath selectedPath clocks n
  let candidate : BillingsleyPath E := ⟨globalClock.symm.act alignedLimit⟩
  have htailNN : Tendsto (fun n => ∑' k, error (n + k)) atTop (nhds 0) := by
    simpa only [Nat.add_comm] using NNReal.tendsto_sum_nat_add error
  have htailENN : Tendsto
      (fun n => ((∑' k, error (n + k) : ℝ≥0) : ENNReal)) atTop (nhds 0) :=
    ENNReal.tendsto_coe.mpr htailNN
  have halignedFun : Tendsto (fun n => UniformFun.ofFun
      (aligned n : unitInterval → E)) atTop
      (nhds (UniformFun.ofFun (alignedLimit : unitInterval → E))) := by
    apply (UniformFun.tendsto_iff_tendstoUniformly).2
    change TendstoUniformly
      (fun n t => UniformFun.toFun (UniformFun.ofFun (aligned n : unitInterval → E)) t)
      (UniformFun.toFun (UniformFun.ofFun (alignedLimit : unitInterval → E))) atTop
    simpa [UniformFun.toFun_ofFun, aligned] using haligned
  refine ⟨candidate, ?_⟩
  apply EMetric.tendsto_nhds.mpr
  intro ε hε
  have htailSmall : ∀ᶠ n in atTop,
      ((∑' k, error (n + k) : ℝ≥0) : ENNReal) < ε := by
    exact (tendsto_order.mp htailENN).2 ε hε
  have hspaceSmall : ∀ᶠ n in atTop, uniformEDist (aligned n) alignedLimit < ε := by
    have h := EMetric.tendsto_nhds.mp halignedFun ε hε
    simpa [uniformEDist, aligned] using h
  filter_upwards [htailSmall, hspaceSmall] with n htail hspace
  have hfactor : globalClock =
      (TimeChange.cumulative clocks n).trans (tailClock n) :=
    TimeChange.cumulativeLimit_eq_prefix_trans_tailLimit clocks n globalClock (tailClock n)
      hglobal (htailUniform n)
  have hrelative : relativeClock n = (tailClock n).symm := by
    apply TimeChange.ext
    intro t
    change TimeChange.cumulative clocks n (globalClock.symm t) = (tailClock n).symm t
    have hcomp := congrArg (fun τ : TimeChange => τ (globalClock.symm t)) hfactor
    simp only [TimeChange.trans_apply, TimeChange.apply_symm_apply] at hcomp
    calc
      TimeChange.cumulative clocks n (globalClock.symm t) =
          (tailClock n).symm ((tailClock n)
            (TimeChange.cumulative clocks n (globalClock.symm t))) := by simp
      _ = (tailClock n).symm t := congrArg (tailClock n).symm hcomp.symm
  have hclockSmall : (relativeClock n).logDistortion ≤
      ((∑' k, error (n + k) : ℝ≥0) : ENNReal) := by
    rw [hrelative, TimeChange.logDistortion_symm]
    simpa [ENNReal.ofReal_coe_nnreal] using htailDistortion n
  have hspaceEq : uniformEDist ((relativeClock n).act (selectedPath n)) candidate.toCadlagPath =
      uniformEDist (aligned n) alignedLimit := by
    have hact : (relativeClock n).act (selectedPath n) =
        globalClock.symm.act (aligned n) := by
      simp [relativeClock, aligned, TimeChange.trans_act, alignedPath, selectedPath]
    rw [hact]
    change uniformEDist (globalClock.symm.act (aligned n))
      (globalClock.symm.act alignedLimit) = _
    exact uniformEDist_act (aligned n) alignedLimit globalClock.symm
  have hspecifiedCost : billingsleyCost (selectedPath n) candidate.toCadlagPath
      (relativeClock n) < ε := by
    unfold billingsleyCost
    rw [hspaceEq]
    exact max_lt_iff.mpr ⟨hclockSmall.trans_lt htail, hspace⟩
  have hdistance : billingsleyEDist (selectedPath n) candidate.toCadlagPath < ε :=
    (billingsleyEDist_le_cost _ _ (relativeClock n)).trans_lt hspecifiedCost
  change edist (path (index n)) candidate < ε
  exact hdistance

end Skorokhod
