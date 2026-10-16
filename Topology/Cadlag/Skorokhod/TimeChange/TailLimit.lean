/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange.StrictLimit
public import Topology.Cadlag.Skorokhod.TimeChange.LogDistortionLimit

/-!
# Tail limits of cumulative time changes

Every tail of a summably controlled clock sequence has a limiting time
change. The global cumulative limit factors through each finite prefix and its
tail limit.
-/

@[expose] public section

open Filter
open scoped NNReal

namespace Skorokhod

namespace TimeChange

/-- A uniform limit of functions gives pointwise convergence at every time. -/
private theorem tendsto_apply_of_tendstoUniformly
    {F : ℕ → unitInterval → unitInterval} {f : unitInterval → unitInterval}
    (h : TendstoUniformly F f atTop) (t : unitInterval) :
    Tendsto (fun n => F n t) atTop (nhds (f t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnear := Metric.tendstoUniformly_iff.mp h ε hε
  filter_upwards [hnear] with n hn
  simpa [dist_comm] using hn t

/-- Every tail of clocks with a summable logarithmic distortion budget has a
uniformly limiting time change. -/
theorem exists_tailTimeChange_limit_of_summable_logDistortion
    (clocks : ℕ → TimeChange) (error : ℕ → ℝ≥0)
    (hstep : ∀ n, (clocks n).logDistortion ≤ error n)
    (herror : Summable error) (start : ℕ) :
    ∃ tail : TimeChange,
      TendstoUniformly (fun length t => segment clocks start length t) tail atTop ∧
        tail.logDistortion ≤
          ENNReal.ofReal ((∑' k, error (start + k) : ℝ≥0) : ℝ) := by
  have htailError : Summable fun k => error (start + k) := by
    simpa only [Nat.add_comm] using NNReal.summable_nat_add error herror start
  obtain ⟨tail, htail⟩ := exists_timeChange_limit_of_summable_logDistortion
    (fun k => clocks (start + k)) (fun k => error (start + k))
    (fun k => hstep (start + k)) htailError
  have htailUniform : TendstoUniformly
      (fun length t => segment clocks start length t) tail atTop := by
    simpa [segment] using htail
  have hsegmentBound (length : ℕ) :
      (segment clocks start length).logDistortion ≤
        ENNReal.ofReal ((∑' k, error (start + k) : ℝ≥0) : ℝ) := by
    have hfinite := logDistortion_segment_le_tsum clocks error hstep start length
    calc
      (segment clocks start length).logDistortion ≤
          ∑' k, (error (start + k) : ENNReal) := hfinite
      _ = ENNReal.ofReal ((∑' k, error (start + k) : ℝ≥0) : ℝ) := by
        rw [← ENNReal.coe_tsum htailError, ENNReal.ofReal_coe_nnreal]
  have htailDistortion := logDistortion_le_of_tendstoUniformly
    (fun length => segment clocks start length) tail htailUniform
    (bound := ((∑' k, error (start + k) : ℝ≥0) : ℝ))
    (NNReal.coe_nonneg _) hsegmentBound
  exact ⟨tail, htailUniform, htailDistortion⟩

/-- The global limit clock factors as any finite cumulative prefix followed by
the limiting time change of the remaining tail. -/
theorem cumulativeLimit_eq_prefix_trans_tailLimit
    (clocks : ℕ → TimeChange) (start : ℕ)
    (globalLimit tailLimit : TimeChange)
    (hglobal : TendstoUniformly (fun n t => cumulative clocks n t) globalLimit atTop)
    (htail : TendstoUniformly
      (fun length t => segment clocks start length t) tailLimit atTop) :
    globalLimit = (cumulative clocks start).trans tailLimit := by
  apply TimeChange.ext
  intro t
  have hglobalPoint := tendsto_apply_of_tendstoUniformly hglobal t
  have hglobalShift : Tendsto (fun k => cumulative clocks (start + k) t)
      atTop (nhds (globalLimit t)) := by
    have hshift : Tendsto (fun k => start + k) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat start
    exact hglobalPoint.comp hshift
  have htailPoint := tendsto_apply_of_tendstoUniformly htail (cumulative clocks start t)
  have hseqEq : ∀ k,
      cumulative clocks (start + k) t =
        segment clocks start k (cumulative clocks start t) := by
    intro k
    calc
      cumulative clocks (start + k) t =
          ((cumulative clocks start).trans (segment clocks start k)) t := by
            rw [cumulative_add_eq_trans_segment]
      _ = segment clocks start k (cumulative clocks start t) := by
        simp [TimeChange.trans_apply]
  have htailPoint' : Tendsto
      (fun k => segment clocks start k (cumulative clocks start t)) atTop
      (nhds (tailLimit (cumulative clocks start t))) := htailPoint
  have htailGlobal := htailPoint'.congr' <| Filter.Eventually.of_forall fun k =>
    (hseqEq k).symm
  have hEq := tendsto_nhds_unique hglobalShift htailGlobal
  simpa [TimeChange.trans_apply] using hEq

end TimeChange

end Skorokhod
