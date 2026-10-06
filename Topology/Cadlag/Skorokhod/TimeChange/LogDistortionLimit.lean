/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange.LogDistortion

/-!
# Logarithmic distortion bounds under uniform convergence

Uniform limits of time changes preserve any common bound on their logarithmic
secant distortion.  The proof passes each secant slope to the limit, then uses
continuity of the logarithm and absolute value and closedness of the bounded
interval.
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace Skorokhod

namespace TimeChange

/-- A uniform limit of time changes with a common logarithmic distortion
bound has the same bound. -/
theorem logDistortion_le_of_tendstoUniformly
    (sequence : ℕ → TimeChange) (limit : TimeChange)
    (huniform : TendstoUniformly (fun n t => sequence n t) limit atTop)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hlog : ∀ n, (sequence n).logDistortion ≤ ENNReal.ofReal bound) :
    limit.logDistortion ≤ ENNReal.ofReal bound := by
  rw [logDistortion_le_iff]
  intro p
  let s := p.1.1
  let t := p.1.2
  have hst : s < t := p.2
  have hpoint (u : unitInterval) :
      Tendsto (fun n => sequence n u) atTop (nhds (limit u)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hnear := Metric.tendstoUniformly_iff.mp huniform ε hε
    filter_upwards [hnear] with n hn
    simpa [dist_comm] using hn u
  have hpointReal (u : unitInterval) :
      Tendsto (fun n => ((sequence n u : unitInterval) : ℝ)) atTop
        (nhds ((limit u : unitInterval) : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp (hpoint u)
  have hnumerator :
      Tendsto (fun n => ((sequence n t : unitInterval) : ℝ) -
        ((sequence n s : unitInterval) : ℝ)) atTop
        (nhds (((limit t : unitInterval) : ℝ) - ((limit s : unitInterval) : ℝ))) :=
    (hpointReal t).sub (hpointReal s)
  have hslope : Tendsto (fun n => (sequence n).secantSlope s t) atTop
      (nhds (limit.secantSlope s t)) := by
    simpa [secantSlope, div_eq_mul_inv] using
      hnumerator.mul_const (((t : unitInterval) : ℝ) - ((s : unitInterval) : ℝ))⁻¹
  have hlogSlope : Tendsto
      (fun n => Real.log ((sequence n).secantSlope s t)) atTop
      (nhds (Real.log (limit.secantSlope s t))) :=
    (Real.continuousAt_log (ne_of_gt (secantSlope_pos limit hst))).tendsto.comp hslope
  have hlogAbs : Tendsto
      (fun n => |Real.log ((sequence n).secantSlope s t)|) atTop
      (nhds |Real.log (limit.secantSlope s t)|) :=
    continuous_abs.continuousAt.tendsto.comp hlogSlope
  have hboundAt (n : ℕ) :
      (sequence n).logSecantDistortion s t ≤ bound := by
    have hENN : ENNReal.ofReal ((sequence n).logSecantDistortion s t) ≤
        ENNReal.ofReal bound := by
      exact (le_iSup (fun q : SecantPair => ENNReal.ofReal
        ((sequence n).logSecantDistortion q.1.1 q.1.2)) p).trans (hlog n)
    exact (ENNReal.ofReal_le_ofReal_iff hbound).mp hENN
  have hlimitBound :
      limit.logSecantDistortion s t ∈ Set.Icc 0 bound := by
    apply isClosed_Icc.mem_of_tendsto hlogAbs
    filter_upwards with n
    exact ⟨logSecantDistortion_nonneg (sequence n) s t, hboundAt n⟩
  exact ENNReal.ofReal_le_ofReal hlimitBound.2

end TimeChange

end Skorokhod
