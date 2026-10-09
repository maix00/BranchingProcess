/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Support
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Support tests for càdlàg path laws

These statements concern arbitrary measures on Skorokhod path space; they do
not require a process realization or a particular path law.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MeasureTheory.CadlagPath

/-- Positive mass in every centered uniform corridor puts the zero path in
the support of a càdlàg path law. -/
theorem straightPath_zero_mem_support_of_centeredCorridors_pos
    (Q : Measure (CadlagPath unitInterval ℝ))
    (hpos : ∀ δ : ℝ, 0 < δ →
      0 < Q (Skorokhod.rangeInOpenInterval (-δ) δ)) :
    Skorokhod.straightPath 0 ∈ Q.support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hsub : Skorokhod.rangeInOpenInterval (-r / 2) (r / 2) ⊆ U := by
    intro f hf
    apply hball
    rw [Metric.mem_ball]
    have huniform : Skorokhod.uniformEDist f (Skorokhod.straightPath 0) ≤
        ENNReal.ofReal (r / 2) := by
      apply iSup_le
      intro t
      obtain ⟨margin, hmargin, hpath⟩ := hf
      have ht := hpath t
      rw [edist_dist]
      have hbound : |f t| ≤ r / 2 := by
        have hvalue : Skorokhod.straightPath 0 t = 0 := by
          simp [Skorokhod.straightPath]
        simp only [hvalue] at *
        rw [abs_le]
        constructor <;> linarith
      simpa [Skorokhod.straightPath, Real.dist_eq] using
        ENNReal.ofReal_le_ofReal hbound
    have hj1 := (Skorokhod.j1EDist_le_uniformEDist f
      (Skorokhod.straightPath 0)).trans huniform
    have hlt : ENNReal.ofReal (r / 2) < ENNReal.ofReal r := by
      exact ENNReal.ofReal_lt_ofReal_iff hr |>.2 (by linarith)
    have hed : edist f (Skorokhod.straightPath 0) < ENNReal.ofReal r := by
      rw [Skorokhod.edist_cadlagPath_eq_j1EDist]
      exact hj1.trans_lt hlt
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hed
    exact hed
  exact (hpos (r / 2) (half_pos hr)).trans_le
    (measure_mono (by simpa only [neg_div] using hsub))

/-- A straight path in the support of a càdlàg path law gives positive mass
to every open corridor containing that path and its endpoint. -/
theorem measure_skorokhodCorridorEndsIn_pos_of_straightPath_mem_support
    (Q : Measure (CadlagPath unitInterval ℝ))
    {lower upper endpointLower endpointUpper y : ℝ}
    (hzero : lower < 0 ∧ 0 < upper)
    (hy : lower < y ∧ y < upper)
    (hend : endpointLower < y ∧ y < endpointUpper)
    (hsupport : Skorokhod.straightPath y ∈ Q.support) :
    0 < Q (Skorokhod.rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper) := by
  have hmem := Skorokhod.straightPath_mem_rangeInOpenIntervalEndsIn
    hzero hy hend
  exact (Measure.mem_support_iff_forall _).mp hsupport _
    ((Skorokhod.isOpen_rangeInOpenIntervalEndsIn
      lower upper endpointLower endpointUpper).mem_nhds hmem)

end MeasureTheory.CadlagPath

end
