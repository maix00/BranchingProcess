/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.EDistance
public import Topology.Cadlag.Skorokhod.Topology
public import Topology.Cadlag.Skorokhod.LinearPath
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Spatial scaling of càdlàg paths

Spatial scaling is a deterministic operation on path space. Its continuity
for the Skorokhod J1 topology is useful independently of probability laws.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace Skorokhod

/-- Pointwise scalar multiplication of a real-valued càdlàg path. -/
def scalePath (scale : ℝ) (f : CadlagPath unitInterval ℝ) :
    CadlagPath unitInterval ℝ :=
  ⟨fun t => scale * f t, f.isCadlag_toFun.const_smul scale⟩

@[simp]
theorem scalePath_apply (scale : ℝ) (f : CadlagPath unitInterval ℝ)
    (t : unitInterval) :
    scalePath scale f t = scale * f t := rfl

/-- Scaling both paths by a fixed scalar is Lipschitz up to the larger of
one and the scalar's absolute value. The factor one accounts for the time
change part of the J1 distance, which spatial scaling does not change. -/
theorem j1EDist_scalePath_le (scale : ℝ)
    (f g : CadlagPath unitInterval ℝ) :
    j1EDist (scalePath scale f) (scalePath scale g) ≤
      ENNReal.ofReal (max 1 |scale|) * j1EDist f g := by
  let C : ℝ := max 1 |scale|
  have hC₁ : 1 ≤ C := le_max_left _ _
  have hCs : |scale| ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC₁
  have hact (change : TimeChange) :
      change.act (scalePath scale f) = scalePath scale (change.act f) := by
    ext t
    rfl
  have huniform (change : TimeChange) :
      uniformEDist (change.act (scalePath scale f)) (scalePath scale g) ≤
        ENNReal.ofReal C * uniformEDist (change.act f) g := by
    have hpoint (t : unitInterval) :
        edist (scale * (change.act f t)) (scale * g t) =
          ENNReal.ofReal |scale| * edist (change.act f t) (g t) := by
      calc
        edist (scale * (change.act f t)) (scale * g t) =
            (‖scale‖₊ : ℝ≥0∞) * edist (change.act f t) (g t) := by
              simpa only [smul_eq_mul, ENNReal.smul_def] using
                edist_smul₀ scale (change.act f t) (g t)
        _ = ENNReal.ofReal |scale| * edist (change.act f t) (g t) := by
          congr 1
          rw [ENNReal.coe_nnreal_eq]
          exact congrArg ENNReal.ofReal
            ((coe_nnnorm scale).trans (Real.norm_eq_abs scale))
    rw [uniformEDist_eq_edist, UniformFun.edist_def,
      uniformEDist_eq_edist, UniformFun.edist_def]
    change (⨆ t : unitInterval,
        edist (scale * (change.act f t)) (scale * g t)) ≤
      ENNReal.ofReal C * uniformEDist (change.act f) g
    refine iSup_le fun t => ?_
    rw [hpoint t]
    exact (mul_le_mul_of_nonneg_left
      (edist_apply_le_uniformEDist (change.act f) g t) bot_le).trans
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCs) bot_le)
  have hcost (change : TimeChange) :
      j1Cost (scalePath scale f) (scalePath scale g) change ≤
        ENNReal.ofReal C * j1Cost f g change := by
    have hd : ENNReal.ofReal change.distortion ≤
        ENNReal.ofReal C * ENNReal.ofReal change.distortion := by
      rw [← ENNReal.ofReal_mul (le_of_lt hCpos)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [change.distortion_nonneg]
    have hu := huniform change
    unfold j1Cost
    refine max_le ?_ ?_
    · exact hd.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) bot_le)
    · exact hu.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) bot_le)
  calc
    j1EDist (scalePath scale f) (scalePath scale g) =
        ⨅ change : TimeChange,
          j1Cost (scalePath scale f) (scalePath scale g) change := rfl
    _ ≤ ⨅ change : TimeChange, ENNReal.ofReal C * j1Cost f g change :=
      iInf_mono hcost
    _ = ENNReal.ofReal C * j1EDist f g := by
      rw [← ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hCpos)
        ENNReal.ofReal_ne_top]
      rfl

/-- Spatial scaling sends a `J₁` ball around a linear path into the
corresponding ball around the scaled linear path. The radius is multiplied by
`max 1 |scale|`, the Lipschitz factor for spatial scaling in `J₁`. -/
theorem dist_scalePath_linearPath_lt
    {path : CadlagPath unitInterval ℝ} {scale slope radius : ℝ}
    (hpath : dist path (linearPath slope) < radius) :
    dist (scalePath scale path) (linearPath (scale * slope)) <
      max 1 |scale| * radius := by
  let C : ℝ := max 1 |scale|
  have hC₁ : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC₁
  have hcenter : scalePath scale (linearPath slope) =
      linearPath (scale * slope) := by
    ext t
    simp [scalePath, linearPath, ofContinuousMap_apply]
    ring
  have hscaled : edist (scalePath scale path)
      (scalePath scale (linearPath slope)) ≤
        ENNReal.ofReal C * edist path (linearPath slope) := by
    rw [edist_cadlagPath_eq_j1EDist, edist_cadlagPath_eq_j1EDist]
    exact j1EDist_scalePath_le scale path (linearPath slope)
  have hscaledReal : ENNReal.ofReal
      (dist (scalePath scale path) (linearPath (scale * slope))) ≤
        ENNReal.ofReal (C * dist path (linearPath slope)) := by
    rw [← hcenter]
    calc
      ENNReal.ofReal
          (dist (scalePath scale path)
            (scalePath scale (linearPath slope))) =
        edist (scalePath scale path)
          (scalePath scale (linearPath slope)) := by rw [edist_dist]
      _ ≤ ENNReal.ofReal C * edist path (linearPath slope) := hscaled
      _ = ENNReal.ofReal (C * dist path (linearPath slope)) := by
        rw [edist_dist, ENNReal.ofReal_mul hCpos.le]
  have hdist : dist (scalePath scale path)
      (linearPath (scale * slope)) ≤ C * dist path (linearPath slope) :=
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hCpos.le (dist_nonneg : 0 ≤ dist path (linearPath slope)))).mp
        hscaledReal
  calc
    dist (scalePath scale path) (linearPath (scale * slope)) ≤
        max 1 |scale| * dist path (linearPath slope) := hdist
    _ < max 1 |scale| * radius :=
      (mul_lt_mul_of_pos_left hpath hCpos)

private theorem exists_norm_bound (f : CadlagPath unitInterval ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |f t| ≤ C := by
  have hbdd : Bornology.IsBounded (Set.range f) := by
    simpa only [Set.image_univ] using
      isBounded_image_of_isCadlag_of_isCompact f.isCadlag_toFun
        (isCompact_univ : IsCompact (Set.univ : Set unitInterval))
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hbdd
  refine ⟨max R 0, le_max_right _ _, fun t => ?_⟩
  have ht : f t ∈ Metric.closedBall (0 : ℝ) R := hR ⟨t, rfl⟩
  have hdist : dist (f t) 0 ≤ R := Metric.mem_closedBall.mp ht
  rw [Real.dist_eq, sub_zero] at hdist
  exact hdist.trans (le_max_left _ _)

private theorem uniformEDist_scalePath_scale_le
    {C : ℝ} (r s : ℝ) (f : CadlagPath unitInterval ℝ)
    (hbound : ∀ t, |f t| ≤ C) :
    uniformEDist (scalePath r f) (scalePath s f) ≤
      ENNReal.ofReal (|r - s| * C) := by
  rw [uniformEDist_eq_edist, UniformFun.edist_def]
  change (⨆ t : unitInterval, edist (r * f t) (s * f t)) ≤
    ENNReal.ofReal (|r - s| * C)
  refine iSup_le fun t => ?_
  rw [edist_dist, Real.dist_eq,
    show r * f t - s * f t = (r - s) * f t by ring, abs_mul]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (hbound t) (abs_nonneg (r - s)))

/-- Scalar multiplication acts continuously on real-valued càdlàg paths in
the Skorokhod J1 topology. -/
theorem continuous_scalePath :
    Continuous (fun p : ℝ × CadlagPath unitInterval ℝ =>
      scalePath p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases p with ⟨r, f⟩
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  obtain ⟨C, hC, hbound⟩ := exists_norm_bound f
  have hfactor : Tendsto
      (fun q : ℝ × CadlagPath unitInterval ℝ =>
        ENNReal.ofReal (max 1 |q.1|))
      (𝓝 (r, f)) (𝓝 (ENNReal.ofReal (max 1 |r|))) := by
    have hinner : Continuous
        (fun q : ℝ × CadlagPath unitInterval ℝ => max 1 |q.1|) := by fun_prop
    have hcont := ENNReal.continuous_ofReal.comp hinner
    exact hcont.continuousAt
  have hpath : Tendsto
      (fun q : ℝ × CadlagPath unitInterval ℝ => edist q.2 f)
    (𝓝 (r, f)) (𝓝 0) := by
    have hcont : Continuous
        (fun q : ℝ × CadlagPath unitInterval ℝ => edist q.2 f) :=
      continuous_edist.comp (continuous_snd.prodMk continuous_const)
    have hca := hcont.continuousAt (x := (r, f))
    simpa using hca.tendsto
  have hfirst : Tendsto
      (fun q : ℝ × CadlagPath unitInterval ℝ =>
        ENNReal.ofReal (max 1 |q.1|) * edist q.2 f)
      (𝓝 (r, f)) (𝓝 0) := by
    have hmul := ENNReal.Tendsto.mul hfactor
      (Or.inr (by simp : (0 : ℝ≥0∞) ≠ ∞)) hpath
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using hmul
  have hsecond : Tendsto
      (fun q : ℝ × CadlagPath unitInterval ℝ =>
        ENNReal.ofReal (|q.1 - r| * C))
      (𝓝 (r, f)) (𝓝 0) := by
    have hinner : Continuous
        (fun q : ℝ × CadlagPath unitInterval ℝ => |q.1 - r| * C) := by fun_prop
    have hcont := ENNReal.continuous_ofReal.comp hinner
    have hca := hcont.continuousAt (x := (r, f))
    change Tendsto (fun q : ℝ × CadlagPath unitInterval ℝ =>
      ENNReal.ofReal (|q.1 - r| * C)) (𝓝 (r, f))
      (𝓝 (ENNReal.ofReal (|r - r| * C))) at hca
    simpa using hca
  have hsum : Tendsto
      (fun q : ℝ × CadlagPath unitInterval ℝ =>
        ENNReal.ofReal (max 1 |q.1|) * edist q.2 f +
          ENNReal.ofReal (|q.1 - r| * C))
      (𝓝 (r, f)) (𝓝 0) := by
    simpa using hfirst.add hsecond
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum ?_ ?_
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun q =>
    calc
      edist (scalePath q.1 q.2) (scalePath r f) ≤
          edist (scalePath q.1 q.2) (scalePath q.1 f) +
            edist (scalePath q.1 f) (scalePath r f) := edist_triangle _ _ _
      _ ≤ ENNReal.ofReal (max 1 |q.1|) * edist q.2 f +
            uniformEDist (scalePath q.1 f) (scalePath r f) := by
        apply add_le_add
        · rw [edist_cadlagPath_eq_j1EDist, edist_cadlagPath_eq_j1EDist]
          exact j1EDist_scalePath_le q.1 q.2 f
        · rw [edist_cadlagPath_eq_j1EDist]
          exact j1EDist_le_uniformEDist _ _
      _ ≤ ENNReal.ofReal (max 1 |q.1|) * edist q.2 f +
            ENNReal.ofReal (|q.1 - r| * C) := by
        exact add_le_add le_rfl
          (uniformEDist_scalePath_scale_le q.1 r f hbound)

end Skorokhod

end
