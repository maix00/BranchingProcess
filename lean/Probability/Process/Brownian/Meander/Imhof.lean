/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Meander.Corridor
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Topology.Cadlag.Skorokhod.Endpoint
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Imhof density on path space

The public objects and theorems in this file are:

- `BrownianMeander.imhofWeight`: the endpoint density
  $f\mapsto\sqrt{\pi/2}/f(1)$, interpreted as zero at nonpositive endpoints.
- `BrownianMeander.imhofTilt`: the measure obtained by weighting a path law
  with this density, $\nu^{\mathrm{Imhof}}=\nu\cdot w$.
- `BrownianMeander.measurable_imhofWeight`: $w$ is Borel measurable.
- `BrownianMeander.imhofWeight_pos_of_endpoint_pos`: a positive endpoint
  gives a strictly positive density.
- `BrownianMeander.measure_openCorridor_pos_imhofTilt`: a Bessel path law
  whose support contains the straight path gives positive mass to the
  meander corridor after the Imhof tilt.

The density is the one in Jean-Pierre Imhof, *Density factorizations for
Brownian motion, meander and the three-dimensional Bessel process, and
applications*, Journal of Applied Probability 21 (1984), 500--510,
Theorem 1. The radial Bessel path law is constructed separately. The
normalization identity for this density remains to be formalized.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Topology

namespace BrownianMeander

/-- The Imhof endpoint density, evaluated on a Skorokhod path. The real
quotient is sent to zero when the endpoint is nonpositive. -/
noncomputable def imhofWeight (path : CadlagPath unitInterval ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (Real.pi / 2) / path ⊤)

/-- Weight a three-dimensional Bessel path law by the Imhof endpoint
density. When the input is the standard BES(3) law, Imhof's theorem
identifies this measure with standard Brownian meander. -/
noncomputable def imhofTilt (besselLaw : Measure (CadlagPath unitInterval ℝ)) :
    Measure (CadlagPath unitInterval ℝ) :=
  besselLaw.withDensity imhofWeight

theorem measurable_imhofWeight : Measurable imhofWeight := by
  unfold imhofWeight
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.div Skorokhod.continuous_apply_top.measurable)

/-- The Imhof density is positive at every path with positive endpoint. -/
theorem imhofWeight_pos_of_endpoint_pos
    {path : CadlagPath unitInterval ℝ} (hend : 0 < path ⊤) :
    0 < imhofWeight path := by
  unfold imhofWeight
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (Real.sqrt_pos.2 (by exact half_pos Real.pi_pos)) hend

/-- The Imhof tilt gives positive mass to the corridor whenever the
underlying Bessel law has the requisite straight path in its support. -/
theorem measure_openCorridor_pos_imhofTilt
    {besselLaw : Measure (CadlagPath unitInterval ℝ)}
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      besselLaw.support) :
    0 < imhofTilt besselLaw (openCorridor sigma rho) := by
  have hbase : 0 < besselLaw (openCorridor sigma rho) :=
    measure_openCorridor_pos_of_straightPath_mem_support
      hsigma hrho hrhoSmall hsupport
  have hne : imhofTilt besselLaw (openCorridor sigma rho) ≠ 0 := by
    intro hzero
    change besselLaw.withDensity imhofWeight (openCorridor sigma rho) = 0 at hzero
    rw [withDensity_apply_eq_zero measurable_imhofWeight] at hzero
    have hsubset : openCorridor sigma rho ⊆
        {path | imhofWeight path ≠ 0} := by
      intro path hpath
      have hend : (5 / 12 + rho) / sigma < path ⊤ := hpath.2.1
      have hendpos : 0 < path ⊤ :=
        (div_pos (by linarith) hsigma).trans hend
      exact ne_of_gt (imhofWeight_pos_of_endpoint_pos hendpos)
    have hinter : {path | imhofWeight path ≠ 0} ∩
        openCorridor sigma rho = openCorridor sigma rho :=
      Set.inter_eq_right.mpr hsubset
    rw [hinter] at hzero
    exact (ne_of_gt hbase) hzero
  exact pos_iff_ne_zero.mpr hne

end BrownianMeander

end
