/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.Separation
public import Topology.Cadlag.Skorokhod.Topology

/-!
# The logarithmic metric on càdlàg paths

This file bundles càdlàg paths with Billingsley's logarithmic metric and proves
that forgetting this metric structure is uniformly continuous into the usual
Skorokhod `J₁` path space.
-/

@[expose] public section

open scoped ENNReal

namespace Skorokhod

/-- A càdlàg path viewed with Billingsley's logarithmic Skorokhod distance. -/
structure BillingsleyPath (E : Type*) [TopologicalSpace E] where
  toCadlagPath : CadlagPath unitInterval E

namespace BillingsleyPath

@[ext]
theorem ext {E : Type*} [TopologicalSpace E] {f g : BillingsleyPath E}
    (h : f.toCadlagPath = g.toCadlagPath) : f = g := by
  cases f
  cases g
  cases h
  rfl

end BillingsleyPath

theorem billingsleyEDist_ne_top {E : Type*} [MetricSpace E]
    (f g : CadlagPath unitInterval E) : billingsleyEDist f g ≠ ∞ := by
  apply ne_top_of_le_ne_top (uniformEDist_ne_top f g)
  calc
    billingsleyEDist f g ≤ billingsleyCost f g TimeChange.refl :=
      billingsleyEDist_le_cost f g TimeChange.refl
    _ = uniformEDist f g := by simp [billingsleyCost]

noncomputable instance instEMetricSpaceBillingsleyPath {E : Type*}
    [MetricSpace E] : EMetricSpace (BillingsleyPath E) where
  edist f g := billingsleyEDist f.toCadlagPath g.toCadlagPath
  edist_self f := billingsleyEDist_self f.toCadlagPath
  edist_comm f g := billingsleyEDist_comm f.toCadlagPath g.toCadlagPath
  edist_triangle f g h :=
    billingsleyEDist_triangle f.toCadlagPath g.toCadlagPath h.toCadlagPath
  eq_of_edist_eq_zero := by
    intro f g h
    apply BillingsleyPath.ext
    exact billingsleyEDist_eq_zero_imp h

noncomputable instance instMetricSpaceBillingsleyPath {E : Type*}
    [MetricSpace E] : MetricSpace (BillingsleyPath E) :=
  EMetricSpace.toMetricSpace fun f g =>
    billingsleyEDist_ne_top f.toCadlagPath g.toCadlagPath

/-- The identity on paths from the logarithmic metric space to the usual `J₁`
metric space is uniformly continuous. -/
theorem uniformContinuous_toCadlagPath {E : Type*} [MetricSpace E] :
    UniformContinuous (fun f : BillingsleyPath E => f.toCadlagPath) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨bound, hbound, hboundε, hmodε⟩ :=
    exists_small_logarithmicJ1_bound hε
  refine ⟨bound, hbound, ?_⟩
  intro f g hfg
  have hd0 : billingsleyEDist f.toCadlagPath g.toCadlagPath <
      ENNReal.ofReal bound := by
    change edist f g < ENNReal.ofReal bound
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hbound]
    exact hfg
  have hj1 : j1EDist f.toCadlagPath g.toCadlagPath ≤
      ENNReal.ofReal (logarithmicJ1Modulus bound) :=
    j1EDist_le_modulus_of_billingsleyEDist_lt f.toCadlagPath g.toCadlagPath
      hbound.le hd0
  have hj1lt : j1EDist f.toCadlagPath g.toCadlagPath < ENNReal.ofReal ε :=
    hj1.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 hmodε)
  have hj1edist : edist f.toCadlagPath g.toCadlagPath < ENNReal.ofReal ε := by
    change j1EDist f.toCadlagPath g.toCadlagPath < _
    exact hj1lt
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] at hj1edist
  exact hj1edist

end Skorokhod
