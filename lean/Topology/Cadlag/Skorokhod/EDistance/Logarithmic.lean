/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.EDistance
public import Topology.Cadlag.Skorokhod.TimeChange.LogDistortion

/-!
# Logarithmic Skorokhod distance

This file defines Billingsley's logarithmic time-change cost and proves its
extended-distance axioms. Completeness and equivalence with the usual
Skorokhod topology are separate results and are not assumed here.
-/

@[expose] public section

open scoped ENNReal

namespace Skorokhod

/-- Billingsley's cost for a specified Skorokhod time change. -/
noncomputable def billingsleyCost {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) : ℝ≥0∞ :=
  max change.logDistortion (uniformEDist (change.act f) g)

theorem billingsleyCost_symm {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) :
    billingsleyCost f g change = billingsleyCost g f change.symm := by
  unfold billingsleyCost
  rw [TimeChange.logDistortion_symm, uniformEDist_act_symm]

theorem billingsleyCost_trans_le {E : Type*} [EMetricSpace E]
    (f g h : CadlagPath unitInterval E) (first second : TimeChange) :
    billingsleyCost f h (first.trans second) ≤
      billingsleyCost f g second + billingsleyCost g h first := by
  apply max_le
  · calc
      (first.trans second).logDistortion ≤ first.logDistortion + second.logDistortion :=
        TimeChange.logDistortion_trans_le first second
      _ = second.logDistortion + first.logDistortion := add_comm _ _
      _ ≤ billingsleyCost f g second + billingsleyCost g h first :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact (uniformEDist_trans_act_le f g h first second).trans <|
      add_le_add (le_max_right _ _) (le_max_right _ _)

/-- The extended path distance obtained by infimizing Billingsley's cost over
all strictly increasing homeomorphic time changes. -/
noncomputable def billingsleyEDist {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) : ℝ≥0∞ :=
  ⨅ change : TimeChange, billingsleyCost f g change

theorem billingsleyEDist_le_cost {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) :
    billingsleyEDist f g ≤ billingsleyCost f g change :=
  iInf_le _ change

theorem billingsleyEDist_comm {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) :
    billingsleyEDist f g = billingsleyEDist g f := by
  apply le_antisymm
  · refine le_iInf fun change ↦ ?_
    calc
      billingsleyEDist f g ≤ billingsleyCost f g change.symm :=
        billingsleyEDist_le_cost f g change.symm
      _ = billingsleyCost g f change := by
        rw [billingsleyCost_symm, TimeChange.symm_symm]
  · refine le_iInf fun change ↦ ?_
    calc
      billingsleyEDist g f ≤ billingsleyCost g f change.symm :=
        billingsleyEDist_le_cost g f change.symm
      _ = billingsleyCost f g change := by
        rw [billingsleyCost_symm, TimeChange.symm_symm]

theorem billingsleyEDist_triangle {E : Type*} [EMetricSpace E]
    (f g h : CadlagPath unitInterval E) :
    billingsleyEDist f h ≤ billingsleyEDist f g + billingsleyEDist g h := by
  calc
    billingsleyEDist f h ≤
        ⨅ second : TimeChange, ⨅ first : TimeChange,
          billingsleyCost f g second + billingsleyCost g h first := by
      refine le_iInf fun second ↦ le_iInf fun first ↦ ?_
      exact (billingsleyEDist_le_cost f h (first.trans second)).trans
        (billingsleyCost_trans_le f g h first second)
    _ = (⨅ second : TimeChange, billingsleyCost f g second) +
        ⨅ first : TimeChange, billingsleyCost g h first := by
      simp_rw [← ENNReal.add_iInf]
      rw [← ENNReal.iInf_add]
    _ = billingsleyEDist f g + billingsleyEDist g h := rfl

@[simp]
theorem billingsleyEDist_self {E : Type*} [EMetricSpace E]
    (f : CadlagPath unitInterval E) : billingsleyEDist f f = 0 := by
  apply le_antisymm
  · calc
      billingsleyEDist f f ≤ billingsleyCost f f TimeChange.refl :=
        billingsleyEDist_le_cost f f TimeChange.refl
      _ = 0 := by simp [billingsleyCost]
  · exact bot_le

end Skorokhod
