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

/-- Real error bound converting a logarithmic time-change cost into the usual
`J₁` cost. -/
noncomputable def logarithmicJ1Modulus (bound : ℝ) : ℝ :=
  max (Real.exp bound - Real.exp (-bound)) bound

/-- The conversion modulus vanishes at zero. -/
@[simp]
theorem logarithmicJ1Modulus_zero : logarithmicJ1Modulus 0 = 0 := by
  simp [logarithmicJ1Modulus]

/-- The conversion modulus is continuous, hence vanishes along bounds tending
to zero. -/
theorem continuous_logarithmicJ1Modulus : Continuous logarithmicJ1Modulus := by
  fun_prop [logarithmicJ1Modulus]

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

/-- A small Billingsley cost gives a small ordinary `J₁` cost for the same
time change. The exponential term is the deterministic conversion from
logarithmic secant control to uniform clock displacement. -/
theorem j1Cost_le_max_of_billingsleyCost_le {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hcost : billingsleyCost f g change ≤ ENNReal.ofReal bound) :
    j1Cost f g change ≤
      max (ENNReal.ofReal (Real.exp bound - Real.exp (-bound)))
        (ENNReal.ofReal bound) := by
  have hlog : change.logDistortion ≤ ENNReal.ofReal bound := by
    exact (le_max_left _ _).trans (by simpa [billingsleyCost] using hcost)
  have htimeReal : change.distortion ≤ Real.exp bound - Real.exp (-bound) :=
    TimeChange.distortion_le_exp_sub_exp_neg_of_logDistortion_le change hbound hlog
  have htime : ENNReal.ofReal change.distortion ≤
      ENNReal.ofReal (Real.exp bound - Real.exp (-bound)) :=
    ENNReal.ofReal_le_ofReal htimeReal
  have hspace : uniformEDist (change.act f) g ≤ ENNReal.ofReal bound := by
    exact (le_max_right _ _).trans (by simpa [billingsleyCost] using hcost)
  unfold j1Cost
  exact max_le (htime.trans (le_max_left _ _))
    (hspace.trans (le_max_right _ _))

/-- The ordinary `J₁` distance is bounded by the converted cost of any
specified logarithmic time change. -/
theorem j1EDist_le_max_of_billingsleyCost_le {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hcost : billingsleyCost f g change ≤ ENNReal.ofReal bound) :
    j1EDist f g ≤
      max (ENNReal.ofReal (Real.exp bound - Real.exp (-bound)))
        (ENNReal.ofReal bound) := by
  exact (j1EDist_le_cost f g change).trans
    (j1Cost_le_max_of_billingsleyCost_le f g change hbound hcost)

/-- The ordinary `J₁` distance is controlled by a scalar modulus of a
Billingsley-cost bound. The modulus tends to zero with its argument. -/
theorem j1EDist_le_modulus_of_billingsleyCost_le {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) (change : TimeChange) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hcost : billingsleyCost f g change ≤ ENNReal.ofReal bound) :
    j1EDist f g ≤ ENNReal.ofReal (logarithmicJ1Modulus bound) := by
  calc
    j1EDist f g ≤
        max (ENNReal.ofReal (Real.exp bound - Real.exp (-bound)))
          (ENNReal.ofReal bound) :=
      j1EDist_le_max_of_billingsleyCost_le f g change hbound hcost
    _ = ENNReal.ofReal (logarithmicJ1Modulus bound) := by
      rw [logarithmicJ1Modulus, ENNReal.ofReal_max]

/-- The extended path distance obtained by infimizing Billingsley's cost over
all strictly increasing homeomorphic time changes. -/
noncomputable def billingsleyEDist {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) : ℝ≥0∞ :=
  ⨅ change : TimeChange, billingsleyCost f g change

/-- If the infimum Billingsley distance is strictly below a real bound, then
the ordinary `J₁` distance is controlled by the continuous logarithmic
modulus at that bound. -/
theorem j1EDist_le_modulus_of_billingsleyEDist_lt {E : Type*} [EMetricSpace E]
    (f g : CadlagPath unitInterval E) {bound : ℝ} (hbound : 0 ≤ bound)
    (hdistance : billingsleyEDist f g < ENNReal.ofReal bound) :
    j1EDist f g ≤ ENNReal.ofReal (logarithmicJ1Modulus bound) := by
  have hexists : ∃ change : TimeChange,
      billingsleyCost f g change < ENNReal.ofReal bound := by
    simpa only [billingsleyEDist, iInf_lt_iff] using hdistance
  obtain ⟨change, hcost⟩ := hexists
  exact j1EDist_le_modulus_of_billingsleyCost_le f g change hbound hcost.le

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
