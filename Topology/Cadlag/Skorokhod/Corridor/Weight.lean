/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint
public import Topology.MetricSpace.Cutoff

/-!
# Continuous weights for strict corridor events

## Public declarations

- `Skorokhod.corridorCutoff`: the clipped distance from a path to the
  complement of the open corridor, taking values in `[0,1]`.
- `Skorokhod.endpointCutoff`: the clipped distance of the terminal value to
  the boundary of an open interval, taking values in `[0,1]`.
- `Skorokhod.corridorEndsInWeight`: the product of corridor and endpoint
  cutoffs; `Skorokhod.corridorPotentialWeight` multiplies the corridor cutoff
  by a terminal potential.
- `Skorokhod.continuous_corridorCutoff`,
  `Skorokhod.continuous_endpointCutoff`,
  `Skorokhod.continuous_corridorEndsInWeight`, and
  `Skorokhod.continuous_corridorPotentialWeight`: these weights are continuous
  when the potential is continuous.
- `Skorokhod.corridorCutoff_nonneg`, `Skorokhod.corridorCutoff_le_one`,
  `Skorokhod.endpointCutoff_nonneg`, and `Skorokhod.endpointCutoff_le_one`:
  the two cutoffs lie in `[0,1]`.
- `Skorokhod.corridorCutoff_pos_iff` and
  `Skorokhod.endpointCutoff_pos_iff`: each cutoff is positive exactly on its
  corresponding open event.
- `Skorokhod.corridorEndsInWeight_nonneg`,
  `Skorokhod.corridorEndsInWeight_le_one`, and
  `Skorokhod.corridorEndsInWeight_pos_iff`: the product weight lies in `[0,1]`
  and is positive exactly on the corridor with endpoint window.
- `Skorokhod.corridorPotentialWeight_nonneg`,
  `Skorokhod.corridorPotentialWeight_le_one`, and
  `Skorokhod.corridorPotentialWeight_pos_iff`: for nonnegative potential,
  the product is nonnegative, is at most `1` when the potential is at most
  `1`, and is positive exactly when the path lies in the corridor and its
  terminal potential is positive.

An open corridor and a terminal interval determine a continuous, bounded
path weight that vanishes outside the event. This gives a continuous-test
function interface for Portmanteau arguments with endpoint weights.

For \(\mathcal O_{a,b}=\operatorname{rangeInOpenInterval}(a,b)\), the
cutoff is \(\phi_{a,b}(f)=\min\{1,\operatorname{infDist}
(f,\mathcal O_{a,b}^{c})\}\). The endpoint cutoff is the same clipped
distance from \(f(1)\) to \((c,d)^c\), and the joint weight is their product.
Each cutoff lies in \([0,1]\) and is positive exactly on its open event.
-/

@[expose] public section

namespace Skorokhod

/-- A continuous cutoff measuring how far a càdlàg path lies inside an open
corridor. It vanishes on the complement and is positive at every point of the
open corridor. -/
noncomputable def corridorCutoff (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) : ℝ :=
  Metric.openSetCutoff (rangeInOpenInterval lower upper) path

/-- A continuous cutoff measuring how far the terminal value lies inside an
open interval. -/
noncomputable def endpointCutoff (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) : ℝ :=
  Metric.openSetCutoff (Set.Ioo lower upper) (path ⊤)

/-- The product cutoff for a strict corridor event with an open terminal
constraint. -/
noncomputable def corridorEndsInWeight (lower upper endpointLower endpointUpper : ℝ)
    (path : CadlagPath unitInterval ℝ) : ℝ :=
  corridorCutoff lower upper path * endpointCutoff endpointLower endpointUpper path

/-- A corridor cutoff multiplied by a nonnegative endpoint potential. This
form is suited to positive test functions for killed transition operators. -/
noncomputable def corridorPotentialWeight (lower upper : ℝ)
    (potential : ℝ → ℝ) (path : CadlagPath unitInterval ℝ) : ℝ :=
  corridorCutoff lower upper path * potential (path ⊤)

theorem continuous_corridorCutoff (lower upper : ℝ) :
    Continuous (corridorCutoff lower upper) :=
  Metric.continuous_openSetCutoff _

theorem continuous_endpointCutoff (lower upper : ℝ) :
    Continuous (endpointCutoff lower upper) :=
  (Metric.continuous_openSetCutoff (Set.Ioo lower upper)).comp
    continuous_apply_top

theorem continuous_corridorEndsInWeight
    (lower upper endpointLower endpointUpper : ℝ) :
    Continuous (corridorEndsInWeight lower upper endpointLower endpointUpper) := by
  unfold corridorEndsInWeight
  exact (continuous_corridorCutoff lower upper).mul
    (continuous_endpointCutoff endpointLower endpointUpper)

theorem continuous_corridorPotentialWeight
    (lower upper : ℝ) {potential : ℝ → ℝ} (hpotential : Continuous potential) :
    Continuous (corridorPotentialWeight lower upper potential) := by
  unfold corridorPotentialWeight
  exact (continuous_corridorCutoff lower upper).mul
    (hpotential.comp continuous_apply_top)

theorem corridorCutoff_nonneg (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    0 ≤ corridorCutoff lower upper path :=
  Metric.openSetCutoff_nonneg _ _

theorem corridorCutoff_le_one (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    corridorCutoff lower upper path ≤ 1 :=
  Metric.openSetCutoff_le_one _ _

theorem endpointCutoff_nonneg (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    0 ≤ endpointCutoff lower upper path :=
  Metric.openSetCutoff_nonneg _ _

theorem endpointCutoff_le_one (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    endpointCutoff lower upper path ≤ 1 :=
  Metric.openSetCutoff_le_one _ _

theorem corridorCutoff_pos_iff {lower upper : ℝ}
    (path : CadlagPath unitInterval ℝ) :
    0 < corridorCutoff lower upper path ↔
      path ∈ rangeInOpenInterval lower upper := by
  have hcomplement : (rangeInOpenInterval lower upper)ᶜ.Nonempty := by
    let outside : CadlagPath unitInterval ℝ :=
      ofContinuousMap (ContinuousMap.const unitInterval (upper + 1))
    refine ⟨outside, ?_⟩
    change outside ∉ rangeInOpenInterval lower upper
    rw [mem_rangeInOpenInterval_iff]
    rintro ⟨margin, hmargin, hall⟩
    have hUpper := (hall ⊥).2
    change upper + 1 ≤ upper - margin at hUpper
    linarith
  simpa [corridorCutoff] using
    (Metric.openSetCutoff_pos_iff
      (isOpen_rangeInOpenInterval lower upper) hcomplement path)

theorem endpointCutoff_pos_iff {lower upper : ℝ}
    (path : CadlagPath unitInterval ℝ) :
    0 < endpointCutoff lower upper path ↔
      path ⊤ ∈ Set.Ioo lower upper := by
  simpa [endpointCutoff] using
    (Metric.openSetCutoff_pos_iff isOpen_Ioo
      (s := Set.Ioo lower upper) ⟨lower, by simp⟩ (path ⊤))

theorem corridorEndsInWeight_nonneg
    (lower upper endpointLower endpointUpper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    0 ≤ corridorEndsInWeight lower upper endpointLower endpointUpper path :=
  mul_nonneg (corridorCutoff_nonneg _ _ _) (endpointCutoff_nonneg _ _ _)

theorem corridorEndsInWeight_le_one
    (lower upper endpointLower endpointUpper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    corridorEndsInWeight lower upper endpointLower endpointUpper path ≤ 1 := by
  calc
    corridorCutoff lower upper path * endpointCutoff endpointLower endpointUpper path ≤
        1 * endpointCutoff endpointLower endpointUpper path :=
      mul_le_mul_of_nonneg_right (corridorCutoff_le_one _ _ _)
        (endpointCutoff_nonneg _ _ _)
    _ = endpointCutoff endpointLower endpointUpper path := one_mul _
    _ ≤ 1 := endpointCutoff_le_one _ _ _

theorem corridorEndsInWeight_pos_iff
    (lower upper endpointLower endpointUpper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    0 < corridorEndsInWeight lower upper endpointLower endpointUpper path ↔
      path ∈ rangeInOpenInterval lower upper ∧
        path ⊤ ∈ Set.Ioo endpointLower endpointUpper := by
  rw [corridorEndsInWeight]
  constructor
  · intro h
    have hcorridorNe : corridorCutoff lower upper path ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at h
      exact (lt_irrefl 0) h
    have hendpointNe : endpointCutoff endpointLower endpointUpper path ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at h
      exact (lt_irrefl 0) h
    have hcorridorPos : 0 < corridorCutoff lower upper path :=
      lt_of_le_of_ne (corridorCutoff_nonneg _ _ _) (Ne.symm hcorridorNe)
    have hendpointPos : 0 < endpointCutoff endpointLower endpointUpper path :=
      lt_of_le_of_ne (endpointCutoff_nonneg _ _ _) (Ne.symm hendpointNe)
    exact ⟨(corridorCutoff_pos_iff path).mp hcorridorPos,
      (endpointCutoff_pos_iff path).mp hendpointPos⟩
  · rintro ⟨hcorridor, hendpoint⟩
    exact mul_pos ((corridorCutoff_pos_iff path).mpr hcorridor)
      ((endpointCutoff_pos_iff path).mpr hendpoint)

theorem corridorPotentialWeight_nonneg
    (lower upper : ℝ) (potential : ℝ → ℝ)
    (hpotential : ∀ x, 0 ≤ potential x) (path : CadlagPath unitInterval ℝ) :
    0 ≤ corridorPotentialWeight lower upper potential path :=
  mul_nonneg (corridorCutoff_nonneg lower upper path)
    (hpotential (path ⊤))

theorem corridorPotentialWeight_le_one
    (lower upper : ℝ) (potential : ℝ → ℝ)
    (hpotentialNonneg : ∀ x, 0 ≤ potential x)
    (hpotentialLeOne : ∀ x, potential x ≤ 1)
    (path : CadlagPath unitInterval ℝ) :
    corridorPotentialWeight lower upper potential path ≤ 1 := by
  calc
    corridorCutoff lower upper path * potential (path ⊤) ≤
        1 * potential (path ⊤) :=
      mul_le_mul_of_nonneg_right (corridorCutoff_le_one _ _ _)
        (hpotentialNonneg (path ⊤))
    _ = potential (path ⊤) := one_mul _
    _ ≤ 1 := hpotentialLeOne _

theorem corridorPotentialWeight_pos_iff
    (lower upper : ℝ) (potential : ℝ → ℝ)
    (hpotential : ∀ x, 0 ≤ potential x)
    (path : CadlagPath unitInterval ℝ) :
    0 < corridorPotentialWeight lower upper potential path ↔
      path ∈ rangeInOpenInterval lower upper ∧ 0 < potential (path ⊤) := by
  unfold corridorPotentialWeight
  constructor
  · intro h
    have hcut : 0 < corridorCutoff lower upper path := by
      by_contra hnot
      have hz : corridorCutoff lower upper path = 0 :=
        le_antisymm (le_of_not_gt hnot) (corridorCutoff_nonneg _ _ _)
      rw [hz, zero_mul] at h
      exact (not_lt_of_ge le_rfl) h
    have hvalue : 0 < potential (path ⊤) := by
      by_contra hnot
      have hz : potential (path ⊤) = 0 :=
        le_antisymm (le_of_not_gt hnot) (hpotential (path ⊤))
      rw [hz, mul_zero] at h
      exact (not_lt_of_ge le_rfl) h
    exact ⟨(corridorCutoff_pos_iff path).mp hcut, hvalue⟩
  · rintro ⟨hcorridor, hvalue⟩
    exact mul_pos ((corridorCutoff_pos_iff path).mpr hcorridor) hvalue

end Skorokhod
