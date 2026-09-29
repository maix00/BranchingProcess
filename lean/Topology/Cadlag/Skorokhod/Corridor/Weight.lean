import Mathlib.Topology.UnitInterval
import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Continuous weights for strict corridor events

An open corridor and a terminal interval determine a continuous, bounded
path weight that vanishes outside the event. This gives a continuous-test
function interface for Portmanteau arguments with endpoint weights.
-/

namespace Skorokhod

/-- A continuous cutoff measuring how far a càdlàg path lies inside an open
corridor. It vanishes on the complement and is positive at every point of the
open corridor. -/
noncomputable def corridorCutoff (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) : ℝ :=
  max 0 (min 1 (Metric.infDist path
    (rangeInOpenInterval lower upper)ᶜ))

/-- A continuous cutoff measuring how far the terminal value lies inside an
open interval. -/
def endpointCutoff (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) : ℝ :=
  max 0 (min 1 (min (path ⊤ - lower) (upper - path ⊤)))

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
    Continuous (corridorCutoff lower upper) := by
  unfold corridorCutoff
  fun_prop

theorem continuous_endpointCutoff (lower upper : ℝ) :
    Continuous (endpointCutoff lower upper) := by
  have heval : Continuous (fun path : CadlagPath unitInterval ℝ => path ⊤) :=
    continuous_apply_top
  have hlower : Continuous (fun path : CadlagPath unitInterval ℝ =>
      path ⊤ - lower) := heval.sub continuous_const
  have hupper : Continuous (fun path : CadlagPath unitInterval ℝ =>
      upper - path ⊤) := continuous_const.sub heval
  unfold endpointCutoff
  exact continuous_const.max
    (continuous_const.min (hlower.min hupper))

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
    0 ≤ corridorCutoff lower upper path := le_max_left _ _

theorem corridorCutoff_le_one (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    corridorCutoff lower upper path ≤ 1 := by
  unfold corridorCutoff
  exact max_le (by norm_num) (min_le_left _ _)

theorem endpointCutoff_nonneg (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    0 ≤ endpointCutoff lower upper path := le_max_left _ _

theorem endpointCutoff_le_one (lower upper : ℝ)
    (path : CadlagPath unitInterval ℝ) :
    endpointCutoff lower upper path ≤ 1 := by
  unfold endpointCutoff
  exact max_le (by norm_num) (min_le_left _ _)

theorem corridorCutoff_pos_iff {lower upper : ℝ}
    (path : CadlagPath unitInterval ℝ) :
    0 < corridorCutoff lower upper path ↔
      path ∈ rangeInOpenInterval lower upper := by
  constructor
  · intro h
    by_contra hmem
    have hzero : Metric.infDist path
        (rangeInOpenInterval lower upper)ᶜ = 0 :=
      Metric.infDist_zero_of_mem hmem
    simp [corridorCutoff, hzero] at h
  · intro hmem
    have hnotempty : (rangeInOpenInterval lower upper)ᶜ.Nonempty := by
      let outside : CadlagPath unitInterval ℝ :=
        ofContinuousMap (ContinuousMap.const unitInterval (upper + 1))
      refine ⟨outside, ?_⟩
      change outside ∉ rangeInOpenInterval lower upper
      rw [mem_rangeInOpenInterval_iff]
      rintro ⟨margin, hmargin, hall⟩
      have hUpper := (hall ⊥).2
      change upper + 1 ≤ upper - margin at hUpper
      linarith
    obtain ⟨radius, hradius, hball⟩ :=
      (Metric.isOpen_iff.mp (isOpen_rangeInOpenInterval lower upper)) path hmem
    have hradiusDist : radius ≤ Metric.infDist path
        (rangeInOpenInterval lower upper)ᶜ :=
      (Metric.le_infDist hnotempty).2 fun q hq => by
        by_contra hdist
        have hstrict : dist path q < radius := lt_of_not_ge hdist
        have hqball : q ∈ Metric.ball path radius := by
          rw [Metric.mem_ball, dist_comm]
          exact hstrict
        have hqnot : q ∉ rangeInOpenInterval lower upper := by
          simpa only [Set.mem_compl_iff] using hq
        exact hqnot (hball hqball)
    unfold corridorCutoff
    rw [max_eq_right (le_min (by norm_num) Metric.infDist_nonneg)]
    exact lt_min_iff.mpr ⟨by norm_num, lt_of_lt_of_le hradius hradiusDist⟩

theorem endpointCutoff_pos_iff {lower upper : ℝ}
    (path : CadlagPath unitInterval ℝ) :
    0 < endpointCutoff lower upper path ↔
      path ⊤ ∈ Set.Ioo lower upper := by
  unfold endpointCutoff
  simp only [lt_max_iff, lt_self_iff_false, false_or]
  constructor
  · intro h
    have hmin : 0 < min (path ⊤ - lower) (upper - path ⊤) :=
      (lt_min_iff.mp h).2
    rcases lt_min_iff.mp hmin with ⟨hl, hu⟩
    exact ⟨sub_pos.mp hl, sub_pos.mp hu⟩
  · rintro ⟨hlower, hupper⟩
    have hmin : 0 < min (path ⊤ - lower) (upper - path ⊤) :=
      lt_min_iff.mpr ⟨sub_pos.mpr hlower, sub_pos.mpr hupper⟩
    exact lt_min_iff.mpr ⟨by norm_num, hmin⟩

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
