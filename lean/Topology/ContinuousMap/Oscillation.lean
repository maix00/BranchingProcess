module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UnitInterval
public import Mathlib.Algebra.Order.Floor.Semiring
public import Topology.ContinuousMap.Corridor

@[expose] public section

noncomputable section

/-!
# Finite corridor covers of continuous paths with bounded oscillation

For a path starting at zero, a bound on its range diameter confines its
minimum to a compact interval of possible locations.  A fixed finite grid of
those locations gives a cover by slightly wider open corridors.  The number
of corridors depends on the relative mesh, not on any discrete approximation
of the path.
-/

open Set

namespace ContinuousMap

/-- A continuous path has oscillation at most `width`. -/
def rangeOscillationLe (width : ℝ) (path : C(unitInterval, ℝ)) : Prop :=
  ∀ s t, |path s - path t| ≤ width

/-- The lower endpoint of the `j`th corridor in the finite minimum-location
cover.  Its mesh is `width / count`. -/
def oscillationCoverLower (width : ℝ) (count : ℕ) (j : Fin count) : ℝ :=
  -width + (j.val : ℝ) * (width / count) - width / count

/-- The upper endpoint of the `j`th corridor in the finite minimum-location
cover. -/
def oscillationCoverUpper (width : ℝ) (count : ℕ) (j : Fin count) : ℝ :=
  -width + (j.val : ℝ) * (width / count) + width + 2 * (width / count)

/-- A zero-starting continuous path with oscillation at most `width` belongs
to one of `count` open corridors.  Every corridor has width
`width * (1 + 3 / count)`. -/
theorem rangeOscillationLe_subset_finiteCorridorCover
    (width : ℝ) (count : ℕ) (hwidth : 0 < width) (hcount : 0 < count) :
    {path : C(unitInterval, ℝ) |
      path 0 = 0 ∧ rangeOscillationLe width path} ⊆
      ⋃ j : Fin count,
        rangeInOpenInterval (oscillationCoverLower width count j)
          (oscillationCoverUpper width count j) := by
  classical
  intro path hpath
  rcases hpath with ⟨hzero, hosc⟩
  obtain ⟨tmin, htmin, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set unitInterval)).exists_isMinOn
      Set.univ_nonempty path.continuous.continuousOn
  let m : ℝ := path tmin
  have hmzero : m ≤ 0 := by
    have := hmin (Set.mem_univ (0 : unitInterval))
    simpa [m, hzero] using this
  have hminus : -width ≤ m := by
    have h := hosc 0 tmin
    rw [hzero] at h
    have := (abs_le.mp h).2
    dsimp [m]
    linarith
  have hdelta : 0 < width / (count : ℝ) :=
    div_pos hwidth (Nat.cast_pos.mpr hcount)
  let delta : ℝ := width / (count : ℝ)
  let q : ℝ := (m + width) / delta
  have hq_nonneg : 0 ≤ q := by
    dsimp [q, delta]
    exact div_nonneg (by linarith) hdelta.le
  have hq_le : q ≤ count := by
    dsimp [q, delta]
    rw [div_le_iff₀ hdelta]
    have hmul : m + width ≤ width := by linarith
    calc
      m + width ≤ width := hmul
      _ = (count : ℝ) * (width / (count : ℝ)) := by
        field_simp [ne_of_gt (Nat.cast_pos.mpr hcount)]
  let jval : ℕ := min ⌊q⌋₊ (count - 1)
  have hjval : jval < count := by
    dsimp [jval]
    exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hcount (by omega))
  let j : Fin count := ⟨jval, hjval⟩
  have hfloorle : ⌊q⌋₊ ≤ count := Nat.floor_le_of_le hq_le
  have hjq_lower : (jval : ℝ) ≤ q := by
    have hj_eq : jval = min ⌊q⌋₊ (count - 1) := rfl
    rw [hj_eq]
    by_cases hf : ⌊q⌋₊ < count
    · rw [Nat.min_eq_left (by omega)]
      exact_mod_cast Nat.floor_le hq_nonneg
    · have heq : ⌊q⌋₊ = count := by omega
      rw [heq, Nat.min_eq_right (by omega)]
      have hqcount : (count : ℝ) ≤ q := by
        exact (Nat.cast_le.mpr (show count ≤ ⌊q⌋₊ by omega)).trans
          (Nat.floor_le hq_nonneg)
      have hjcast : ((count - 1 : ℕ) : ℝ) ≤ (count : ℝ) := by
        exact_mod_cast Nat.sub_le count 1
      exact hjcast.trans hqcount
  have hjq_upper : q ≤ (jval : ℝ) + 1 := by
    have hj_eq : jval = min ⌊q⌋₊ (count - 1) := rfl
    rw [hj_eq]
    by_cases hf : ⌊q⌋₊ < count
    · rw [Nat.min_eq_left (by omega)]
      exact (Nat.lt_floor_add_one q).le
    · have hfge : count ≤ ⌊q⌋₊ := Nat.le_of_not_gt hf
      have heq : ⌊q⌋₊ = count := Nat.le_antisymm hfloorle hfge
      rw [heq, Nat.min_eq_right (by omega)]
      have hqeq : q = count := by
        have h1 : (count : ℝ) ≤ q := by
          exact (Nat.cast_le.mpr hfge).trans (Nat.floor_le hq_nonneg)
        linarith
      rw [hqeq]
      exact_mod_cast (show count ≤ count - 1 + 1 by omega)
  have hgrid_lower : -width + (jval : ℝ) * delta ≤ m := by
    have hjq_lower' : (jval : ℝ) ≤ (m + width) / delta := by
      simpa [q] using hjq_lower
    have h := (le_div_iff₀ hdelta).mp hjq_lower'
    dsimp [delta]
    linarith
  have hgrid_upper : m ≤ -width + (jval : ℝ) * delta + delta := by
    have hjq_upper' : (m + width) / delta ≤ (jval : ℝ) + 1 := by
      simpa [q] using hjq_upper
    have h := (div_le_iff₀ hdelta).mp hjq_upper'
    dsimp [delta]
    linarith
  have hpath_lower (t : unitInterval) : m ≤ path t := by
    exact hmin (Set.mem_univ t)
  have hpath_upper (t : unitInterval) : path t ≤ m + width := by
    have h := hosc tmin t
    dsimp [m] at h ⊢
    linarith [(abs_le.mp h).1]
  have hcover :
      path ∈ rangeInOpenInterval (oscillationCoverLower width count j)
        (oscillationCoverUpper width count j) := by
    rw [mem_rangeInOpenInterval_iff]
    intro t
    have hlow := hpath_lower t
    have hupp := hpath_upper t
    constructor
    · dsimp [oscillationCoverLower, delta]
      linarith
    · dsimp [oscillationCoverUpper, delta]
      linarith
  exact Set.mem_iUnion.mpr ⟨j, hcover⟩

/-- All corridors in the finite minimum-location cover have the same width,
which is the original width plus three mesh lengths. -/
theorem oscillationCoverUpper_sub_lower
    (width : ℝ) (count : ℕ) (j : Fin count) :
    oscillationCoverUpper width count j - oscillationCoverLower width count j =
      width + 3 * (width / count) := by
  simp [oscillationCoverUpper, oscillationCoverLower]
  ring

/-- Every corridor in the finite cover is a nonempty open interval. -/
theorem oscillationCoverLower_lt_upper
    (width : ℝ) (count : ℕ) (j : Fin count)
    (hwidth : 0 < width) (hcount : 0 < count) :
    oscillationCoverLower width count j <
      oscillationCoverUpper width count j := by
  have hmesh : 0 < width / (count : ℝ) :=
    div_pos hwidth (Nat.cast_pos.mpr hcount)
  have hdiff := oscillationCoverUpper_sub_lower width count j
  linarith

/-- Zero lies strictly inside each corridor in the finite cover. -/
theorem oscillationCoverLower_lt_zero
    (width : ℝ) (count : ℕ) (j : Fin count)
    (hwidth : 0 < width) (hcount : 0 < count) :
    oscillationCoverLower width count j < 0 := by
  have hmesh : 0 < width / (count : ℝ) :=
    div_pos hwidth (Nat.cast_pos.mpr hcount)
  have hjle : (j.val : ℝ) ≤ (count : ℝ) - 1 := by
    have hcast : (j.val : ℝ) + 1 ≤ (count : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt j.isLt
    linarith
  have hprod : (j.val : ℝ) * (width / (count : ℝ)) ≤
      width - width / (count : ℝ) := by
    have hjplus : (j.val : ℝ) + 1 ≤ (count : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt j.isLt
    have hcountmul : (count : ℝ) * (width / (count : ℝ)) = width := by
      field_simp [ne_of_gt (Nat.cast_pos.mpr hcount)]
    have htotal : (j.val : ℝ) * (width / (count : ℝ)) +
        width / (count : ℝ) ≤ width := by
      calc
        (j.val : ℝ) * (width / (count : ℝ)) +
            width / (count : ℝ) =
          ((j.val : ℝ) + 1) * (width / (count : ℝ)) := by ring
        _ ≤ (count : ℝ) * (width / (count : ℝ)) :=
          mul_le_mul_of_nonneg_right hjplus hmesh.le
        _ = width := hcountmul
    linarith
  rw [oscillationCoverLower]
  linarith

/-- Zero lies strictly inside each corridor in the finite cover. -/
theorem zero_lt_oscillationCoverUpper
    (width : ℝ) (count : ℕ) (j : Fin count)
    (hwidth : 0 < width) (hcount : 0 < count) :
    0 < oscillationCoverUpper width count j := by
  have hmesh : 0 < width / (count : ℝ) :=
    div_pos hwidth (Nat.cast_pos.mpr hcount)
  rw [oscillationCoverUpper]
  have hjnonneg : 0 ≤ (j.val : ℝ) := by positivity
  nlinarith

end ContinuousMap

end
