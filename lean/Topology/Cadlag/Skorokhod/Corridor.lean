import Topology.Cadlag.Skorokhod.ContinuousMap
import Topology.ContinuousMap.Corridor

/-!
# Uniformly interior corridors in Skorokhod path space

For a càdlàg path, pointwise membership in an open interval need not have a
positive uniform margin: a left limit may lie on the boundary without being
attained.  The open event appropriate for the Skorokhod `J₁` topology therefore
records an explicit positive margin from both boundaries.
-/

open Set
open scoped ENNReal

namespace Skorokhod

/-- Càdlàg paths whose values remain a positive uniform distance inside an
open real interval. -/
def rangeInOpenInterval (lower upper : ℝ) : Set (CadlagPath UnitInterval ℝ) :=
  {path | ∃ margin > 0, ∀ t,
    lower + margin ≤ path t ∧ path t ≤ upper - margin}

theorem mem_rangeInOpenInterval_iff
    {lower upper : ℝ} {path : CadlagPath UnitInterval ℝ} :
    path ∈ rangeInOpenInterval lower upper ↔
      ∃ margin > 0, ∀ t,
        lower + margin ≤ path t ∧ path t ≤ upper - margin :=
  Iff.rfl

/-- The uniformly interior corridor is open for the Skorokhod `J₁` topology.
Time changes do not affect the range of a path, while the spatial part of the
`J₁` cost controls all values uniformly. -/
theorem isOpen_rangeInOpenInterval (lower upper : ℝ) :
    IsOpen (rangeInOpenInterval lower upper) := by
  rw [isOpen_iff_forall_mem_open]
  intro path hpath
  obtain ⟨margin, hmargin, hpath⟩ := hpath
  refine ⟨Metric.ball path (margin / 2), ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (half_pos hmargin)⟩
  intro other hother
  have hj1 : j1EDist path other < ENNReal.ofReal (margin / 2) := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff (half_pos hmargin)]
    simpa [dist_comm] using hother
  obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt hj1
  have huniform : uniformEDist (change.act path) other <
      ENNReal.ofReal (margin / 2) :=
    (le_max_right _ _).trans_lt hchange
  refine ⟨margin / 2, half_pos hmargin, fun t => ?_⟩
  have ht := (edist_apply_le_uniformEDist (change.act path) other t).trans_lt
    huniform
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (half_pos hmargin)] at ht
  have hp := hpath (change t)
  rw [Real.dist_eq, abs_lt] at ht
  change -(margin / 2) < path (change t) - other t ∧
    path (change t) - other t < margin / 2 at ht
  constructor <;> linarith

theorem measurableSet_rangeInOpenInterval (lower upper : ℝ) :
    MeasurableSet (rangeInOpenInterval lower upper) :=
  (isOpen_rangeInOpenInterval lower upper).measurableSet

/-- For continuous paths, ordinary pointwise strict corridor membership
already supplies a uniform positive margin by compactness.  Hence the
continuous and Skorokhod corridor interfaces agree under the canonical
inclusion. -/
theorem ofContinuousMap_mem_rangeInOpenInterval_iff
    {lower upper : ℝ} (hlowerUpper : lower < upper)
    (path : C(UnitInterval, ℝ)) :
    ofContinuousMap path ∈ rangeInOpenInterval lower upper ↔
      path ∈ ContinuousMap.rangeInOpenInterval lower upper := by
  constructor
  · rintro ⟨margin, hmargin, hpath⟩
    apply ContinuousMap.mem_rangeInOpenInterval_iff.mpr
    intro t
    have ht := hpath t
    change lower + margin ≤ path t ∧ path t ≤ upper - margin at ht
    constructor <;> linarith
  · intro hpath
    have hball : path ∈ Metric.ball
        (ContinuousMap.const UnitInterval ((lower + upper) / 2))
        ((upper - lower) / 2) := by
      rwa [← ContinuousMap.rangeInOpenInterval_eq_ball hlowerUpper]
    let radius := (upper - lower) / 2
    let center := ContinuousMap.const UnitInterval ((lower + upper) / 2)
    let margin := radius - dist path center
    have hmargin : 0 < margin := by
      exact sub_pos.mpr hball
    refine ⟨margin, hmargin, fun t => ?_⟩
    have ht := ContinuousMap.dist_apply_le_dist (f := path) (g := center) t
    change dist (path t) ((lower + upper) / 2) ≤ dist path center at ht
    rw [Real.dist_eq, abs_le] at ht
    dsimp only [margin, radius]
    change lower + ((upper - lower) / 2 - dist path center) ≤ path t ∧
      path t ≤ upper - ((upper - lower) / 2 - dist path center)
    constructor <;> linarith

end Skorokhod
