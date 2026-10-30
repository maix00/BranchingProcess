/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Topology.Order.UnitInterval.Time

/-!
# Complete corridor events on a time segment

## Public declarations

- segmentIncrement defines the centered segment path
  \(t\mapsto X_{s+\ell t}-X_s\).
- fullSegmentCorridorEvent records a positive uniform margin inside
  \((a,b)\):
  \[
    \exists\eta>0,\ \forall t\in[0,1],\quad
      a+\eta\le X_{s+\ell t}-X_s\le b-\eta.
  \]
- fullSegmentCorridorEvent_subset_endpoint_Icc places the terminal
  increment of this event in \([a,b]\).
- segmentCorridorEndpointEvent adds an arbitrary endpoint condition;
  fullSegmentCorridorReturnEvent uses the open interval \((c,d)\), while
  fullSegmentCorridorIocReturnEvent uses \((c,d]\).
- linearTube_subset_fullSegmentCorridorReturnEvent: if
  \(a+2\eta\le0\le b-2\eta\), \(a+2\eta\le v\le b-2\eta\), and
  \(c+\eta<v<d-\eta\), then
  \[
    \left\{\omega:\forall t\in[0,1],\
      |\Delta X_{s,\ell}(t,\omega)-vt|<\eta\right\}
    \subseteq
    \left\{\omega:\exists\rho>0,\ \forall t\in[0,1],\
      a+\rho\le\Delta X_{s,\ell}(t,\omega)\le b-\rho,\
      \Delta X_{s,\ell}(1,\omega)\in(c,d)\right\},
  \]
  where \(\Delta X_{s,\ell}(t,\omega)=X_{s+\ell t}(\omega)-X_s(\omega)\).
- segmentCorridorEndpointEvent_mono, fullSegmentCorridorReturnEvent_mono_bounds,
  and fullSegmentCorridorIocReturnEvent_mono_bounds state monotonicity under
  enlargement of their spatial and endpoint intervals.
- `fullEntrance_inter_continuation_subset_fullCorridor`: a first segment with
  endpoint increment in $(c,d)$ followed by a corridor translated by $(c,d)$
  lies in the unshifted corridor on the joined interval.
- `fullReturn_inter_return_subset_fullReturn`: two adjacent corridors with
  endpoint windows $(c_1,d_1)$ and $(c_2,d_2)$ concatenate into a corridor
  whose endpoint window is $(c_1+c_2,d_1+d_2)$.
- `fullSegmentCorridorEvent_mono_length`: if $0<\ell$ and $0\le s\le\ell$,
  the full corridor event on $[0,\ell]$ is contained in the one on $[0,s]$.

This module defines pathwise segment increments and corridor events without
using a path-space topology. Endpoint conventions are represented by an
arbitrary measurable-set parameter; the `Ioo` and `Ioc` events used by
applications are special cases.
-/

@[expose] public section

namespace ProbabilityTheory

open scoped NNReal

/-- A segment of a process, translated to start at zero. -/
def segmentIncrement {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (ω : Ω) (t : unitInterval) : ℝ :=
  X (start + length * unitInterval.toNNReal t) ω - X start ω

/-- The complete segment remains a positive uniform distance inside a
spatial corridor. -/
def fullSegmentCorridorEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) : Set Ω :=
  {ω | ∃ margin > 0, ∀ t : unitInterval,
    lower + margin ≤ segmentIncrement X start length ω t ∧
      segmentIncrement X start length ω t ≤ upper - margin}

/-- A complete-segment corridor constrains its terminal increment to the
corresponding closed interval. -/
theorem fullSegmentCorridorEvent_subset_endpoint_Icc
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) :
    fullSegmentCorridorEvent X start length lower upper ⊆
      {ω | segmentIncrement X start length ω ⊤ ∈ Set.Icc lower upper} := by
  rintro ω ⟨margin, hmargin, hpath⟩
  have hend := hpath ⊤
  exact ⟨by linarith, by linarith⟩

/-- A corridor event with an arbitrary endpoint constraint. -/
def segmentCorridorEndpointEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0) (lower upper : ℝ) (J : Set ℝ) : Set Ω :=
  fullSegmentCorridorEvent X start length lower upper ∩
    {ω | segmentIncrement X start length ω ⊤ ∈ J}

/-- The endpoint-constrained complete segment corridor with an open window. -/
def fullSegmentCorridorReturnEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) : Set Ω :=
  segmentCorridorEndpointEvent X start length lower upper
    (Set.Ioo coreLower coreUpper)

/-- The endpoint-constrained complete segment corridor with a
left-open, right-closed window. -/
def fullSegmentCorridorIocReturnEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) : Set Ω :=
  segmentCorridorEndpointEvent X start length lower upper
    (Set.Ioc coreLower coreUpper)

/-- A pathwise tube around a linear segment lies in any corridor that
contains the line with a twice-as-large margin and contains its endpoint with
a margin. -/
theorem linearTube_subset_fullSegmentCorridorReturnEvent
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start length : ℝ≥0)
    (lower upper coreLower coreUpper slope η : ℝ)
    (hη : 0 < η)
    (hstart : lower + 2 * η ≤ 0 ∧ 0 ≤ upper - 2 * η)
    (hend : lower + 2 * η ≤ slope ∧ slope ≤ upper - 2 * η)
    (hcore : coreLower + η < slope ∧ slope < coreUpper - η) :
    {ω | ∀ t : unitInterval,
      |segmentIncrement X start length ω t - slope * (t : ℝ)| < η} ⊆
      fullSegmentCorridorReturnEvent X start length
        lower upper coreLower coreUpper := by
  intro ω hω
  have hline (t : unitInterval) :
      lower + 2 * η ≤ slope * (t : ℝ) ∧
        slope * (t : ℝ) ≤ upper - 2 * η := by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hlo₁ := mul_le_mul_of_nonneg_right hend.1 ht0
    have hlo₂ := mul_le_mul_of_nonneg_right hstart.1
      (sub_nonneg.mpr ht1)
    have hhi₁ := mul_le_mul_of_nonneg_right hend.2 ht0
    have hhi₂ := mul_le_mul_of_nonneg_right hstart.2
      (sub_nonneg.mpr ht1)
    constructor <;> nlinarith
  have hcorridor : ω ∈ fullSegmentCorridorEvent X start length lower upper := by
    refine ⟨η, hη, fun t => ?_⟩
    have hdeviation := abs_lt.mp (hω t)
    have hline' := hline t
    constructor <;> linarith
  have htop : ((⊤ : unitInterval) : ℝ) = 1 := rfl
  have hendpointDeviation :
      |segmentIncrement X start length ω ⊤ - slope| < η := by
    simpa only [htop, mul_one] using hω ⊤
  have hendpoint : segmentIncrement X start length ω ⊤ ∈
      Set.Ioo coreLower coreUpper := by
    have hdeviation := abs_lt.mp hendpointDeviation
    exact ⟨by linarith [hcore.1], by linarith [hcore.2]⟩
  exact ⟨hcorridor, hendpoint⟩

/-- Enlarging a spatial corridor and its arbitrary endpoint set preserves
the corresponding event. -/
theorem segmentCorridorEndpointEvent_mono
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    {lower₁ upper₁ lower₂ upper₂ : ℝ} {J₁ J₂ : Set ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂)
    (hJ : J₁ ⊆ J₂) :
    segmentCorridorEndpointEvent X start length lower₁ upper₁ J₁ ⊆
      segmentCorridorEndpointEvent X start length lower₂ upper₂ J₂ := by
  rintro ω ⟨⟨margin, hmargin, hpath⟩, hend⟩
  refine ⟨⟨margin, hmargin, ?_⟩, hJ hend⟩
  intro t
  obtain ⟨hlo, hhi⟩ := hpath t
  exact ⟨by linarith, by linarith⟩

/-- Enlarging the spatial corridor and endpoint window preserves an open
complete-segment entrance event. -/
theorem fullSegmentCorridorReturnEvent_mono_bounds
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    {lower₁ upper₁ coreLower₁ coreUpper₁
      lower₂ upper₂ coreLower₂ coreUpper₂ : ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂)
    (hcoreLower : coreLower₂ ≤ coreLower₁)
    (hcoreUpper : coreUpper₁ ≤ coreUpper₂) :
    fullSegmentCorridorReturnEvent X start length
        lower₁ upper₁ coreLower₁ coreUpper₁ ⊆
      fullSegmentCorridorReturnEvent X start length
        lower₂ upper₂ coreLower₂ coreUpper₂ := by
  apply segmentCorridorEndpointEvent_mono X start length hlower hupper
  intro x hx
  exact ⟨lt_of_le_of_lt hcoreLower hx.1,
    lt_of_lt_of_le hx.2 hcoreUpper⟩

/-- Enlarging a corridor and a left-open, right-closed endpoint window
preserves the corresponding complete-segment event. -/
theorem fullSegmentCorridorIocReturnEvent_mono_bounds
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (start length : ℝ≥0)
    {lower₁ upper₁ coreLower₁ coreUpper₁
      lower₂ upper₂ coreLower₂ coreUpper₂ : ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂)
    (hcoreLower : coreLower₂ ≤ coreLower₁)
    (hcoreUpper : coreUpper₁ ≤ coreUpper₂) :
    fullSegmentCorridorIocReturnEvent X start length
        lower₁ upper₁ coreLower₁ coreUpper₁ ⊆
      fullSegmentCorridorIocReturnEvent X start length
        lower₂ upper₂ coreLower₂ coreUpper₂ := by
  apply segmentCorridorEndpointEvent_mono X start length hlower hupper
  intro x hx
  exact ⟨lt_of_le_of_lt hcoreLower hx.1,
    le_trans hx.2 hcoreUpper⟩

/-- A constrained first segment and a translated continuation lie in the
same complete-path corridor. This is the pathwise inclusion behind the
fixed-cut probability lower bound. -/
theorem fullEntrance_inter_continuation_subset_fullCorridor
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (cut remaining : ℝ≥0) (hcut : 0 < cut) (hremaining : 0 < remaining)
    (lower upper endpointLower endpointUpper : ℝ) :
    fullSegmentCorridorReturnEvent X 0 cut
        lower upper endpointLower endpointUpper ∩
      fullSegmentCorridorEvent X cut remaining
        (lower - endpointLower) (upper - endpointUpper) ⊆
      fullSegmentCorridorEvent X 0 (cut + remaining) lower upper := by
  intro ω hω
  rcases hω with ⟨⟨⟨margin₁, hmargin₁, hfirst⟩, hend⟩,
    margin₂, hmargin₂, hsecond⟩
  have htop : unitInterval.toNNReal ⊤ = 1 := unitInterval.toNNReal_one
  have hendpoint : endpointLower < X cut ω - X 0 ω ∧
      X cut ω - X 0 ω < endpointUpper := by
    simpa [segmentIncrement, htop] using hend
  let margin := min margin₁ (min margin₂
    (min (X cut ω - X 0 ω - endpointLower)
      (endpointUpper - (X cut ω - X 0 ω))))
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact lt_min hmargin₁ (lt_min hmargin₂
      (lt_min (sub_pos.mpr hendpoint.1) (sub_pos.mpr hendpoint.2)))
  refine ⟨margin, hmargin, ?_⟩
  intro t
  let absoluteTime := (cut + remaining) * unitInterval.toNNReal t
  by_cases hbefore : absoluteTime ≤ cut
  · obtain ⟨u, hu⟩ := unitInterval.exists_mul_eq cut absoluteTime hcut hbefore
    have hu' := hfirst u
    have hm : margin ≤ margin₁ := min_le_left _ _
    dsimp [segmentIncrement] at hu' ⊢
    simp only [zero_add] at hu' ⊢
    change cut * unitInterval.toNNReal u = absoluteTime at hu
    rw [hu] at hu'
    constructor <;> linarith
  · have hafter : cut ≤ absoluteTime := le_of_not_ge hbefore
    have htimeLe : unitInterval.toNNReal t ≤ 1 := by
      exact_mod_cast t.property.2
    have htotal : absoluteTime ≤ cut + remaining := by
      simpa [absoluteTime] using mul_le_mul_of_nonneg_left
        htimeLe (cut + remaining).property
    obtain ⟨u, hu⟩ := unitInterval.exists_add_mul_eq
      cut remaining absoluteTime hremaining hafter htotal
    have hu' := hsecond u
    have hmLow : margin ≤ X cut ω - X 0 ω - endpointLower := by
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have hmUp : margin ≤ endpointUpper - (X cut ω - X 0 ω) := by
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    dsimp [segmentIncrement] at hu' ⊢
    simp only [zero_add] at hu' ⊢
    change cut + remaining * unitInterval.toNNReal u = absoluteTime at hu
    rw [hu] at hu'
    constructor <;> linarith

/-- Two adjacent endpoint-constrained segments concatenate to an
endpoint-constrained complete corridor. The second corridor is translated by
the entire first endpoint window. -/
theorem fullReturn_inter_return_subset_fullReturn
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (cut remaining : ℝ≥0) (hcut : 0 < cut) (hremaining : 0 < remaining)
    (lower upper firstLower firstUpper secondLower secondUpper : ℝ) :
    fullSegmentCorridorReturnEvent X 0 cut
        lower upper firstLower firstUpper ∩
      fullSegmentCorridorReturnEvent X cut remaining
        (lower - firstLower) (upper - firstUpper)
        secondLower secondUpper ⊆
      fullSegmentCorridorReturnEvent X 0 (cut + remaining)
        lower upper (firstLower + secondLower) (firstUpper + secondUpper) := by
  intro ω hω
  have hpath := fullEntrance_inter_continuation_subset_fullCorridor X
    cut remaining hcut hremaining lower upper firstLower firstUpper
    ⟨hω.1, hω.2.1⟩
  refine ⟨hpath, ?_⟩
  have hfirst := hω.1.2
  have hsecond := hω.2.2
  have htop : unitInterval.toNNReal ⊤ = 1 := unitInterval.toNNReal_one
  dsimp [segmentIncrement] at hfirst hsecond ⊢
  simp only [htop, mul_one, zero_add, Set.mem_Ioo] at hfirst hsecond ⊢
  constructor <;> linarith

/-- Restricting a complete corridor path to a shorter initial horizon
preserves its positive uniform spatial margin. -/
theorem fullSegmentCorridorEvent_mono_length
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (start short long : ℝ≥0) (hlong : 0 < long)
    (hshort : short ≤ long) (lower upper : ℝ) :
    fullSegmentCorridorEvent X start long lower upper ⊆
      fullSegmentCorridorEvent X start short lower upper := by
  intro ω hω
  rcases hω with ⟨margin, hmargin, hpath⟩
  refine ⟨margin, hmargin, ?_⟩
  intro t
  have htimeLe : unitInterval.toNNReal t ≤ 1 := by
    exact_mod_cast t.property.2
  have htime : short * unitInterval.toNNReal t ≤ long := by
    calc
      short * unitInterval.toNNReal t ≤ short * 1 :=
        mul_le_mul_of_nonneg_left htimeLe short.property
      _ = short := mul_one _
      _ ≤ long := hshort
  obtain ⟨u, hu⟩ := unitInterval.exists_mul_eq long
    (short * unitInterval.toNNReal t) hlong htime
  have hb := hpath u
  dsimp [segmentIncrement] at hb ⊢
  rw [hu] at hb
  exact hb

end ProbabilityTheory

end
