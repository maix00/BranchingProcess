module

public import Topology.Cadlag.Skorokhod.Oscillation
public import Topology.Cadlag.Skorokhod.RationalGrid
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Order.IsLUB

/-!
# Oscillation bounds on dense sets

For càdlàg paths, a range bound can be checked on a dense set of times that
contains the terminal endpoint.  The rational-coordinate tube is then a
countable measurable description of the same open Skorokhod tube.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Skorokhod

/-- For a càdlàg real path, an oscillation bound on a dense time set that
contains the terminal endpoint holds at every time. -/
theorem oscillationBounded_on_dense
    {T : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    [DenselyOrdered T] [FirstCountableTopology T] [OrderTop T]
    {D : Set T} (hD : Dense D) (htop : ⊤ ∈ D)
    (path : T → ℝ) (hpath : IsCadlag path) {bound : ℝ}
    (hDpath : ∀ s ∈ D, ∀ t ∈ D, |path s - path t| ≤ bound) :
    ∀ s t, |path s - path t| ≤ bound := by
  have happrox (x : T) :
      ∃ u : ℕ → T, (∀ n, u n ∈ D) ∧
        Tendsto (fun n => path (u n)) atTop (𝓝 (path x)) := by
    by_cases hx : x = ⊤
    · subst x
      exact ⟨fun _ => ⊤, fun _ => htop, tendsto_const_nhds⟩
    · have hxtop : x < ⊤ := lt_of_le_of_ne le_top hx
      obtain ⟨u, _, humem, hulim⟩ :=
        hD.exists_seq_strictAnti_tendsto_of_lt hxtop
      have hwithin : Tendsto u atTop (𝓝[Set.Ioi x] x) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hulim, Filter.Eventually.of_forall fun n => (humem n).1.1⟩
      refine ⟨u, fun n => (humem n).2, ?_⟩
      exact (hpath.isRightContinuous x).tendsto.comp hwithin
  intro s t
  obtain ⟨us, husD, hus⟩ := happrox s
  obtain ⟨ut, hutD, hut⟩ := happrox t
  have hdiff : Tendsto (fun n => path (us n) - path (ut n)) atTop
      (𝓝 (path s - path t)) := hus.sub hut
  have hosc : Tendsto (fun n => |path (us n) - path (ut n)|) atTop
      (𝓝 |path s - path t|) :=
    (continuous_abs.tendsto _).comp hdiff
  have hbounded : ∀ᶠ n in atTop,
      |path (us n) - path (ut n)| ∈ Set.Iic bound :=
    Filter.Eventually.of_forall fun n => hDpath (us n) (husD n) (ut n) (hutD n)
  exact isClosed_Iic.mem_of_tendsto hosc hbounded

/-- The countable-coordinate description of an open oscillation tube on the
rational points of the unit interval. Rational margins make the existential
slack countable without changing the event.
-/
def rationalOscillationInOpenTube (width : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {path | ∃ margin : ℚ, 0 < (margin : ℝ) ∧
    ∀ s t : RationalunitInterval,
      |path (rationalunitIntervalCoe s) -
        path (rationalunitIntervalCoe t)| ≤ width - margin}

/-- The rational-coordinate oscillation tube is the already-established open
Skorokhod tube.
-/
theorem rationalOscillationInOpenTube_eq (width : ℝ) :
    rationalOscillationInOpenTube width = oscillationInOpenTube width := by
  have hD : Dense (Set.range rationalunitIntervalCoe) :=
    denseRange_rationalunitIntervalCoe
  have htop : (⊤ : unitInterval) ∈ Set.range rationalunitIntervalCoe := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    apply Subtype.ext
    simp [rationalunitIntervalCoe]
  ext path
  constructor
  · rintro ⟨margin, hmargin, hbound⟩
    refine ⟨(margin : ℝ), hmargin, ?_⟩
    apply oscillationBounded_on_dense hD htop path path.isCadlag_toFun
    intro s hs t ht
    obtain ⟨s', rfl⟩ := hs
    obtain ⟨t', rfl⟩ := ht
    exact hbound s' t'
  · rintro ⟨margin, hmargin, hbound⟩
    obtain ⟨q, hq0, hqmargin⟩ := exists_rat_btwn hmargin
    refine ⟨q, hq0, ?_⟩
    intro s t
    calc
      |path (rationalunitIntervalCoe s) -
          path (rationalunitIntervalCoe t)| ≤ width - margin := hbound _ _
      _ ≤ width - (q : ℝ) := by linarith

/-- The rational-coordinate description inherits measurability from the
Skorokhod topology through the preceding set equality.
-/
theorem measurableSet_rationalOscillationInOpenTube (width : ℝ) :
    MeasurableSet (rationalOscillationInOpenTube width) := by
  rw [rationalOscillationInOpenTube_eq]
  exact measurableSet_oscillationInOpenTube width

/-- Oscillation tube in the countable product of rational-time coordinates.
-/
def rationalCoordinateOscillationTube (width : ℝ) :
    Set (RationalunitInterval → ℝ) :=
  {x | ∃ margin : ℚ, 0 < (margin : ℝ) ∧
    ∀ s t : RationalunitInterval, |x s - x t| ≤ width - margin}

/-- The rational-time tube is measurable in the countable product sigma
algebra, so its probability is determined by finite-dimensional laws.
-/
theorem measurableSet_rationalCoordinateOscillationTube (width : ℝ) :
    MeasurableSet (rationalCoordinateOscillationTube width) := by
  classical
  have hbound (margin : ℚ) : MeasurableSet
      {x : RationalunitInterval → ℝ |
        ∀ s t : RationalunitInterval, |x s - x t| ≤ width - margin} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun s => by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun t => by
        have hst : Measurable
            (fun x : RationalunitInterval → ℝ => |x s - x t|) := by
          fun_prop
        have hconst : Measurable
            (fun _ : RationalunitInterval → ℝ => width - (margin : ℝ)) :=
          measurable_const
        exact measurableSet_le hst hconst
  rw [show rationalCoordinateOscillationTube width =
      ⋃ margin : ℚ,
        if 0 < (margin : ℝ) then
          {x : RationalunitInterval → ℝ |
            ∀ s t : RationalunitInterval, |x s - x t| ≤ width - margin}
        else ∅ by
    ext x
    simp [rationalCoordinateOscillationTube]]
  exact MeasurableSet.iUnion fun margin => by
    split_ifs
    · exact hbound margin
    · exact MeasurableSet.empty

end Skorokhod

end
