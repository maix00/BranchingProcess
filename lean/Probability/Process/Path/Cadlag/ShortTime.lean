module

public import MeasureTheory.Measure.SetLimits
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Short-time corridors for càdlàg processes

Almost-sure right continuity at the starting time makes every fixed centered
spatial corridor overwhelmingly likely as its time horizon shrinks to zero.
Coordinate random variables only need to be almost-everywhere measurable.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

def rationalInitialCorridorEvent {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (horizon : ℝ≥0) (lower upper : ℝ) : Set Ω :=
  (fun ω q => X (horizon * rationalUnitTime q) ω - X 0 ω) ⁻¹'
    rationalCoordinateCorridor lower upper

theorem rationalInitialCorridorEvent_inter_positive_subset_return
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (horizon : ℝ≥0)
    (δ coreUpper : ℝ) (hcore : δ ≤ coreUpper) :
    rationalInitialCorridorEvent X horizon (-δ) δ ∩
        {ω | 0 < X horizon ω - X 0 ω} ⊆
      (fun ω q => X (horizon * rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ) δ 0 coreUpper := by
  intro ω hω
  refine ⟨hω.1, ?_, ?_⟩
  · simpa [rationalUnitTime_top] using hω.2
  · have htop := Set.mem_iInter.mp hω.1 ⊤
    change -δ < X (horizon * rationalUnitTime ⊤) ω - X 0 ω ∧
      X (horizon * rationalUnitTime ⊤) ω - X 0 ω < δ at htop
    simpa [rationalUnitTime_top] using lt_of_lt_of_le htop.2 hcore

theorem rationalInitialCorridorEvent_inter_negative_subset_return
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (horizon : ℝ≥0)
    (δ coreLower : ℝ) (hcore : coreLower ≤ -δ) :
    rationalInitialCorridorEvent X horizon (-δ) δ ∩
        {ω | X horizon ω - X 0 ω < 0} ⊆
      (fun ω q => X (horizon * rationalUnitTime q) ω - X 0 ω) ⁻¹'
        rationalCoordinateCorridorReturn (-δ) δ coreLower 0 := by
  intro ω hω
  refine ⟨hω.1, ?_, ?_⟩
  · have htop := Set.mem_iInter.mp hω.1 ⊤
    change -δ < X (horizon * rationalUnitTime ⊤) ω - X 0 ω ∧
      X (horizon * rationalUnitTime ⊤) ω - X 0 ω < δ at htop
    simpa [rationalUnitTime_top] using lt_of_le_of_lt hcore htop.1
  · simpa [rationalUnitTime_top] using hω.2

theorem nullMeasurableSet_rationalInitialCorridorEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (horizon : ℝ≥0) (lower upper : ℝ) :
    NullMeasurableSet (rationalInitialCorridorEvent X horizon lower upper) P := by
  have hmap : AEMeasurable
      (fun ω q => X (horizon * rationalUnitTime q) ω - X 0 ω) P := by
    rw [aemeasurable_pi_iff]
    intro q
    exact (hX _).sub (hX 0)
  exact hmap.nullMeasurableSet_preimage
    (measurableSet_rationalCoordinateCorridor lower upper)

/-- Centered rational-time increment corridors of fixed positive width have probability tending to one as the
time horizon tends to zero. -/
theorem tendsto_measure_rationalInitialCorridorEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ t, AEMeasurable (X t) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
    {horizon : ℕ → ℝ≥0} (hhorizon : Tendsto horizon atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => P (rationalInitialCorridorEvent X (horizon n) (-δ) δ))
      atTop (𝓝 1) := by
  let A : ℕ → Set Ω := fun n => rationalInitialCorridorEvent X (horizon n) (-δ) δ
  have hA : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    exact nullMeasurableSet_rationalInitialCorridorEvent P X hX _ _ _
  have hnear : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n := by
    filter_upwards [hcadlag] with ω hω
    have hlocal := hω.eventually_initial_interval_subset_Ioo hhorizon
      (show X 0 ω - δ < X 0 ω by linarith)
      (show X 0 ω < X 0 ω + δ by linarith)
    filter_upwards [hlocal] with n hn
    change (fun q => X (horizon n * rationalUnitTime q) ω - X 0 ω) ∈
      rationalCoordinateCorridor (-δ) δ
    simp only [rationalCoordinateCorridor, Set.mem_iInter,
      Set.mem_ofPred_eq, Set.mem_Ioo]
    intro q
    have htime : horizon n * rationalUnitTime q ≤ horizon n := by
      calc
        horizon n * rationalUnitTime q ≤ horizon n * 1 :=
          mul_le_mul_of_nonneg_left (rationalUnitTime_le_one q) (horizon n).property
        _ = horizon n := mul_one _
    have hq := hn _ htime
    constructor <;> linarith [hq.1, hq.2]
  simpa [A, measure_univ] using
    tendsto_measure_univ_of_ae_eventually P A hA hnear

end ProbabilityTheory
