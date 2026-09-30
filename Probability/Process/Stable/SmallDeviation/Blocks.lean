module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks
public import Probability.Process.Stable.SmallDeviation.RationalTube

/-!
# Stable-process block laws

The path-level uniform partition, its measurability, and the generic tube
factorization live in
`Probability.Process.Path.Skorokhod.Corridor.UniformBlocks`.  This file only
adds the translated stable Lévy block law needed by the stable
small-deviation argument.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- The sample path of a stable process restricted to one uniform block and
translated to start at zero. -/
def rationalUniformBlockProcessFromLevy {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) : ↑Skorokhod.RationalunitInterval → Ω → ℝ :=
  fun q ω => X (rationalUniformBlockAbsoluteTime hblocks j q) ω -
    X (rationalUniformBlockAbsoluteTime hblocks j ⊥) ω

/-- Restricting a stable Lévy process to a translated block preserves its
stable independent-increment specification, with elapsed clock `q / blocks`.
-/
theorem IsStableLevyProcess.rationalUniformBlock_hasStableClockIncrements
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j : Fin blocks) :
    HasStableClockIncrements α μ (rationalUniformBlockClock hblocks j)
      (rationalUniformBlockProcessFromLevy X hblocks j) P := by
  let τ : ↑Skorokhod.RationalunitInterval → ℝ≥0 :=
    rationalUniformBlockAbsoluteTime hblocks j
  let Y : ↑Skorokhod.RationalunitInterval → Ω → ℝ :=
    rationalUniformBlockProcessFromLevy X hblocks j
  let clock : ↑Skorokhod.RationalunitInterval → ℝ :=
    rationalUniformBlockClock hblocks j
  have hτmono : Monotone τ := by
    intro s t hst
    apply NNReal.coe_le_coe.mp
    change ((rationalUniformBlockTime hblocks j s : ℚ) : ℝ) ≤
      ((rationalUniformBlockTime hblocks j t : ℚ) : ℝ)
    exact_mod_cast monotone_rationalUniformBlockTime hblocks j hst
  have hclockMono : Monotone clock := by
    intro s t hst
    change rationalUniformBlockClock hblocks j s ≤
      rationalUniformBlockClock hblocks j t
    rw [rationalUniformBlockClock_eq hblocks j s,
      rationalUniformBlockClock_eq hblocks j t]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hst)
      (by positivity)
  have hclockBot : clock ⊥ = 0 := by
    change rationalUniformBlockClock hblocks j ⊥ = 0
    rw [rationalUniformBlockClock_eq hblocks j]
    simp
  have hbase := h.increments
  have hcomp : HasIndepIncrements (fun q ω => X (τ q) ω) P :=
    hbase.indepIncrements.comp_time τ hτmono
  have hindep : HasIndepIncrements Y P := by
    intro n grid hgrid
    convert hcomp n grid hgrid using 1 <;>
      ext i ω <;> dsimp [Y, rationalUniformBlockProcessFromLevy] <;> ring
  refine ⟨hbase.strictlyStable, hclockMono, hclockBot, ?_, hindep, ?_⟩
  · filter_upwards [] with ω
    simp [rationalUniformBlockProcessFromLevy]
  · intro s t hst
    have hlaw := hbase.increment_hasLaw (τ s) (τ t) (hτmono hst)
    have hclockDiff : clock t - clock s = (τ t : ℝ) - (τ s : ℝ) := by
      simp [clock, rationalUniformBlockClock, τ,
        rationalUniformBlockAbsoluteTime]
    have hprocessDiff :
        (fun ω => Y t ω - Y s ω) = fun ω => X (τ t) ω - X (τ s) ω := by
      funext ω
      simp [Y, rationalUniformBlockProcessFromLevy,
        rationalUniformBlockAbsoluteTime, τ]
    rw [hprocessDiff, hclockDiff]
    exact hlaw

/-- Every translated block of the same length in a stable Lévy process has
the same rational path law. Mutual independence between blocks is separate. -/
theorem IsStableLevyProcess.rationalUniformBlockProcess_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j j' : Fin blocks) :
    IdentDistrib (fun ω q => rationalUniformBlockProcessFromLevy X hblocks j q ω)
      (fun ω q => rationalUniformBlockProcessFromLevy X hblocks j' q ω) P P := by
  have hj := h.rationalUniformBlock_hasStableClockIncrements blocks hblocks j
  have hj' := h.rationalUniformBlock_hasStableClockIncrements blocks hblocks j'
  have hclock : rationalUniformBlockClock hblocks j =
      rationalUniformBlockClock hblocks j' := by
    funext q
    rw [rationalUniformBlockClock_eq, rationalUniformBlockClock_eq]
  have hj'Clock : HasStableClockIncrements α μ
      (rationalUniformBlockClock hblocks j)
      (rationalUniformBlockProcessFromLevy X hblocks j') P := by
    simpa [hclock] using hj'
  exact hj.process_identDistrib hj'Clock

/-- The rational-coordinate block process is the process-level restriction
of the stable Lévy process. -/
theorem IsStableLevyProcess.rationalTubeBlockProcess_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j j' : Fin blocks) :
    IdentDistrib
      (rationalUniformBlockProcess
        (fun q ω => X (rationalUnitTime q) ω) hblocks j)
      (rationalUniformBlockProcess
        (fun q ω => X (rationalUnitTime q) ω) hblocks j') P P := by
  convert h.rationalUniformBlockProcess_identDistrib blocks hblocks j j' using 1 <;>
    funext ω q <;>
    simp [rationalUniformBlockProcess, rationalTubeBlockIncrement,
      rationalUniformBlockProcessFromLevy, rationalUniformBlockAbsoluteTime]

/-- The stable-process instance of the upper block inequality. Stable
independent increments already identify every translated block path law, so
the only remaining hypothesis is mutual independence of the finitely many
block path sigma-fields. -/
theorem IsStableLevyProcess.measure_rationalTube_le_pow_of_iIndep_uniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (width : ℝ)
    (hindep : iIndepFun
      (rationalUniformBlockProcess
        (fun q ω => X (rationalUnitTime q) ω) hblocks) P) :
    P ((fun ω q => X (rationalUnitTime q) ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      (P ((rationalUniformBlockProcess
        (fun q ω => X (rationalUnitTime q) ω) hblocks
          ⟨0, hblocks⟩) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) ^ blocks := by
  apply ProbabilityTheory.measure_rationalTube_le_pow_of_iIndep_uniformBlocks P
    (fun q ω => X (rationalUnitTime q) ω) hblocks width hindep
  intro j
  exact h.rationalTubeBlockProcess_identDistrib blocks hblocks j ⟨0, hblocks⟩

end ProbabilityTheory

end
