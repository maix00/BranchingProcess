module

public import Probability.Process.Stable.SmallDeviation.RationalTube

/-!
# Uniform block restrictions for stable-process tubes

Uniformly partition a rational-time path into blocks. A tube on the whole
unit interval forces the increment path on each block to remain in the same
range tube; the probability factorization from independent increments is a
separate theorem.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- The `q` coordinate inside the `j`th block of a uniform partition of the
unit interval, represented as a rational point of the unit interval. -/
def rationalUniformBlockTime {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (q : ↑Skorokhod.RationalunitInterval) :
    ↑Skorokhod.RationalunitInterval :=
  ⟨((j.val : ℚ) + (q : ℚ)) / (blocks : ℚ), by
    have hden : 0 < (blocks : ℚ) := by exact_mod_cast hblocks
    have hnum0 : 0 ≤ (j.val : ℚ) + (q : ℚ) :=
      add_nonneg (by positivity) q.property.1
    have hj : (j.val : ℚ) + 1 ≤ (blocks : ℚ) := by
      exact_mod_cast (Nat.succ_le_of_lt j.isLt)
    have hnum : (j.val : ℚ) + (q : ℚ) ≤ (blocks : ℚ) := by
      linarith [q.property.2]
    constructor
    · exact div_nonneg hnum0 hden.le
    · rw [div_le_iff₀ hden]
      simpa using hnum⟩

/-- The time embedding for one rational block is monotone. -/
theorem monotone_rationalUniformBlockTime {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) :
    Monotone (rationalUniformBlockTime hblocks j) := by
  intro s t hst
  apply Subtype.mk_le_mk.mpr
  have hden : 0 < (blocks : ℚ) := by exact_mod_cast hblocks
  change (s : ℚ) ≤ t at hst
  change ((j.val : ℚ) + (s : ℚ)) / (blocks : ℚ) ≤
    ((j.val : ℚ) + (t : ℚ)) / (blocks : ℚ)
  exact (div_le_div_iff_of_pos_right hden).2 (by linarith)

/-- The uniform block time map preserves the initial rational time. -/
@[simp]
theorem rationalUniformBlockTime_bot {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) :
    rationalUniformBlockTime hblocks j ⊥ = ⟨(j.val : ℚ) / (blocks : ℚ), by
      constructor
      · positivity
      · rw [div_le_iff₀ (by exact_mod_cast hblocks : 0 < (blocks : ℚ))]
        norm_num [one_mul]
      ⟩ := by
  apply Subtype.ext
  simp [rationalUniformBlockTime]

/-- The corresponding real time in the stable process. -/
def rationalUniformBlockAbsoluteTime {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (q : ↑Skorokhod.RationalunitInterval) : ℝ≥0 :=
  rationalUnitTime (rationalUniformBlockTime hblocks j q)

/-- Elapsed time within a uniform block. It is independent of the block
index, as required for equality of the block path laws. -/
def rationalUniformBlockClock {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (q : ↑Skorokhod.RationalunitInterval) : ℝ :=
  (rationalUniformBlockAbsoluteTime hblocks j q : ℝ) -
    (rationalUniformBlockAbsoluteTime hblocks j ⊥ : ℝ)

/-- The increment path across one uniform block, read on rational unit time.
The subtraction makes the event depend only on the block increments. -/
def rationalTubeBlockIncrement {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (x : ↑Skorokhod.RationalunitInterval → ℝ) :
    ↑Skorokhod.RationalunitInterval → ℝ :=
  fun q => x (rationalUniformBlockTime hblocks j q) -
    x (rationalUniformBlockTime hblocks j ⊥)

/-- The event that the increment path on one uniform block has oscillation
strictly less than `width`. -/
def rationalTubeBlockEvent (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) : Set (↑Skorokhod.RationalunitInterval → ℝ) :=
  (rationalTubeBlockIncrement hblocks j) ⁻¹'
    Skorokhod.rationalCoordinateOscillationTube width

/-- The family of uniform block increment paths cut from a rational-time
process. -/
def rationalUniformBlockProcess {Ω : Type*} (X : ↑Skorokhod.RationalunitInterval →
    Ω → ℝ) {blocks : ℕ} (hblocks : 0 < blocks) :
    Fin blocks → Ω → ↑Skorokhod.RationalunitInterval → ℝ :=
  fun j ω => rationalTubeBlockIncrement hblocks j (fun q => X q ω)

/-- The elapsed-time clock of every uniform block is `q / blocks`. -/
theorem rationalUniformBlockClock_eq {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (q : ↑Skorokhod.RationalunitInterval) :
    rationalUniformBlockClock hblocks j q =
      (q : ℝ) / (blocks : ℝ) := by
  simp only [rationalUniformBlockClock, rationalUniformBlockAbsoluteTime,
    rationalUnitTime_coe, rationalUniformBlockTime_bot]
  change ((((j.val : ℚ) + (q : ℚ)) / (blocks : ℚ) : ℚ) : ℝ) -
      (((j.val : ℚ) / (blocks : ℚ) : ℚ) : ℝ) =
    (q : ℝ) / (blocks : ℝ)
  push_cast
  field_simp [ne_of_gt hblocks]
  ring

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

/-- Restricting a measurable rational-time path to a block and subtracting its
initial value is measurable. -/
theorem measurable_rationalTubeBlockIncrement {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    Measurable (rationalTubeBlockIncrement hblocks j) := by
  rw [measurable_pi_iff]
  intro q
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- Measurability of all block paths follows from measurability of the
original process as a map into the rational-coordinate path space. -/
theorem measurable_rationalUniformBlockProcess {Ω : Type*}
    [MeasurableSpace Ω]
    (X : ↑Skorokhod.RationalunitInterval → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks)
    (hX : Measurable (fun ω q => X q ω)) :
    ∀ j, Measurable (rationalUniformBlockProcess X hblocks j) := by
  intro j
  rw [measurable_pi_iff]
  intro q
  have hEval : ∀ t : ↑Skorokhod.RationalunitInterval,
      Measurable (fun ω => X t ω) := by
    intro t
    exact (measurable_pi_iff.mp hX) t
  exact (hEval _).sub (hEval _)

/-- A block tube is a measurable event in the rational-coordinate path space.
-/
theorem measurableSet_rationalTubeBlockEvent (width : ℝ) {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    MeasurableSet (rationalTubeBlockEvent width hblocks j) := by
  exact (Skorokhod.measurableSet_rationalCoordinateOscillationTube width).preimage
    (measurable_rationalTubeBlockIncrement hblocks j)

/-- A global rational-coordinate tube gives the same oscillation bound on
every block increment path. This deterministic inclusion is needed for an
upper block bound; only independence remains to turn it into a power of a
one-block probability. -/
theorem rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
    (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) :
    Skorokhod.rationalCoordinateOscillationTube width ⊆
      ⋂ j : Fin blocks, rationalTubeBlockEvent width hblocks j := by
  intro x hx
  simp only [Set.mem_iInter]
  intro j
  change rationalTubeBlockIncrement hblocks j x ∈
    Skorokhod.rationalCoordinateOscillationTube width
  change ∃ margin : ℚ, 0 < (margin : ℝ) ∧
    ∀ s t : ↑Skorokhod.RationalunitInterval, |x s - x t| ≤ width - margin at hx
  rcases hx with ⟨margin, hmargin, hbound⟩
  refine ⟨margin, hmargin, ?_⟩
  intro s t
  change |(x (rationalUniformBlockTime hblocks j s) -
      x (rationalUniformBlockTime hblocks j 0)) -
    (x (rationalUniformBlockTime hblocks j t) -
      x (rationalUniformBlockTime hblocks j 0))| ≤ width - margin
  rw [show (x (rationalUniformBlockTime hblocks j s) -
      x (rationalUniformBlockTime hblocks j 0)) -
    (x (rationalUniformBlockTime hblocks j t) -
      x (rationalUniformBlockTime hblocks j 0)) =
      x (rationalUniformBlockTime hblocks j s) -
        x (rationalUniformBlockTime hblocks j t) by ring]
  exact hbound _ _

/-- For any measure on rational-coordinate paths, the global tube probability
is bounded by the probability of the intersection of its block restrictions.
This theorem is purely pathwise; independent increments are needed for the
product formula in the next step of Lemma 2(c). -/
theorem measure_rationalTube_le_uniformBlockInter
    (P : Measure (↑Skorokhod.RationalunitInterval → ℝ)) (width : ℝ) {blocks : ℕ}
    (hblocks : 0 < blocks) :
    P (Skorokhod.rationalCoordinateOscillationTube width) ≤
      P (⋂ j : Fin blocks, rationalTubeBlockEvent width hblocks j) :=
  measure_mono
    (rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
      width hblocks)

/-- Independent block paths factor the probability of the intersection of
their tube events. This uses Mathlib's finite-family independence theorem; the
stable-process proof still has to derive `hblocks` from independent
increments. -/
theorem measure_iInter_rationalTubeBlock_eq_prod
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {blocks : ℕ}
    (X : Fin blocks → Ω → ↑Skorokhod.RationalunitInterval → ℝ)
    (hblocks : iIndepFun X P) (width : ℝ) :
    P (⋂ j : Fin blocks,
        X j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) =
      ∏ j : Fin blocks,
        P (X j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) := by
  have hfactor := hblocks.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (Fin blocks))
    (sets := fun _ => Skorokhod.rationalCoordinateOscillationTube width)
    (by
      intro j hj
      exact Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  simpa using hfactor

/-- The upper block inequality for a uniform rational partition,
conditional only on the two probabilistic facts that remain to be derived
from the stable independent-increment specification: independence of the
block paths and equality of their path laws. -/
theorem measure_rationalTube_le_pow_of_iIndep_uniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ↑Skorokhod.RationalunitInterval → Ω → ℝ)
    {blocks : ℕ} (hblocksPos : 0 < blocks) (width : ℝ)
    (hindep : iIndepFun (rationalUniformBlockProcess X hblocksPos) P)
    (hsameLaw : ∀ j : Fin blocks,
      IdentDistrib (rationalUniformBlockProcess X hblocksPos j)
        (rationalUniformBlockProcess X hblocksPos ⟨0, hblocksPos⟩) P P) :
    P ((fun ω q => X q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      (P ((rationalUniformBlockProcess X hblocksPos ⟨0, hblocksPos⟩) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) ^ blocks := by
  let blockProcess := rationalUniformBlockProcess X hblocksPos
  have hsubset :
      (fun ω q => X q ω) ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube width ⊆
        ⋂ j : Fin blocks,
          blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width := by
    intro ω hω
    simp only [Set.mem_iInter]
    intro j
    have hglobal : (fun q => X q ω) ∈
        Skorokhod.rationalCoordinateOscillationTube width := hω
    have hlocal :=
      rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
        width hblocksPos hglobal
    have hlocalj := Set.mem_iInter.mp hlocal j
    simpa [blockProcess, rationalUniformBlockProcess, rationalTubeBlockEvent,
      Set.mem_preimage] using hlocalj
  have hfactor := measure_iInter_rationalTubeBlock_eq_prod P blockProcess
    hindep width
  have hsame (j : Fin blocks) :
      P (blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) =
        P (blockProcess ⟨0, hblocksPos⟩ ⁻¹'
          Skorokhod.rationalCoordinateOscillationTube width) := by
    exact (hsameLaw j).measure_mem_eq
      (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
  calc
    P ((fun ω q => X q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ≤
      P (⋂ j : Fin blocks,
        blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) :=
      measure_mono hsubset
    _ = ∏ j : Fin blocks,
        P (blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) := by
      exact hfactor
    _ = (P (blockProcess ⟨0, hblocksPos⟩ ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) ^ blocks := by
      simp_rw [hsame]
      simp

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
