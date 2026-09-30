module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Topology.Cadlag.Skorokhod.Oscillation.Dense

/-!
# Uniform rational block restrictions

This module contains the path-level part of a uniform corridor partition.
It is independent of stable laws and of any particular process: a path on
rational times is cut into translated block paths, and the resulting tube
events are measurable.  Stable Lévy processes supply the block laws and
independence in `Probability.Process.Stable.SmallDeviation.Blocks`.
-/

open MeasureTheory

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
    MeasurableSet (rationalTubeBlockEvent width hblocks j) :=
  (Skorokhod.measurableSet_rationalCoordinateOscillationTube width).preimage
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
their tube events. This uses Mathlib's finite-family independence theorem. -/
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

/-- The upper block inequality for a uniform rational partition, conditional
only on independence of the block paths and equality of their path laws. -/
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
        P (blockProcess j ⁻¹' Skorokhod.rationalCoordinateOscillationTube width) :=
      hfactor
    _ = (P (blockProcess ⟨0, hblocksPos⟩ ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) ^ blocks := by
      simp_rw [hsame]
      simp

end ProbabilityTheory

end
