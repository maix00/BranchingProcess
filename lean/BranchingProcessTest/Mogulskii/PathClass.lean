import Probability.Process.SmallDeviation.Mogulskii.PathClass.Energy

open MeasureTheory
open ProbabilityTheory.Process.SmallDeviation.Mogulskii
open scoped ENNReal

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii.PathClassTest

private noncomputable def halfTime : unitInterval := ⟨(1 / 2 : ℝ), by norm_num⟩

private theorem halfTime_ne_bot : halfTime ≠ ⊥ := by
  intro h
  have := congrArg Subtype.val h
  norm_num [halfTime] at this

private noncomputable def terminalUpper : StepBoundary :=
  StepBoundary.singleJump ⊤ (by norm_num) 2 1

private noncomputable def terminalLower : StepBoundary :=
  StepBoundary.singleJump ⊤ (by norm_num) (-2) (-1)

private noncomputable def terminalCrossingLower : StepBoundary :=
  StepBoundary.singleJump ⊤ (by norm_num) (-2) 3

private noncomputable def interiorUpper : StepBoundary :=
  StepBoundary.singleJump halfTime halfTime_ne_bot 2 1

private noncomputable def interiorLower : StepBoundary :=
  StepBoundary.singleJump halfTime halfTime_ne_bot (-2) (-1)

private noncomputable def interiorCrossingLower : StepBoundary :=
  StepBoundary.singleJump halfTime halfTime_ne_bot (-2) 3

private theorem terminalStartAdmissible :
    StartAdmissible terminalUpper terminalLower := by
  have hl : terminalLower.eval ⊥ = -2 := by
    simp [terminalLower, StepBoundary.singleJump, StepBoundary.eval, StepBoundary.levelIndex]
  have hu : terminalUpper.eval ⊥ = 2 := by
    simp [terminalUpper, StepBoundary.singleJump, StepBoundary.eval, StepBoundary.levelIndex]
  rw [StartAdmissible, hl, hu]
  exact ⟨EReal.coe_lt_coe (by norm_num : (-2 : ℝ) < 0),
    EReal.coe_lt_coe (by norm_num : (0 : ℝ) < 2)⟩

private theorem terminalTraceSeparated : TraceSeparated terminalUpper terminalLower := by
  intro t
  by_cases ht : t = ⊤
  · subst t
    have hlu : terminalLower.leftTrace ⊤ = -2 := by
      simpa [terminalLower] using
        StepBoundary.leftTrace_singleJump ⊤ (by norm_num) (-2) (-1)
    have hru : terminalUpper.rightTrace ⊤ = 1 := by
      simpa [terminalUpper] using
        StepBoundary.rightTrace_singleJump ⊤ (by norm_num) 2 1
    have hll : terminalLower.rightTrace ⊤ = -1 := by
      simpa [terminalLower] using
        StepBoundary.rightTrace_singleJump ⊤ (by norm_num) (-2) (-1)
    have hrl : terminalUpper.leftTrace ⊤ = 2 := by
      simpa [terminalUpper] using
        StepBoundary.leftTrace_singleJump ⊤ (by norm_num) 2 1
    rw [hlu, hll, hrl, hru]
    rw [max_eq_right (by
      change ((-2 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal)
      exact EReal.coe_le_coe (by norm_num : (-2 : ℝ) ≤ -1)),
      min_eq_right (by
        change ((1 : ℝ) : EReal) ≤ ((2 : ℝ) : EReal)
        exact EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 2))]
    change ((-1 : ℝ) : EReal) < ((1 : ℝ) : EReal)
    exact EReal.coe_lt_coe (by norm_num : (-1 : ℝ) < 1)
  · have hnotu : t ∉ terminalUpper.knots := by
      simp [terminalUpper, StepBoundary.singleJump, ht]
    have hnotl : t ∉ terminalLower.knots := by
      simp [terminalLower, StepBoundary.singleJump, ht]
    rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem terminalLower hnotl,
      StepBoundary.leftTrace_eq_rightTrace_of_not_mem terminalUpper hnotu,
      StepBoundary.rightTrace_eq_eval terminalLower,
      StepBoundary.rightTrace_eq_eval terminalUpper]
    have htlt : t < ⊤ := lt_top_iff_ne_top.mpr ht
    have hl : terminalLower.eval t = -2 := by
      simpa [terminalLower] using
        StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num) htlt (-2) (-1)
    have hu : terminalUpper.eval t = 2 := by
      simpa [terminalUpper] using
        StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num) htlt 2 1
    rw [hl, hu]
    simp only [max_self, min_self]
    change ((-2 : ℝ) : EReal) < ((2 : ℝ) : EReal)
    exact EReal.coe_lt_coe (by norm_num : (-2 : ℝ) < 2)

private theorem terminalCrossing_notTraceSeparated :
    ¬ TraceSeparated terminalUpper terminalCrossingLower := by
  intro h
  have htop := h ⊤
  have hlu : terminalCrossingLower.leftTrace ⊤ = -2 := by
    simpa [terminalCrossingLower] using
      StepBoundary.leftTrace_singleJump ⊤ (by norm_num) (-2) 3
  have hru : terminalUpper.rightTrace ⊤ = 1 := by
    simpa [terminalUpper] using StepBoundary.rightTrace_singleJump ⊤ (by norm_num) 2 1
  have hll : terminalCrossingLower.rightTrace ⊤ = 3 := by
    simpa [terminalCrossingLower] using
      StepBoundary.rightTrace_singleJump ⊤ (by norm_num) (-2) 3
  have hrl : terminalUpper.leftTrace ⊤ = 2 := by
    simpa [terminalUpper] using StepBoundary.leftTrace_singleJump ⊤ (by norm_num) 2 1
  rw [hlu, hll, hrl, hru] at htop
  have hmax : max (-2 : EReal) 3 = 3 := by
    rw [max_eq_right (by
      change ((-2 : ℝ) : EReal) ≤ ((3 : ℝ) : EReal)
      exact EReal.coe_le_coe (by norm_num : (-2 : ℝ) ≤ 3))]
  have hmin : min (2 : EReal) 1 = 1 := by
    rw [min_eq_right (by
      change ((1 : ℝ) : EReal) ≤ ((2 : ℝ) : EReal)
      exact EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 2))]
  rw [hmax, hmin] at htop
  have hge : (1 : EReal) ≤ 3 := by
    change ((1 : ℝ) : EReal) ≤ ((3 : ℝ) : EReal)
    exact EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 3)
  exact (not_lt_of_ge hge) htop

private theorem interiorTraceSeparated : TraceSeparated interiorUpper interiorLower := by
  intro t
  by_cases ht : t = halfTime
  · subst t
    have hll : interiorLower.leftTrace halfTime = -2 := by
      simpa [interiorLower] using
        StepBoundary.leftTrace_singleJump halfTime halfTime_ne_bot (-2) (-1)
    have hlr : interiorLower.rightTrace halfTime = -1 := by
      simpa [interiorLower] using
        StepBoundary.rightTrace_singleJump halfTime halfTime_ne_bot (-2) (-1)
    have hul : interiorUpper.leftTrace halfTime = 2 := by
      simpa [interiorUpper] using
        StepBoundary.leftTrace_singleJump halfTime halfTime_ne_bot 2 1
    have hur : interiorUpper.rightTrace halfTime = 1 := by
      simpa [interiorUpper] using
        StepBoundary.rightTrace_singleJump halfTime halfTime_ne_bot 2 1
    rw [hll, hlr, hul, hur]
    rw [max_eq_right (show (-2 : EReal) ≤ -1 from
        EReal.coe_le_coe (by norm_num : (-2 : ℝ) ≤ -1)),
      min_eq_right (show (1 : EReal) ≤ 2 from
        EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 2))]
    exact EReal.coe_lt_coe (by norm_num : (-1 : ℝ) < 1)
  · have hnotL : t ∉ interiorLower.knots := by
      change t ∉ ({halfTime} : Finset unitInterval)
      simpa using ht
    have hnotU : t ∉ interiorUpper.knots := by
      change t ∉ ({halfTime} : Finset unitInterval)
      simpa using ht
    rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem _ hnotL,
      StepBoundary.rightTrace_eq_eval, StepBoundary.leftTrace_eq_rightTrace_of_not_mem _ hnotU,
      StepBoundary.rightTrace_eq_eval]
    rcases lt_or_gt_of_ne ht with hbefore | hafter
    · have hl : interiorLower.eval t = -2 := by
        change (StepBoundary.singleJump halfTime halfTime_ne_bot (-2) (-1)).eval t = -2
        exact StepBoundary.eval_singleJump_of_lt halfTime halfTime_ne_bot hbefore (-2) (-1)
      have hu : interiorUpper.eval t = 2 := by
        change (StepBoundary.singleJump halfTime halfTime_ne_bot 2 1).eval t = 2
        exact StepBoundary.eval_singleJump_of_lt halfTime halfTime_ne_bot hbefore 2 1
      rw [hl, hu]
      change max ((-2 : ℝ) : EReal) ((-2 : ℝ) : EReal) <
        min ((2 : ℝ) : EReal) ((2 : ℝ) : EReal)
      rw [max_self, min_self]
      exact EReal.coe_lt_coe (by norm_num : (-2 : ℝ) < 2)
    · have hl : interiorLower.eval t = -1 := by
        change (StepBoundary.singleJump halfTime halfTime_ne_bot (-2) (-1)).eval t = -1
        exact StepBoundary.eval_singleJump_of_le halfTime halfTime_ne_bot hafter.le (-2) (-1)
      have hu : interiorUpper.eval t = 1 := by
        change (StepBoundary.singleJump halfTime halfTime_ne_bot 2 1).eval t = 1
        exact StepBoundary.eval_singleJump_of_le halfTime halfTime_ne_bot hafter.le 2 1
      rw [hl, hu]
      change max ((-1 : ℝ) : EReal) ((-1 : ℝ) : EReal) <
        min ((1 : ℝ) : EReal) ((1 : ℝ) : EReal)
      rw [max_self, min_self]
      exact EReal.coe_lt_coe (by norm_num : (-1 : ℝ) < 1)

private theorem interiorCrossing_notTraceSeparated :
    ¬ TraceSeparated interiorUpper interiorCrossingLower := by
  intro h
  have hmid := h halfTime
  have hll : interiorCrossingLower.leftTrace halfTime = -2 := by
    simpa [interiorCrossingLower] using
      StepBoundary.leftTrace_singleJump halfTime halfTime_ne_bot (-2) 3
  have hlr : interiorCrossingLower.rightTrace halfTime = 3 := by
    simpa [interiorCrossingLower] using
      StepBoundary.rightTrace_singleJump halfTime halfTime_ne_bot (-2) 3
  have hul : interiorUpper.leftTrace halfTime = 2 := by
    simpa [interiorUpper] using
      StepBoundary.leftTrace_singleJump halfTime halfTime_ne_bot 2 1
  have hur : interiorUpper.rightTrace halfTime = 1 := by
    simpa [interiorUpper] using
      StepBoundary.rightTrace_singleJump halfTime halfTime_ne_bot 2 1
  rw [hll, hlr, hul, hur] at hmid
  have hmax : max (-2 : EReal) 3 = 3 := by
    rw [max_eq_right (show (-2 : EReal) ≤ 3 from
      EReal.coe_le_coe (by norm_num : (-2 : ℝ) ≤ 3))]
  have hmin : min (2 : EReal) 1 = 1 := by
    rw [min_eq_right (show (1 : EReal) ≤ 2 from
      EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 2))]
  rw [hmax, hmin] at hmid
  exact (not_lt_of_ge (EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 3))) hmid

/-- Constant boundaries have the expected value and endpoint traces. -/
example (t : unitInterval) :
    (StepBoundary.constant (3 : EReal)).eval t = 3 ∧
      (StepBoundary.constant (3 : EReal)).leftTrace t = 3 ∧
      (StepBoundary.constant (3 : EReal)).rightTrace t = 3 := by
  simp

/-- A constant continuous path witnesses the nonempty corridor case. -/
example : HasContinuousAdmissiblePath
    (StepBoundary.constant (1 : EReal))
    (StepBoundary.constant (-1 : EReal)) := by
  let f : C(unitInterval, ℝ) := ContinuousMap.const _ 0
  refine ⟨f, rfl, ?_⟩
  constructor
  · rfl
  · intro t
    simp only [StepBoundary.eval_constant, f, ContinuousMap.const_apply,
      Skorokhod.ofContinuousMap_apply]
    constructor <;> exact EReal.coe_lt_coe (by norm_num)

/-- An interior jump uses the post-jump value at the knot and its previous
level as the left trace. -/
example :
    (StepBoundary.singleJump halfTime halfTime_ne_bot (0 : EReal) 2).leftTrace halfTime = 0 ∧
      (StepBoundary.singleJump halfTime halfTime_ne_bot (0 : EReal) 2).rightTrace halfTime = 2 := by
  constructor
  · exact StepBoundary.leftTrace_singleJump halfTime halfTime_ne_bot 0 2
  · rw [StepBoundary.rightTrace_eq_eval, StepBoundary.eval]
    simp [StepBoundary.singleJump, StepBoundary.levelIndex,
      Finset.filter_singleton, Finset.card_singleton]

/-- The overlap condition at an interior jump is true when the left and right
corridor intervals overlap. -/
example :
    max ((-2 : ℝ) : EReal) ((-1 : ℝ) : EReal) <
      min ((2 : ℝ) : EReal) ((1 : ℝ) : EReal) := by
  rw [max_eq_right (EReal.coe_le_coe (by norm_num : (-2 : ℝ) ≤ -1)),
    min_eq_right (EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 2))]
  exact EReal.coe_lt_coe (by norm_num : (-1 : ℝ) < 1)

/-- The overlap condition at an interior jump is false when the right lower
boundary crosses above the left upper boundary. -/
example :
    ¬ max ((-2 : ℝ) : EReal) ((3 : ℝ) : EReal) <
      min ((2 : ℝ) : EReal) ((1 : ℝ) : EReal) := by
  rw [max_eq_right (EReal.coe_le_coe (by norm_num : (-2 : ℝ) ≤ 3)),
    min_eq_right (EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 2))]
  exact not_lt_of_ge (EReal.coe_le_coe (by norm_num : (1 : ℝ) ≤ 3))

/-- A terminal knot is allowed and has distinct left and right traces. -/
example :
    (StepBoundary.singleJump ⊤ (by norm_num : (⊤ : unitInterval) ≠ ⊥)
      (1 : EReal) 2).leftTrace ⊤ = 1 ∧
      (StepBoundary.singleJump ⊤ (by norm_num : (⊤ : unitInterval) ≠ ⊥)
        (1 : EReal) 2).rightTrace ⊤ = 2 := by
  constructor
  · rw [StepBoundary.leftTrace_top]
    · simp [StepBoundary.singleJump]
    · simp [StepBoundary.singleJump]
  · rw [StepBoundary.rightTrace_eq_eval, StepBoundary.eval,
      StepBoundary.singleJump, StepBoundary.levelIndex]
    simp [Finset.card_singleton]

/-- Terminal trace overlap and non-overlap are both represented by the same
order test used at interior knots. -/
example : max ((-2 : ℝ) : EReal) ((-1 : ℝ) : EReal) <
    min ((2 : ℝ) : EReal) ((3 : ℝ) : EReal) := by
  rw [max_eq_right (EReal.coe_le_coe (by norm_num : (-2 : ℝ) ≤ -1)),
    min_eq_left (EReal.coe_le_coe (by norm_num : (2 : ℝ) ≤ 3))]
  exact EReal.coe_lt_coe (by norm_num : (-1 : ℝ) < 2)

example : ¬ max ((-2 : ℝ) : EReal) ((3 : ℝ) : EReal) <
    min ((2 : ℝ) : EReal) ((2 : ℝ) : EReal) := by
  rw [max_eq_right (EReal.coe_le_coe (by norm_num : (-2 : ℝ) ≤ 3))]
  simp only [min_self]
  exact not_lt_of_ge (EReal.coe_le_coe (by norm_num : (2 : ℝ) ≤ 3))

/-- An interior jump with overlapping left and right corridors satisfies the
trace criterion. -/
example : TraceSeparated interiorUpper interiorLower := interiorTraceSeparated

/-- An interior jump that crosses the upper boundary fails the trace
criterion. -/
example : ¬ TraceSeparated interiorUpper interiorCrossingLower :=
  interiorCrossing_notTraceSeparated

/-- The overlapping interior-jump corridor has a continuous admissible path. -/
example : HasContinuousAdmissiblePath interiorUpper interiorLower := by
  apply (hasContinuousAdmissiblePath_iff_startAndTraceSeparated).2
  constructor
  · have hl : interiorLower.eval ⊥ = -2 := by
      have hbot : (⊥ : unitInterval) < halfTime :=
        bot_lt_iff_ne_bot.mpr halfTime_ne_bot
      simpa [interiorLower] using
        StepBoundary.eval_singleJump_of_lt halfTime halfTime_ne_bot hbot (-2) (-1)
    have hu : interiorUpper.eval ⊥ = 2 := by
      have hbot : (⊥ : unitInterval) < halfTime :=
        bot_lt_iff_ne_bot.mpr halfTime_ne_bot
      simpa [interiorUpper] using
        StepBoundary.eval_singleJump_of_lt halfTime halfTime_ne_bot hbot 2 1
    rw [StartAdmissible, hl, hu]
    exact ⟨EReal.coe_lt_coe (by norm_num : (-2 : ℝ) < 0),
      EReal.coe_lt_coe (by norm_num : (0 : ℝ) < 2)⟩
  · exact interiorTraceSeparated

/-- The crossing interior-jump corridor admits no continuous admissible
path. -/
example : ¬ HasContinuousAdmissiblePath interiorUpper interiorCrossingLower := by
  intro h
  exact interiorCrossing_notTraceSeparated
    ((hasContinuousAdmissiblePath_iff_startAndTraceSeparated.mp h).2)

/-- A terminal jump with overlap on its two sides satisfies the exact
trace criterion and admits a continuous corridor path. -/
example : HasContinuousAdmissiblePath terminalUpper terminalLower := by
  exact (hasContinuousAdmissiblePath_iff_startAndTraceSeparated).2
    ⟨terminalStartAdmissible, terminalTraceSeparated⟩

/-- If the terminal lower boundary jumps past the upper corridor, the exact
trace criterion rejects continuous admissibility. -/
example : ¬ HasContinuousAdmissiblePath terminalUpper terminalCrossingLower := by
  intro h
  exact terminalCrossing_notTraceSeparated
    ((hasContinuousAdmissiblePath_iff_startAndTraceSeparated.mp h).2)

/-- The initial value condition is independent of the local trace-gap
condition: this corridor excludes the required starting value zero. -/
example :
    ¬ StartAdmissible (StepBoundary.constant (2 : EReal))
      (StepBoundary.constant (1 : EReal)) := by
  norm_num [StartAdmissible]

/-- Infinite sides are accepted by the totalized width cost. -/
example (α : ℝ) :
    widthCost α ⊤ (0 : EReal) = 0 ∧
      widthCost α (0 : EReal) ⊥ = 0 ∧
      widthCost α ⊤ ⊥ = 0 := by
  simp

/-- The trace criterion produces the expected continuous corridor witness
for a constant corridor. -/
example : HasContinuousAdmissiblePath
    (StepBoundary.constant (1 : EReal))
    (StepBoundary.constant (-1 : EReal)) := by
  apply (hasContinuousAdmissiblePath_iff_startAndTraceSeparated).2
  constructor
  · norm_num [StartAdmissible, StepBoundary.constant]
  · intro t
    rw [StepBoundary.leftTrace_constant, StepBoundary.rightTrace_constant,
      StepBoundary.leftTrace_constant, StepBoundary.rightTrace_constant]
    simp only [max_self, min_self]
    change ((-1 : ℝ) : EReal) < ((1 : ℝ) : EReal)
    exact EReal.coe_lt_coe (by norm_num : (-1 : ℝ) < 1)

/-- The level indices and boundary traces used by the energy partition are
measurable. -/
example (b : StepBoundary) : Measurable b.levelIndex ∧
    Measurable b.leftLevelIndex ∧ Measurable b.eval ∧ Measurable b.leftTrace :=
  ⟨b.levelIndex_measurable, b.leftLevelIndex_measurable,
    b.eval_measurable, b.leftTrace_measurable⟩

/-- The energy of every `M₂` corridor is a finite sum over its level cells. -/
example (α : ℝ) (c : M2Corridor) :
    M2Corridor.energy α c =
      ∑ p ∈ c.levelPairIndexSimple.range,
        widthCost α (c.upper.levels p.1) (c.lower.levels p.2) *
          volume (c.levelPairIndex ⁻¹' {p}) :=
  M2Corridor.energy_eq_finiteLevelCellSum α c

#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.hasContinuousAdmissiblePath_implies_startAdmissible
#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.hasContinuousAdmissiblePath_implies_traceSeparated
#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.hasContinuousAdmissiblePath_implies_startAndTraceSeparated
#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.M2Corridor.energy_eq_of_boundaries_eq_off_top
#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.hasContinuousAdmissiblePath_iff_startAndTraceSeparated
#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.StepBoundary.levelIndex_measurable
#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.StepBoundary.leftLevelIndex_measurable
#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.StepBoundary.eval_singleJump_of_le
#print axioms ProbabilityTheory.Process.SmallDeviation.Mogulskii.M2Corridor.energy_eq_finiteLevelCellSum

end ProbabilityTheory.Process.SmallDeviation.Mogulskii.PathClassTest
