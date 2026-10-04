import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.PathClass.Energy

open ProbabilityTheory.RandomWalk.Mogulskii
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.Mogulskii.PathClassTest

private noncomputable def halfTime : unitInterval := ⟨(1 / 2 : ℝ), by norm_num⟩

private theorem halfTime_ne_bot : halfTime ≠ ⊥ := by
  intro h
  have := congrArg Subtype.val h
  norm_num [halfTime] at this

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

#print axioms ProbabilityTheory.RandomWalk.Mogulskii.hasContinuousAdmissiblePath_implies_startAdmissible
#print axioms ProbabilityTheory.RandomWalk.Mogulskii.hasContinuousAdmissiblePath_implies_traceSeparated
#print axioms ProbabilityTheory.RandomWalk.Mogulskii.hasContinuousAdmissiblePath_implies_startAndTraceSeparated
#print axioms ProbabilityTheory.RandomWalk.Mogulskii.lintegral_eq_zero_of_eq_zero_off_top
#print axioms ProbabilityTheory.RandomWalk.Mogulskii.M2Corridor.energy_eq_of_boundaries_eq_off_top

end ProbabilityTheory.RandomWalk.Mogulskii.PathClassTest
