/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Return.Basic
public import Probability.Kernel.Step.Noise.Map
public import Probability.Kernel.Step.Noise.Restriction

/-!
# Correlated marks on an additive walk confined to a corridor

## Public declarations

In `ProbabilityTheory.RandomWalk.SmallDeviation.Marked`:

* `corridorEvent lower upper drift threshold horizon initial` is
  `{ω | lower ≤ initial + ∑_(j<k)(Xⱼ-drift) ≤ upper (1≤k≤horizon),
  Bⱼ ≤ threshold (j<horizon)}` for joint observations `ωⱼ=(Xⱼ,Bⱼ)`.
* `killedMarkedStep` reads the displacement from a joint observation and uses
  the existing interval-killed partial step. Mark acceptance is imposed by
  `Kernel.restrictNoise`, rather than by a normalized increment law.
* `killedMarkedStep_measurable`, `survivesPrefix_killedMarkedStep_iff`,
  `survivesPrefix_restrictNoise_killedMarkedStep_iff`,
  `endsInPrefix_killedMarkedStep_iff`,
  and `measurableSet_corridorEvent` provide measurability and identify the
  partial-step survival event with the confined marked-walk event.

Dependence within each displacement/mark pair is retained. The linear drift
is deterministic; no law of a centered conditioned walk is introduced.
-/

@[expose] public section
namespace ProbabilityTheory.RandomWalk.SmallDeviation.Marked
open MeasureTheory
open scoped Classical

set_option backward.isDefEq.respectTransparency false

/-- The joint increment path stays in the corridor and every mark is accepted. -/
def corridorEvent (lower upper drift threshold : ℝ) (horizon : ℕ) (initial : ℝ) :
    Set (ℕ → ℝ × ℝ) :=
  {ω | StaysIn (Set.Icc lower upper) horizon initial (fun j => (ω j).1 - drift) ∧
    ∀ j < horizon, (ω j).2 ≤ threshold}

/-- The original displacement update, with killing on exit from the interval. -/
noncomputable def killedMarkedStep (lower upper drift : ℝ) (x : ℝ) (z : ℝ × ℝ) :
    Option ℝ := killedStep (Set.Icc lower upper) x (z.1 - drift)

theorem killedMarkedStep_measurable (lower upper drift : ℝ) :
    Measurable (Function.uncurry (killedMarkedStep lower upper drift)) :=
  (killedStep_measurable (Set.Icc lower upper) measurableSet_Icc).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).sub measurable_const))

/-- The original joint-noise step is the drifted additive path killed on exit. -/
theorem survivesPrefix_killedMarkedStep_iff (lower upper drift : ℝ)
    (horizon : ℕ) (initial : ℝ) (ω : ℕ → ℝ × ℝ) :
    Kernel.SurvivesPrefix (killedMarkedStep lower upper drift) horizon initial ω ↔
      StaysIn (Set.Icc lower upper) horizon initial (fun j => (ω j).1 - drift) := by
  unfold Kernel.SurvivesPrefix Kernel.Survives killedMarkedStep
  rw [Kernel.runPartialSteps_comp_noise]
  have h := survivesPrefix_killedStep_iff
    (Set.Icc lower upper) horizon initial (fun j => (ω j).1 - drift)
  simp only [Kernel.SurvivesPrefix, Kernel.Survives] at h
  exact h

theorem survivesPrefix_restrictNoise_killedMarkedStep_iff (lower upper drift threshold : ℝ)
    (horizon : ℕ) (initial : ℝ) (ω : ℕ → ℝ × ℝ) :
    Kernel.SurvivesPrefix
      (Kernel.restrictNoise (killedMarkedStep lower upper drift) {z | z.2 ≤ threshold})
      horizon initial ω ↔ ω ∈ corridorEvent lower upper drift threshold horizon initial := by
  rw [Kernel.survivesPrefix_restrictNoise_iff]
  unfold Kernel.SurvivesPrefix Kernel.Survives killedMarkedStep
  rw [Kernel.runPartialSteps_comp_noise]
  have h := survivesPrefix_killedStep_iff
    (Set.Icc lower upper) horizon initial (fun j => (ω j).1 - drift)
  simp only [Kernel.SurvivesPrefix, Kernel.Survives] at h
  exact and_congr h Iff.rfl

/-- The original joint-noise partial step reaches its target precisely on the
ordinary drifted-walk survival and endpoint event. -/
theorem endsInPrefix_killedMarkedStep_iff (lower upper drift : ℝ)
    (target : Set ℝ) (horizon : ℕ) (initial : ℝ) (ω : ℕ → ℝ × ℝ) :
    Kernel.EndsInPrefix (killedMarkedStep lower upper drift) target horizon initial ω ↔
      StaysIn (Set.Icc lower upper) horizon initial (fun j => (ω j).1 - drift) ∧
        initial + AdditivePath.displacement horizon (fun j => (ω j).1 - drift) ∈ target := by
  unfold Kernel.EndsInPrefix Kernel.EndsIn killedMarkedStep
  rw [Kernel.runPartialSteps_comp_noise]
  have h := endsInPrefix_killedStep_iff
    (Set.Icc lower upper) target horizon initial (fun j => (ω j).1 - drift)
  simp only [Kernel.EndsInPrefix, Kernel.EndsIn] at h
  exact h

theorem measurableSet_corridorEvent (lower upper drift threshold : ℝ)
    (horizon : ℕ) (initial : ℝ) :
    MeasurableSet (corridorEvent lower upper drift threshold horizon initial) := by
  have hs := Kernel.measurableSet_survivesPrefix
    (Kernel.restrictNoise (killedMarkedStep lower upper drift) {z | z.2 ≤ threshold})
    (Kernel.measurable_restrictNoise _ (killedMarkedStep_measurable lower upper drift)
      (measurableSet_le measurable_snd measurable_const)) horizon initial
  convert hs using 1
  ext ω
  exact (survivesPrefix_restrictNoise_killedMarkedStep_iff lower upper drift threshold horizon initial ω).symm

end ProbabilityTheory.RandomWalk.SmallDeviation.Marked
