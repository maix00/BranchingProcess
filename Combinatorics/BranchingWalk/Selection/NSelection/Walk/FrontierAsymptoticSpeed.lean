/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Sequence.Speed
public import Combinatorics.BranchingWalk.Selection.NSelection.Walk.Frontier

/-!
# Paths and asymptotic speeds of a selected walk's frontiers

## Public declarations

* `Walk.Frontier.lowerPath` and `Walk.Frontier.upperPath` return the least
  and greatest positions in each nonempty generation.
* `Walk.Frontier.HasLowerAsymptoticSpeed` and
  `Walk.Frontier.HasUpperAsymptoticSpeed` assert convergence of the respective
  frontier position divided by the generation index.
* `Walk.Frontier.hasLowerAsymptoticSpeed_mapOrderDual_iff` identifies the
  lower speed after order reversal with the original upper speed.
-/

open Asymptotics _root_.Combinatorics.Selection

@[expose] public section

namespace Combinatorics.Branching.Selection.NSelection

section FrontierPath

variable {X : Type*} [DecidableEq X] [LinearOrder X] {N : ℕ} {M : FiniteNSelection X N}

namespace Walk.Frontier

/-- The path of least particles of a walk whose generations never die. -/
noncomputable def lowerPath (V : Walk N X M) (h : ∀ n, (V.population n).Nonempty) :
    ℕ → X :=
  fun n => V.lowerPoint n (h n)

/-- The path of greatest particles of a walk whose generations never die. -/
noncomputable def upperPath (V : Walk N X M) (h : ∀ n, (V.population n).Nonempty) :
    ℕ → X :=
  fun n => V.upperPoint n (h n)

@[simp] theorem lowerPath_apply (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty) (n : ℕ) :
    lowerPath V h n = V.lowerPoint n (h n) :=
  rfl

@[simp] theorem upperPath_apply (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty) (n : ℕ) :
    upperPath V h n = V.upperPoint n (h n) :=
  rfl

/-- Reversing the order of a walk swaps its two frontier paths. -/
theorem lowerPath_mapOrderDual (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty)
    (h' : ∀ n, (V.mapOrderDual.population n).Nonempty) :
    lowerPath V.mapOrderDual h' =
      fun n => OrderDual.toDual (upperPath V h n) := by
  funext n
  exact lowerPoint_mapOrderDual V n (h n) (h' n)

theorem upperPath_mapOrderDual (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty)
    (h' : ∀ n, (V.mapOrderDual.population n).Nonempty) :
    upperPath V.mapOrderDual h' =
      fun n => OrderDual.toDual (lowerPath V h n) := by
  funext n
  exact upperPoint_mapOrderDual V n (h n) (h' n)

end Walk.Frontier

end FrontierPath

section FrontierSpeed

variable {𝕜 X : Type*} [Field 𝕜] [TopologicalSpace X] [SMul 𝕜 X]
variable [DecidableEq X] [LinearOrder X] {N : ℕ} {M : FiniteNSelection X N}

namespace Walk.Frontier

/-- The lower frontier of a walk has asymptotic speed `c`. -/
def HasLowerAsymptoticSpeed (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty) (c : X) : Prop :=
  HasAsymptoticSpeed (𝕜 := 𝕜) (lowerPath V h) c

/-- The upper frontier of a walk has asymptotic speed `c`. -/
def HasUpperAsymptoticSpeed (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty) (c : X) : Prop :=
  HasAsymptoticSpeed (𝕜 := 𝕜) (upperPath V h) c

/-- The lower frontier of the reversed walk moves at the speed of the upper
frontier of the walk. -/
theorem hasLowerAsymptoticSpeed_mapOrderDual_iff (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty)
    (h' : ∀ n, (V.mapOrderDual.population n).Nonempty) (c : X) :
    HasLowerAsymptoticSpeed (𝕜 := 𝕜) V.mapOrderDual h' (OrderDual.toDual c) ↔
      HasUpperAsymptoticSpeed (𝕜 := 𝕜) V h c := by
  rw [HasLowerAsymptoticSpeed, HasUpperAsymptoticSpeed, lowerPath_mapOrderDual V h h']
  rfl

end Walk.Frontier

end FrontierSpeed

end Combinatorics.Branching.Selection.NSelection

end
