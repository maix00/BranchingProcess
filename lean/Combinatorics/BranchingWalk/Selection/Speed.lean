import Combinatorics.BranchingWalk.Selection.Frontier
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Asymptotic speed of a frontier

The speed of a frontier is the limit of `p n / n`, where `p n` is the position
of the frontier particle at generation `n`. The definition only uses a scalar
action and a topology, so it applies verbatim to the order-dual position type
and therefore to both the leftmost and the rightmost rule.

Nothing here assumes a law: `HasAsymptoticSpeed` is a deterministic statement
about a sequence of positions. A branching random walk proves it for the
frontier path of its selected walk, and that proof belongs to the probability
layer. The deterministic content isolated here is the definition, uniqueness
of the speed, its invariance under shifting the time index, and the fact that
reversing the order exchanges the two frontier speeds.

A generation of a walk may be empty, because a particle may have no offspring;
so a frontier path is only defined under an explicit non-extinction hypothesis.
Non-extinction of the branching random walk is a probabilistic statement and is
not proved here.
-/

open Filter

open scoped Topology

namespace Combinatorics

namespace Branching

namespace Selection

section Speed

variable {𝕜 X : Type*} [Field 𝕜] [TopologicalSpace X] [SMul 𝕜 X]

/-- A sequence of positions has asymptotic speed `c` when `p n / n` converges
to `c`. -/
def HasAsymptoticSpeed (p : ℕ → X) (c : X) : Prop :=
  Tendsto (fun n : ℕ => ((n : 𝕜))⁻¹ • p n) atTop (𝓝 c)

theorem hasAsymptoticSpeed_def (p : ℕ → X) (c : X) :
    HasAsymptoticSpeed (𝕜 := 𝕜) p c ↔
      Tendsto (fun n : ℕ => ((n : 𝕜))⁻¹ • p n) atTop (𝓝 c) :=
  Iff.rfl

/-- The asymptotic speed of a sequence is unique. -/
theorem hasAsymptoticSpeed_unique [T2Space X] {p : ℕ → X} {c d : X}
    (hc : HasAsymptoticSpeed (𝕜 := 𝕜) p c)
    (hd : HasAsymptoticSpeed (𝕜 := 𝕜) p d) :
    c = d :=
  tendsto_nhds_unique hc hd

/-- Shifting the time index does not change the asymptotic speed. -/
theorem hasAsymptoticSpeed_iff_succ (p : ℕ → X) (c : X) :
    HasAsymptoticSpeed (𝕜 := 𝕜) p c ↔
      Tendsto (fun n : ℕ => (((n : ℕ) + 1 : ℕ) : 𝕜)⁻¹ • p ((n : ℕ) + 1))
        atTop (𝓝 c) := by
  constructor
  · intro h
    exact (tendsto_add_atTop_iff_nat (f := fun n : ℕ => ((n : 𝕜))⁻¹ • p n) 1).2 h
  · intro h
    exact (tendsto_add_atTop_iff_nat (f := fun n : ℕ => ((n : 𝕜))⁻¹ • p n) 1).1 h

/-- Reversing the order of positions preserves asymptotic speeds. -/
theorem hasAsymptoticSpeed_mapOrderDual_iff (p : ℕ → X) (c : X) :
    HasAsymptoticSpeed (𝕜 := 𝕜) (fun n => OrderDual.toDual (p n))
        (OrderDual.toDual c) ↔
      HasAsymptoticSpeed (𝕜 := 𝕜) p c :=
  Iff.rfl

end Speed

section FrontierPath

variable {X : Type*} [DecidableEq X] [LinearOrder X] {N : ℕ} {M : Mechanism X N}

namespace Walk

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
    V.lowerPath h n = V.lowerPoint n (h n) :=
  rfl

@[simp] theorem upperPath_apply (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty) (n : ℕ) :
    V.upperPath h n = V.upperPoint n (h n) :=
  rfl

/-- Reversing the order of a walk swaps its two frontier paths. -/
theorem lowerPath_mapOrderDual (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty)
    (h' : ∀ n, (V.mapOrderDual.population n).Nonempty) :
    (V.mapOrderDual).lowerPath h' =
      fun n => OrderDual.toDual (V.upperPath h n) := by
  funext n
  exact lowerPoint_mapOrderDual V n (h n) (h' n)

theorem upperPath_mapOrderDual (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty)
    (h' : ∀ n, (V.mapOrderDual.population n).Nonempty) :
    (V.mapOrderDual).upperPath h' =
      fun n => OrderDual.toDual (V.lowerPath h n) := by
  funext n
  exact upperPoint_mapOrderDual V n (h n) (h' n)

end Walk

end FrontierPath

section FrontierSpeed

variable {𝕜 X : Type*} [Field 𝕜] [TopologicalSpace X] [SMul 𝕜 X]
variable [DecidableEq X] [LinearOrder X] {N : ℕ} {M : Mechanism X N}

namespace Walk

/-- The lower frontier of a walk has asymptotic speed `c`. -/
def HasLowerFrontierSpeed (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty) (c : X) : Prop :=
  HasAsymptoticSpeed (𝕜 := 𝕜) (V.lowerPath h) c

/-- The upper frontier of a walk has asymptotic speed `c`. -/
def HasUpperFrontierSpeed (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty) (c : X) : Prop :=
  HasAsymptoticSpeed (𝕜 := 𝕜) (V.upperPath h) c

theorem hasLowerFrontierSpeed_iff (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty) (c : X) :
    HasLowerFrontierSpeed (𝕜 := 𝕜) V h c ↔
      Tendsto (fun n : ℕ => ((n : 𝕜))⁻¹ • V.lowerPath h n) atTop (𝓝 c) :=
  Iff.rfl

/-- The lower frontier of the reversed walk moves at the speed of the upper
frontier of the walk. -/
theorem hasLowerFrontierSpeed_mapOrderDual_iff (V : Walk N X M)
    (h : ∀ n, (V.population n).Nonempty)
    (h' : ∀ n, (V.mapOrderDual.population n).Nonempty) (c : X) :
    HasLowerFrontierSpeed (𝕜 := 𝕜) V.mapOrderDual h' (OrderDual.toDual c) ↔
      HasUpperFrontierSpeed (𝕜 := 𝕜) V h c := by
  rw [HasLowerFrontierSpeed, HasUpperFrontierSpeed, lowerPath_mapOrderDual]
  exact hasAsymptoticSpeed_mapOrderDual_iff (𝕜 := 𝕜) (V.upperPath h) c

end Walk

end FrontierSpeed

end Selection

end Branching

end Combinatorics
