import Combinatorics.BranchingStep.Prefix

/-!
# The slot value of a branching step

`step? ξ i` is the raw optional mark `ξ i`, and `step ξ i` is its
zero-defaulted reading: the mark of a present slot and the zero of the value
monoid for an absent one. The total reading is therefore defined on every
slot. An increasing order condition makes it monotone in the slot label.
-/

namespace BranchingStep

/-- The raw optional mark of a slot. -/
def step? {ι X : Type*} (ξ : Step ι X) (i : ι) : Option X := ξ i

@[simp] theorem step?_apply {ι X : Type*} (ξ : Step ι X) (i : ι) :
    step? ξ i = ξ i := rfl

/-- The zero-defaulted mark of a slot. -/
def step {X : Type*} [Zero X] (ξ : Step ι X) (i : ι) : X :=
  (step? ξ i).getD 0

theorem step_eq_getD {ι X : Type*} [Zero X]
    (ξ : Step ι X) (i : ι) :
    step ξ i = (ξ i).getD 0 := rfl

theorem step_measurable
    {ι X : Type*} [MeasurableSpace X] [Zero X] (i : ι) :
    Measurable (fun ξ : Step ι X => step ξ i) := by
  rw [show (fun ξ : Step ι X => step ξ i) =
      fun ξ : Step ι X => (ξ i).getD (0 : X) by
        funext ξ; exact step_eq_getD ξ i]
  exact (measurable_optionGetD (0 : X)).comp (measurable_pi_apply i)

theorem step_none {ι X : Type*} [Zero X]
    (ξ : Step ι X) (i : ι) (h : ξ i = none) :
    step ξ i = 0 := by
  simp [step, h]

theorem step_some {ι X : Type*} [Zero X]
    (ξ : Step ι X) (i : ι) (x : X) (h : ξ i = some x) :
    step ξ i = x := by
  simp [step, h]

theorem step_mono_of_present
    {X : Type*} [Zero X] [Preorder X]
    (ξ : Step ℕ X) (hordered : prefixOrdered ξ)
    {i j : ℕ} (hij : i ≤ j)
    (hi : present ξ i) (hj : present ξ j) :
    step ξ i ≤ step ξ j := by
  rcases hi with ⟨x, hx⟩
  rcases hj with ⟨y, hy⟩
  by_cases heq : i = j
  · subst j
    exact le_rfl
  · have hlt : i < j := lt_of_le_of_ne hij heq
    rw [step_some ξ i x hx, step_some ξ j y hy]
    exact hordered i j x y hlt hx hy

end BranchingStep
