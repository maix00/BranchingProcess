/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.LocalBias.Basic
public import Probability.BranchingProcess.State.Generation
public import Mathlib.Data.Fin.Tuple.Take

/-!
# Products of local family biases along a fixed address

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine.LocalBias`:

* `stepWeight B o ξ i` reads `r(s,ξ,i)` from an eligible present parent,
  and is zero for absent or ineligible parents; `measurable_stepWeight`
  gives its joint measurability.
* `addressWeight B n z H` is the product of these weights along address `z`,
  with `W₀=1`; `measurable_addressWeight` proves finite-history measurability.

These are the products of local Radon--Nikodym factors in Zhan Shi,
*Branching Random Walks* (2015), Theorem 4.3, (4.12)–(4.13),
DOI 10.1007/978-3-319-25372-5, allowing dependence on the full child family.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias

open MeasureTheory Combinatorics.Branching Finset Preorder
open scoped ENNReal

noncomputable def stepWeight {S ι : Type*} (B : LocalBias S ι)
    (o : Option S) (ξ : Step ι S) (i : ι) : ℝ≥0∞ := by
  classical
  exact o.elim 0 (fun s => if s ∈ B.domain then B.density s ξ i else 0)

@[fun_prop] theorem measurable_stepWeight {S ι : Type*}
    [MeasurableSpace S] (B : LocalBias S ι)
    (hD : MeasurableSet B.domain)
    (hr : ∀ i, Measurable (Function.uncurry (fun s ξ => B.density s ξ i))) (i : ι) :
    Measurable (fun p : Option S × Step ι S => stepWeight B p.1 p.2 i) := by
  classical
  apply Measurable.option_elim measurable_fst measurable_const
  exact ((hr i).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).ite
    (hD.preimage measurable_snd) measurable_const

noncomputable def addressWeight {S ι : Type*} (B : LocalBias S ι) :
    (n : ℕ) → (Fin n → ι) → (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) → ℝ≥0∞
  | 0, _, _ => 1
  | n + 1, z, x =>
    addressWeight B n (Fin.init z) (fun k => x ⟨k.1, mem_Iic.mpr
      ((mem_Iic.mp k.2).trans (Nat.le_succ n))⟩) *
    stepWeight B (x ⟨n, by simp⟩ ((), Fin.init z))
      (fun j => x ⟨n + 1, by simp⟩ ((), Fin.snoc (Fin.init z) j)) (z (Fin.last n))

@[fun_prop] theorem measurable_addressWeight {S ι : Type*} [MeasurableSpace S]
    (B : LocalBias S ι) (hD : MeasurableSet B.domain)
    (hr : ∀ i, Measurable (Function.uncurry (fun s ξ => B.density s ξ i)))
    (n : ℕ) (z : Fin n → ι) : Measurable (addressWeight B n z) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((ih (Fin.init z)).comp (by fun_prop)).mul
      ((measurable_stepWeight B hD hr (z (Fin.last n))).comp
        (show Measurable (fun x : Π k : Iic (n + 1),
            (Unit × (Fin k.1 → ι)) → Option S =>
          (x ⟨n, by simp⟩ ((), Fin.init z),
            fun j => x ⟨n + 1, by simp⟩ ((), Fin.snoc (Fin.init z) j))) from by fun_prop))

end ProbabilityTheory.BranchingProcess.Spine.LocalBias
