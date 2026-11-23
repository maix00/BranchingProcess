/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.LocalBias.Weight
public import Probability.BranchingProcess.Spine.LocalBias.Ray
import all Probability.BranchingProcess.Spine.LocalBias.Lemmas.Induction

/-!
# Finite-history densities for arbitrary locally biased offspring

## Public declarations

* `ProbabilityTheory.BranchingProcess.Spine.LocalBias.lintegral_treeKernel_fixedAddress`
  proves `E_bias[1_{w_n=z} g(erase(H_n))] = E_Q[R_z(H_n) g(H_n)]` for
  every nonnegative measurable finite-history payoff. The only bias
  hypotheses are measurable local densities, normalization, and eligible
  selected-child support (`LocalBias.IsAdmissible`).

The proof follows the fixed-address induction of Zhan Shi,
*Branching Random Walks* (2015), Theorem 4.3, (4.12)–(4.13),
DOI 10.1007/978-3-319-25372-5, using a general family-dependent local factor.
This is the unique probabilistic density induction; harmonic formulas
specialize it rather than repeat it.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias
open MeasureTheory Combinatorics.Branching Finset Preorder
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

private lemma treeKernel_history {S ι : Type*} [MeasurableSpace S]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q] (s : Option S) (n : ℕ) :
    (State.treeKernel Q s).map (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) =>
      t (List.ofFn p.2)) =
    Kernel.partialTraj (X := fun k => (Unit × (Fin k → ι)) → Option S)
      (State.generationHistoryKernel Q) 0 n (fun _ _ => s) := by
  change (State.treeKernel Q s).map ((frestrictLe n) ∘
    (fun t k (p : Unit × (Fin k → ι)) => t (List.ofFn p.2))) = _
  have hπ : Measurable (fun t : List ι → Option S =>
      fun k : ℕ => fun p : Unit × (Fin k → ι) => t (List.ofFn p.2)) := by fun_prop
  have hm := Measure.map_map (measurable_frestrictLe n) hπ (μ := State.treeKernel Q s)
  rw [State.treeKernel_generations] at hm
  exact hm.symm.trans (Kernel.traj_map_frestrictLe_apply 0 n _)

/-- Shi (4.12)–(4.13): the fixed-address identity at arbitrary depth,
for arbitrary nonnegative measurable observations through that generation. -/
theorem lintegral_treeKernel_fixedAddress {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (s : B.domain) (n : ℕ) (z : Fin n → ι)
    {g : (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ t, if (t (List.ofFn z)).any Sum.isRight = true then
      g (fun _k p => (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) else 0
      ∂treeKernel Q B hB (some (Sum.inr s))) =
    ∫⁻ t, addressWeight B n z (fun _k p => t (List.ofFn p.2)) *
      g (fun _k p => t (List.ofFn p.2)) ∂State.treeKernel Q (some s.1) := by
  let := reproductionKernel_isMarkovKernel Q B hB
  let E := S ⊕ B.domain
  have he : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option E =>
      fun k q => (x k q).map (Sum.elim id Subtype.val)) := by
    have hm : Measurable (fun o : Option E => o.map (Sum.elim id Subtype.val)) :=
      measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
    fun_prop
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false (measurable_const.sumElim measurable_const)
  have hG : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option E =>
      if (x ⟨n, by simp⟩ ((), z)).any Sum.isRight = true then
        g (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0) :=
    (hg.comp he).ite ((MeasurableSet.singleton true).preimage
      (htag.comp ((measurable_pi_apply _).comp (measurable_pi_apply _)))) measurable_const
  have hW : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option S => addressWeight B n z x * g x) :=
    (measurable_addressWeight B hB.measurableSet_domain hB.measurable_density n z).mul hg
  have hleft := lintegral_map hG (show Measurable
    (fun t : List ι → Option E => fun k : Iic n =>
      fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) from by fun_prop)
    (μ := State.treeKernel (reproductionKernel Q B) (some (Sum.inr s)))
  rw [treeKernel_history] at hleft
  have hright := lintegral_map hW (show Measurable
    (fun t : List ι → Option S => fun k : Iic n =>
      fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) from by fun_prop)
    (μ := State.treeKernel Q (some s.1))
  rw [treeKernel_history] at hright
  exact hleft.symm.trans ((lintegral_partialTraj_fixedAddress Q B hB s n z hg).trans hright)


end ProbabilityTheory.BranchingProcess.Spine.LocalBias

end
