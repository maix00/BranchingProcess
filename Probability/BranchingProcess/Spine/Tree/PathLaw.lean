/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Observation
public import Probability.BranchingProcess.Spine.StateChain
public import Probability.Process.Markov.Trajectory
public import Probability.Kernel.IonescuTulcea.Map
import all Probability.BranchingProcess.Spine.Tree.Lemmas.Generation

/-!
# The complete state-path law of the realized spine

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `ae_treeKernel_statePath`: almost surely, the existing unique distinguished
  ray `ξ` satisfies `t(ξₙ) = some(inr(statePath d t n))` at every depth.
* `treeKernel_statePath`: for any eligible initial state `s` and any
  eligible default `d`, the observed complete path has the canonical Doob
  Markov law `Law_h(s)`: `P_tree(s).map (statePath d) = Law_h(s)`.
* `statePath_isMarkovChain`: this observed path law is Markov under its
  coordinate filtration, with transitions `(Kʰ|E)^(n-m)`.

This proves Zhan Shi, *Branching Random Walks* (2015), Chapter 4, §4.4,
Theorem 4.4(ii), (4.10), DOI 10.1007/978-3-319-25372-5, for arbitrary
measurable states and countable child slots. `h` denotes the full mean-harmonic
reproductive weight. The proof identifies the next observed state through
one-parent reproduction, then invokes the existing general trajectory-law
identification. It uses the same canonical tree and Doob kernel throughout.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris Finset Preorder
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

/-- The observed states are exactly those on the actual unique realized ray. -/
theorem ae_treeKernel_statePath (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (d s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    ∀ᵐ t ∂treeKernel Q hh harmonic (some (Sum.inr s)),
      ∃! f, IsRay (distinguishedNodes t) f ∧
        distinguishedNodes t = Set.range (lineagePrefix f) ∧
        ∀ n, t (lineagePrefix f n) = some (Sum.inr (statePath d t n)) := by
  filter_upwards [ae_treeKernel_unique_spine Q hh harmonic s] with t ht
  obtain ⟨f, ⟨hf, hc⟩, hu⟩ := ht
  exact ⟨f, ⟨hf, hc, statePath_eq_of_isRay d t f hf hc⟩,
    fun g hg => hu g ⟨hg.1, hg.2.1⟩⟩

/-- Reading the realized spine gives the complete canonical Doob-chain path law. -/
theorem treeKernel_statePath (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (d s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    letI := eligibleStateKernel_isMarkovKernel Q hh harmonic
    (treeKernel Q hh harmonic (some (Sum.inr s))).map (statePath d) =
      Kernel.traj (X := fun _ => {s // h s ≠ 0 ∧ h s ≠ ∞})
        (Kernel.historyKernel (eligibleStateKernel Q hh)) 0 (fun _ => s) := by
  let := eligibleStateKernel_isMarkovKernel Q hh harmonic
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  let P := State.pathKernel (reproductionKernel Q h) (some (Sum.inr s))
  have hgood := ae_pathKernel_unique_distinguished Q hh harmonic s
  have hstep : ∀ n, ∀ᵐ history ∂P.map (frestrictLe n),
      (State.generationHistoryKernel (reproductionKernel Q h) n history).map
        (distinguishedState d) =
      Kernel.historyKernel (eligibleStateKernel Q hh) n
        (fun k => distinguishedState d (history k)) := by
    intro n
    have hG : MeasurableSet {history : Π k : Iic n,
        (Unit × (Fin k.1 → ι)) → Option E |
        ∃! p, (history ⟨n, by simp⟩ p).any Sum.isRight = true} :=
      measurableSet_unique_distinguished.preimage (measurable_pi_apply _)
    have hg : ∀ᵐ history ∂P.map (frestrictLe n),
        ∃! p, (history ⟨n, by simp⟩ p).any Sum.isRight = true :=
      (ae_map_iff (measurable_frestrictLe n).aemeasurable hG).mpr
        (hgood.mono fun x hx => hx n)
    filter_upwards [hg] with history ht
    obtain ⟨p, hp, hu⟩ := ht
    obtain ⟨v, hv⟩ : ∃ v, history ⟨n, by simp⟩ p = some (Sum.inr v) := by
      cases he : history ⟨n, by simp⟩ p with
      | none => simp [he] at hp
      | some a => cases a with
        | inl a => simp [he] at hp
        | inr v => exact ⟨v, rfl⟩
    have ho : ∀ q, q ≠ p → (history ⟨n, by simp⟩ q).any Sum.isRight ≠ true :=
      fun q hqp hq => hqp (hu q hq)
    have hread := distinguishedState_eq d (history ⟨n, by simp⟩) p v hv ho
    change (State.generationKernel (reproductionKernel Q h) n
      (history ⟨n, by simp⟩)).map (distinguishedState d) =
        eligibleStateKernel Q hh (distinguishedState d (history ⟨n, by simp⟩))
    rw [hread]
    exact generationKernel_distinguished_state Q hh harmonic d n _ p v hv ho
  have hpath := Kernel.map_eq_trajMeasure
    (X := fun n => (Unit × (Fin n → ι)) → Option E)
    (Y := fun _ => {s // h s ≠ 0 ∧ h s ≠ ∞}) id monotone_id
    (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q h))
    (Kernel.historyKernel (eligibleStateKernel Q hh)) P
    (fun _ => distinguishedState d) (fun _ => measurable_distinguishedState d)
    hstep (fun n => State.pathKernel_oneStep _ _ n)
  have hroot : distinguishedState d
      (fun _ : Unit × (Fin 0 → ι) => (some (Sum.inr s) : Option E)) = s := by
    apply distinguishedState_eq d _ ((), fun i : Fin 0 => i.elim0) s rfl
    intro j hj
    exact False.elim (hj (Subsingleton.elim _ _))
  change P.map (fun x n => distinguishedState d (x n)) =
    Kernel.trajMeasure ((P.map (fun x => x 0)).map (distinguishedState d))
      (Kernel.historyKernel (eligibleStateKernel Q hh)) at hpath
  have hinit := State.pathKernel_initial (reproductionKernel Q h) (some (Sum.inr s))
  rw [hinit, Measure.map_dirac' (measurable_distinguishedState d),
    hroot] at hpath
  have htree := State.treeKernel_generations (reproductionKernel Q h) (some (Sum.inr s))
  have hobs := congrArg (Measure.map (fun x n => distinguishedState d (x n))) htree
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hobs
  change (treeKernel Q hh harmonic (some (Sum.inr s))).map (statePath d) = _ at hobs
  rw [hobs, hpath, Kernel.trajMeasure, Measure.map_dirac' (by fun_prop),
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- The identified path law satisfies the generic Doob-chain Markov property. -/
theorem statePath_isMarkovChain (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (d s : {s // h s ≠ 0 ∧ h s ≠ ∞}) :
    letI := eligibleStateKernel_isMarkovKernel Q hh harmonic
    IsMarkovChain (fun n (x : ℕ → {s // h s ≠ 0 ∧ h s ≠ ∞}) => x n)
      Filtration.piLE ((treeKernel Q hh harmonic (some (Sum.inr s))).map (statePath d))
      (eligibleStateKernel Q hh) := by
  let := eligibleStateKernel_isMarkovKernel Q hh harmonic
  simpa only [← treeKernel_statePath Q hh harmonic d s] using
    isMarkovChain_traj_historyKernel (eligibleStateKernel Q hh) s

end ProbabilityTheory.BranchingProcess.Spine

end
