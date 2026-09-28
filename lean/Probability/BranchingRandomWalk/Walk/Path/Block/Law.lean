import Probability.BranchingRandomWalk.Walk.Path.Block.Basic
import Probability.Sequence.IID
import Mathlib.Probability.Independence.Basic

/-!
# Laws and independence of increment blocks

Probability statements for consecutive blocks under the canonical i.i.d.
increment law.
-/

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]

/-- Every deterministic shift of a block sum has the same law as the
corresponding initial partial sum. -/
theorem iidSequenceLaw_map_blockSum (ν : Measure E) [IsProbabilityMeasure ν]
    (start length : ℕ) :
    (iidSequenceLaw ν).map (blockSum start length) =
      (iidSequenceLaw ν).map (partialSum length) := by
  rw [show blockSum (E := E) start length =
      partialSum length ∘ fun increment => fun k => increment (start + k) by
    funext increment
    exact blockSum_eq_partialSum_natAdd start length increment]
  rw [← Measure.map_map (partialSum_measurable length) (measurable_natAdd start)]
  rw [iidSequenceLaw_map_natAdd]

/-- Sums over two consecutive deterministic blocks of an i.i.d. increment
path are independent. -/
theorem indepFun_blockSum_blockSum (ν : Measure E) [IsProbabilityMeasure ν]
    (start m n : ℕ) :
    IndepFun (blockSum (E := E) start m)
      (blockSum (start + m) n) (iidSequenceLaw ν) := by
  let S := Finset.Ico start (start + m)
  let T := Finset.Ico (start + m) (start + m + n)
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_Ico] at hkS hkT
    omega
  have htuple := (iidSequenceLaw_independent ν).indepFun_finset S T hdisjoint
    (fun k => measurable_pi_apply k)
  have hsumS : Measurable (fun x : S → E => ∑ k : S, x k) := by
    exact Finset.measurable_sum Finset.univ
      (fun k _ => measurable_pi_apply k)
  have hsumT : Measurable (fun x : T → E => ∑ k : T, x k) := by
    exact Finset.measurable_sum Finset.univ
      (fun k _ => measurable_pi_apply k)
  have h := htuple.comp hsumS hsumT
  have hleft : (fun x : ℕ → E => ∑ k : S, x k) = blockSum start m := by
    funext x
    simpa [S, blockSum] using
      (Finset.sum_attach (Finset.Ico start (start + m)) x)
  have hright : (fun x : ℕ → E => ∑ k : T, x k) =
      blockSum (start + m) n := by
    funext x
    simpa [T, blockSum, Nat.add_assoc] using
      (Finset.sum_attach (Finset.Ico (start + m) (start + m + n)) x)
  simpa only [Function.comp_def, hleft, hright] using h

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
