module

public import Probability.Kernel.Survival
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Kernels returning to a measurable subset

One step of `returnKernel` runs a prescribed number of steps of an ambient
kernel and retains only endpoints in a measurable return set.  Its iterates
therefore describe paths that return to that set after every block.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- Run `K` for `length` steps and retain only endpoints in `returnSet`.
The resulting kernel has `returnSet` as both source and target state space. -/
noncomputable def returnKernel (K : Kernel S S)
    (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (length : ℕ) : Kernel returnSet returnSet :=
  ((K ^ length).comap Subtype.val measurable_subtype_coe).comapRight
    (MeasurableEmbedding.subtype_coe hreturn)

noncomputable instance returnKernel.instIsSubMarkovKernel
    (K : Kernel S S) [IsSubMarkovKernel K]
    (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (length : ℕ) :
    IsSubMarkovKernel (returnKernel K returnSet hreturn length) := by
  unfold returnKernel
  infer_instance

/-- Evaluation of a return kernel is ambient block transition mass restricted
to the image of the requested subset. -/
theorem returnKernel_apply
    (K : Kernel S S) (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (length : ℕ) (x : returnSet) (target : Set returnSet)
    (htarget : MeasurableSet target) :
    returnKernel K returnSet hreturn length x target =
      (K ^ length) (x : S) (Subtype.val '' target) := by
  rw [returnKernel, Kernel.comapRight_apply' _
    (MeasurableEmbedding.subtype_coe hreturn) x htarget,
    Kernel.comap_apply']

/-- The total mass of one return block is the ambient block transition mass
of the return set. -/
theorem returnKernel_apply_univ
    (K : Kernel S S) (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (length : ℕ) (x : returnSet) :
    returnKernel K returnSet hreturn length x univ =
      (K ^ length) (x : S) returnSet := by
  rw [returnKernel_apply K returnSet hreturn length x univ MeasurableSet.univ]
  simp

/-- A return block may be assembled from two stages: first enter a measurable
core set, then reach the return set with a uniform lower bound from every
point of that core.  Requiring the starting point to lie in the return set
makes the resulting two-stage estimate iterable by `returnKernel`.

This statement permits the core to be strictly smaller than the return set.
That distinction is needed when a sharp long-block estimate is uniform only
away from the killing boundary. -/
theorem mul_le_returnKernel_apply_univ_of_entrance
    (K : Kernel S S) (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (core : Set S) (hcore : MeasurableSet core)
    (entranceLength mainLength : ℕ)
    (entranceLower mainLower : ENNReal)
    (hentrance : ∀ start : returnSet,
      entranceLower ≤ (K ^ entranceLength) (start : S) core)
    (hmain : ∀ state ∈ core,
      mainLower ≤ (K ^ mainLength) state returnSet) :
    ∀ start : returnSet,
      mainLower * entranceLower ≤
        returnKernel K returnSet hreturn (entranceLength + mainLength)
          start univ := by
  intro start
  rw [returnKernel_apply_univ]
  calc
    mainLower * entranceLower ≤
        mainLower * (K ^ entranceLength) (start : S) core :=
      mul_le_mul le_rfl (hentrance start) bot_le bot_le
    _ ≤ (K ^ (entranceLength + mainLength)) (start : S) returnSet :=
      mul_pow_apply_le_pow_add_apply_of_mem K entranceLength mainLength
        (start : S) core returnSet hcore hreturn mainLower hmain

/-- After every iterated return block, the embedded endpoint measure is
dominated by the ambient kernel run for the corresponding total time. -/
theorem pow_apply_preimage_le
    (K : Kernel S S) [IsSubMarkovKernel K]
    (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (length : ℕ) :
    ∀ blocks (x : returnSet) (target : Set S), MeasurableSet target →
      (returnKernel K returnSet hreturn length ^ blocks) x
          (Subtype.val ⁻¹' target) ≤
        (K ^ (blocks * length)) (x : S) target := by
  intro blocks
  induction blocks with
  | zero =>
      intro x target htarget
      simp only [pow_zero, Nat.zero_mul]
      change Kernel.id x (Subtype.val ⁻¹' target) ≤ Kernel.id (x : S) target
      rw [Kernel.id_apply, Kernel.id_apply,
        Measure.dirac_apply' _ (htarget.preimage measurable_subtype_coe),
        Measure.dirac_apply' _ htarget]
      rfl
  | succ blocks ih =>
      intro x target htarget
      have hpreimage : MeasurableSet
          ((fun y : returnSet => (y : S)) ⁻¹' target) :=
        htarget.preimage measurable_subtype_coe
      rw [Kernel.pow_succ_apply_eq_lintegral _ blocks x hpreimage]
      calc
        (∫⁻ y, returnKernel K returnSet hreturn length y
              (Subtype.val ⁻¹' target)
            ∂(returnKernel K returnSet hreturn length ^ blocks) x) ≤
            ∫⁻ y, (K ^ length) (y : S) target
              ∂(returnKernel K returnSet hreturn length ^ blocks) x := by
          apply lintegral_mono
          intro y
          change returnKernel K returnSet hreturn length y
              ((fun z : returnSet => (z : S)) ⁻¹' target) ≤
            (K ^ length) (y : S) target
          rw [returnKernel_apply _ _ _ _ _ _ hpreimage]
          exact measure_mono (by
            rintro z ⟨w, hw, rfl⟩
            exact hw)
        _ = ∫⁻ z, (K ^ length) z target ∂Measure.map Subtype.val
              ((returnKernel K returnSet hreturn length ^ blocks) x) := by
          rw [MeasureTheory.lintegral_map
            (Kernel.measurable_coe (K ^ length) htarget)
            measurable_subtype_coe]
        _ ≤ ∫⁻ z, (K ^ length) z target
              ∂(K ^ (blocks * length)) (x : S) := by
          apply lintegral_mono'
          · apply Measure.le_iff.2
            intro measurableTarget hmeasurableTarget
            rw [Measure.map_apply measurable_subtype_coe hmeasurableTarget]
            exact ih x measurableTarget hmeasurableTarget
          · exact le_rfl
        _ = (K ^ (blocks * length + length)) (x : S) target := by
          symm
          exact Kernel.pow_add_apply_eq_lintegral
            K (blocks * length) length (x : S) htarget
        _ = (K ^ ((blocks + 1) * length)) (x : S) target := by
          simp [Nat.add_mul]

/-- Requiring a return after every block can only decrease the probability
of surviving the ambient kernel for the same total elapsed time. -/
theorem remainingMass_returnKernel_le
    (K : Kernel S S) [IsSubMarkovKernel K]
    (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (length blocks : ℕ) (x : returnSet) :
    remainingMass (returnKernel K returnSet hreturn length) blocks x ≤
      remainingMass K (blocks * length) (x : S) := by
  unfold remainingMass
  simpa using pow_apply_preimage_le K returnSet hreturn length blocks x univ
    MeasurableSet.univ

/-- A uniform one-block return bound controls ambient survival at an arbitrary
elapsed time.  One additional return block covers the incomplete final part. -/
theorem pow_succ_div_le_remainingMass_of_returnKernel
    (K : Kernel S S) [IsSubMarkovKernel K]
    (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    {length : ℕ} (hlength : 0 < length) (total : ℕ)
    (x : returnSet) (lowerBound : ENNReal)
    (hblock : ∀ state : returnSet,
      lowerBound ≤ returnKernel K returnSet hreturn length state univ) :
    lowerBound ^ (total / length + 1) ≤ remainingMass K total (x : S) := by
  let blocks := total / length + 1
  have hreturnBlocks : lowerBound ^ blocks ≤
      remainingMass (returnKernel K returnSet hreturn length) blocks x := by
    have hrow : ∀ state : returnSet, lowerBound ≤
        remainingMass (returnKernel K returnSet hreturn length) 1 state := by
      intro state
      simpa [remainingMass] using hblock state
    simpa [blocks] using pow_le_remainingMass_mul
      (returnKernel K returnSet hreturn length) 1 blocks x lowerBound hrow
  have hambient := hreturnBlocks.trans
    (remainingMass_returnKernel_le K returnSet hreturn length blocks x)
  exact hambient.trans
    (antitone_remainingMass K (x : S) (by
      dsimp [blocks]
      simpa [mul_comm] using (Nat.lt_mul_div_succ total hlength).le))

/-- Logarithmic form of the arbitrary-time return-block lower bound.  It is
valid without separately excluding zero probabilities because `ENNReal.log`
takes values in `EReal`. -/
theorem natCast_mul_log_le_log_remainingMass_of_returnKernel
    (K : Kernel S S) [IsSubMarkovKernel K]
    (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    {length : ℕ} (hlength : 0 < length) (total : ℕ)
    (x : returnSet) (lowerBound : ENNReal)
    (hblock : ∀ state : returnSet,
      lowerBound ≤ returnKernel K returnSet hreturn length state univ) :
    ((total / length + 1 : ℕ) : EReal) * ENNReal.log lowerBound ≤
      ENNReal.log (remainingMass K total (x : S)) := by
  rw [← ENNReal.log_pow]
  exact ENNReal.log_monotone
    (pow_succ_div_le_remainingMass_of_returnKernel
      K returnSet hreturn hlength total x lowerBound hblock)

end ProbabilityTheory.Kernel

end
