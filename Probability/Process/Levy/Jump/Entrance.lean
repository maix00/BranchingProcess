module

public import Probability.Process.Levy.Jump.OneJump
public import Topology.Cadlag.Skorokhod.Corridor.OneJump
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Entrance by one finite-activity jump

The theorem combines a Poisson count, a jump mark and an independent
finite-variation residual path. It makes no stable-law claim: an application
to a stable Lévy process must still identify its law with such a jump-sum
model.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem measure_oneJumpEntrance_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X S : unitInterval → Ω → ℝ)
    (jumpTime : Ω → unitInterval) (N : Ω → ℕ)
    (W : Ω → ℝ) (V : Ω → ENNReal)
    (rate : ℝ≥0) (ν : Measure ℝ)
    (lower upper target ρ ε margin : ℝ)
    (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hrate : 0 < rate)
    (hν : 0 < ν (Set.Ioo (target - ρ) (target + ρ)))
    (hN : HasLaw N (poissonMeasure rate) P)
    (hW : HasLaw W ν P)
    (hNW : IndepFun N W P)
    (hVNW : IndepFun V (fun ω => (N ω, W ω)) P)
    (hV : Measurable V)
    (hE : (∫⁻ ω, V ω ∂P) < ENNReal.ofReal ρ)
    (hsmall : ∀ ω, V ω < ENNReal.ofReal ρ →
      ∀ t, |S t ω| ≤ ρ)
    (hdecomp : ∀ ω, V ω < ENNReal.ofReal ρ → N ω = 1 →
      ∀ t, X t ω = S t ω +
        (if jumpTime ω ≤ t then W ω else 0)) :
    0 < P {ω | (∀ t, lower + (margin - 2 * ρ) ≤ X t ω ∧
      X t ω ≤ upper - (margin - 2 * ρ)) ∧
      target - ε < X ⊤ ω ∧ X ⊤ ω < target + ε} := by
  let J := Set.Ioo (target - ρ) (target + ρ)
  let good : Set Ω :=
    {ω | V ω < ENNReal.ofReal ρ ∧ N ω = 1 ∧ W ω ∈ J}
  have hgood : 0 < P good :=
    measure_oneMarkedJump_and_smallVariation_pos P N W V rate ν J
      (ENNReal.ofReal ρ) hrate hν measurableSet_Ioo hN hW hNW hVNW hV hE
  apply hgood.trans_le
  apply measure_mono
  intro ω hω
  obtain ⟨hvariation, hcount, hmark⟩ := hω
  have hwindow : |W ω - target| < ρ := by
    have hw : target - ρ < W ω ∧ W ω < target + ρ := hmark
    rw [abs_lt]
    constructor <;> linarith
  have hpath := oneJump_staysInInterval_and_endsNear
    (fun t => S t ω) (jumpTime ω) (W ω) lower upper target ρ ε margin
    hε hl0 hu0 hly huy (hsmall ω hvariation) hwindow
  constructor
  · intro t
    rw [hdecomp ω hvariation hcount t]
    exact hpath.1 t
  · rw [hdecomp ω hvariation hcount ⊤]
    simpa using hpath.2

/-- The parameters of Mogulskii's fixed entrance event. The probabilistic
inputs describe a one-jump decomposition with a target mark window chosen
after `b`, `c`, and `ε`; no path-support statement is assumed. -/
theorem measure_oneJumpSourceEntrance_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X S : unitInterval → Ω → ℝ)
    (jumpTime : Ω → unitInterval) (N : Ω → ℕ)
    (W : Ω → ℝ) (V : Ω → ENNReal)
    (rate : ℝ≥0) (ν : Measure ℝ)
    (b c ε ρ : ℝ) (hρ : 0 < ρ)
    (hroomBLower : 4 * ρ < 1 + b)
    (hroomBUpper : 4 * ρ < 1 - b)
    (hroomCLower : 4 * ρ < 1 + c)
    (hroomCUpper : 4 * ρ < 1 - c)
    (hroomEndpoint : 4 * ρ < ε)
    (hrate : 0 < rate)
    (hν : 0 < ν (Set.Ioo (c - b - ρ) (c - b + ρ)))
    (hN : HasLaw N (poissonMeasure rate) P)
    (hW : HasLaw W ν P)
    (hNW : IndepFun N W P)
    (hVNW : IndepFun V (fun ω => (N ω, W ω)) P)
    (hV : Measurable V)
    (hE : (∫⁻ ω, V ω ∂P) < ENNReal.ofReal ρ)
    (hsmall : ∀ ω, V ω < ENNReal.ofReal ρ →
      ∀ t, |S t ω| ≤ ρ)
    (hdecomp : ∀ ω, V ω < ENNReal.ofReal ρ → N ω = 1 →
      ∀ t, X t ω = S t ω +
        (if jumpTime ω ≤ t then W ω else 0)) :
    0 < P {ω | (∃ δ > 0, ∀ t,
        c - 1 + δ ≤ X t ω ∧ X t ω ≤ c + 1 - δ) ∧
      c - b - ε < X ⊤ ω ∧ X ⊤ ω ≤ c - b + ε} := by
  have hmain := measure_oneJumpEntrance_pos P X S jumpTime N W V rate ν
    (c - 1) (c + 1) (c - b) ρ ε (3 * ρ)
    (by linarith [hroomEndpoint, hρ])
    (by linarith [hroomCUpper]) (by linarith [hroomCLower])
    (by linarith [hroomBUpper]) (by linarith [hroomBLower])
    hrate hν hN hW hNW hVNW hV hE hsmall hdecomp
  apply hmain.trans_le
  apply measure_mono
  rintro ω ⟨hcorridor, hlo, hhi⟩
  refine ⟨⟨ρ, hρ, ?_⟩, hlo, hhi.le⟩
  intro t
  simpa only [show 3 * ρ - 2 * ρ = ρ by ring] using hcorridor t

end ProbabilityTheory

end
