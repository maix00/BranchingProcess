import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Target.LowerBound

/-!
# Central terminal targets

For intervals whose Dirichlet width is a multiple of eight, an explicit
arithmetic progression gives a positive-density set of central, reachable
terminal sites.  These are the targets used in the core-to-core estimate.
-/

open scoped BigOperators
open Filter Topology

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- A central starting site in an interval with Dirichlet width `8 * m`. -/
def centralIntervalStart (m : ℕ) (hm : 0 < m) : Fin (8 * m - 1) :=
  ⟨4 * m - 1, by omega⟩

/-- A central terminal target with exactly the parity reachable from `start`
after `n` steps. Its spatial support is independent of the starting site. -/
def centralParityTarget (m n : ℕ) (hm : 0 < m)
    (start : Fin (8 * m - 1)) :
    Finset (Fin (8 * m - 1)) :=
  let base := 2 * m - 1
  let offset := if Even (n + start.val + base) then 0 else 1
  Finset.univ.image fun j : Fin (2 * m) =>
    (⟨base + offset + 2 * j.val, by
      have hj := j.isLt
      have hoff : offset ≤ 1 := by dsimp [offset]; split <;> omega
      omega⟩ : Fin (8 * m - 1))

/-- The central target has the expected linear cardinality. -/
theorem centralParityTarget_card (m n : ℕ) (hm : 0 < m)
    (start : Fin (8 * m - 1)) :
    (centralParityTarget m n hm start).card = 2 * m := by
  classical
  unfold centralParityTarget
  rw [Finset.card_image_of_injOn]
  · simp
  · intro i _ j _ hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp at hval
    omega

/-- Sine on the middle half of the Dirichlet interval is bounded below by
the value at a quarter turn. -/
theorem sqrt_two_div_two_le_sin_of_mem_middle_thirds {x : ℝ}
    (hx₁ : Real.pi / 4 ≤ x) (hx₂ : x ≤ 3 * Real.pi / 4) :
    Real.sqrt 2 / 2 ≤ Real.sin x := by
  rcases le_total x (Real.pi / 2) with hx | hx
  · rw [← Real.sin_pi_div_four]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hx hx₁
  · calc
      Real.sqrt 2 / 2 = Real.sin (Real.pi / 4) := Real.sin_pi_div_four.symm
      _ ≤ Real.sin (Real.pi - x) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos]) (by linarith) (by linarith)
      _ = Real.sin x := Real.sin_pi_sub x

/-- A starting site belongs to the central core when its physical lattice
coordinate lies between one quarter and three quarters of the interval. -/
def IsCentralCoreStart (m : ℕ) (start : Fin (8 * m - 1)) : Prop :=
  2 * m ≤ start.val + 1 ∧ start.val + 1 ≤ 6 * m

/-- Every central-core starting site has a uniformly positive ground-state
weight. -/
theorem sqrt_two_div_two_le_intervalSineWeight_of_isCentralCoreStart
    (m : ℕ) (hm : 0 < m) (start : Fin (8 * m - 1))
    (hcore : IsCentralCoreStart m start) :
    Real.sqrt 2 / 2 ≤ intervalSineWeight (8 * m - 1) start := by
  rw [intervalSineWeight, dirichletSine]
  have hwidth : ((8 * m - 1 + 1 : ℕ) : ℝ) = 8 * (m : ℝ) := by
    have hNat : 8 * m - 1 + 1 = 8 * m := by omega
    exact_mod_cast hNat
  have hlow : (Real.pi / 4) ≤
      (Real.pi / (8 * (m : ℝ))) * ((start.val + 1 : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))).2
    have hlowCast : (2 * m : ℕ) ≤ start.val + 1 := hcore.1
    have hmul := mul_le_mul_of_nonneg_left
      (show (2 * (m : ℝ)) ≤ ((start.val + 1 : ℕ) : ℝ) by exact_mod_cast hlowCast)
      Real.pi_pos.le
    nlinarith [hmul]
  have hupp :
      (Real.pi / (8 * (m : ℝ))) * ((start.val + 1 : ℕ) : ℝ) ≤
        3 * Real.pi / 4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))).2
    have huppCast : ((start.val + 1 : ℕ) : ℝ) ≤ 6 * (m : ℝ) := by
      exact_mod_cast hcore.2
    have hmul := mul_le_mul_of_nonneg_left huppCast Real.pi_pos.le
    nlinarith [hmul]
  rw [hwidth]
  exact sqrt_two_div_two_le_sin_of_mem_middle_thirds hlow hupp

/-- Every site in the central target has ground-state weight at least
`√2 / 2`, including after the parity filter. -/
theorem sqrt_two_div_two_le_intervalSineWeight_of_mem_centralParityTarget
    (m n : ℕ) (hm : 0 < m)
    (start : Fin (8 * m - 1))
    (site : Fin (8 * m - 1))
    (hsite : site ∈ intervalParityCompatibleTarget n
      start (centralParityTarget m n hm start)) :
    Real.sqrt 2 / 2 ≤ intervalSineWeight (8 * m - 1) site := by
  classical
  have hsiteTarget : site ∈ centralParityTarget m n hm start :=
    (Finset.mem_filter.mp hsite).1
  unfold centralParityTarget at hsiteTarget
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hsiteTarget
  obtain ⟨j, rfl⟩ := hsiteTarget
  let base := 2 * m - 1
  let offset := if Even (n + start.val + base) then 0 else 1
  have hj := j.isLt
  have hoff : offset ≤ 1 := by dsimp [offset]; split <;> omega
  have hlow : 2 * m ≤ base + offset + 2 * j.val + 1 := by omega
  have hupp : base + offset + 2 * j.val + 1 ≤ 6 * m := by omega
  rw [intervalSineWeight, dirichletSine]
  have hmReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hwidth : ((8 * m - 1 + 1 : ℕ) : ℝ) = 8 * (m : ℝ) := by
    have hNat : 8 * m - 1 + 1 = 8 * m := by omega
    exact_mod_cast hNat
  have hsiteLower : (Real.pi / 4) ≤
      (Real.pi / (8 * (m : ℝ))) *
        ((base + offset + 2 * j.val + 1 : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))).2
    have hlowCast : (2 * m : ℕ) ≤ base + offset + 2 * j.val + 1 := hlow
    have hmul := mul_le_mul_of_nonneg_left
      (show (2 * (m : ℝ)) ≤
        ((base + offset + 2 * j.val + 1 : ℕ) : ℝ) by exact_mod_cast hlowCast)
      Real.pi_pos.le
    nlinarith [hmul]
  have hsiteUpper :
      (Real.pi / (8 * (m : ℝ))) *
          ((base + offset + 2 * j.val + 1 : ℕ) : ℝ) ≤
        3 * Real.pi / 4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))).2
    have huppCast :
        ((base + offset + 2 * j.val + 1 : ℕ) : ℝ) ≤ 6 * (m : ℝ) := by
      exact_mod_cast hupp
    have hmul := mul_le_mul_of_nonneg_left huppCast Real.pi_pos.le
    nlinarith [hmul]
  rw [hwidth]
  exact sqrt_two_div_two_le_sin_of_mem_middle_thirds hsiteLower hsiteUpper

/-- The parity-compatible part of the central target still contains one
quarter of the full Dirichlet width. -/
theorem quarter_mul_dirichletWidth_le_centralParityTarget_card
    (m n : ℕ) (hm : 0 < m) (start : Fin (8 * m - 1)) :
    (1 / 4 : ℝ) * ((8 * m - 1 + 1 : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget n start
        (centralParityTarget m n hm start)).card := by
  classical
  have hfilter : intervalParityCompatibleTarget n start
      (centralParityTarget m n hm start) =
      centralParityTarget m n hm start := by
    ext site
    simp only [intervalParityCompatibleTarget, Finset.mem_filter]
    constructor
    · exact And.left
    · intro hsite
      refine ⟨hsite, ?_⟩
      unfold centralParityTarget at hsite
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hsite
      obtain ⟨j, rfl⟩ := hsite
      let base := 2 * m - 1
      let offset := if Even (n + start.val + base) then 0 else 1
      have hEven : Even (n + start.val + base + offset + 2 * j.val) := by
        by_cases he : Even (n + start.val + base)
        · have hoffzero : offset = 0 := by simp [offset, he]
          rw [hoffzero]
          rcases he with ⟨k, hk⟩
          refine ⟨k + j.val, ?_⟩
          omega
        · have hodd : Odd (n + start.val + (2 * m - 1)) :=
            Nat.not_even_iff_odd.mp he
          have hoffone : offset = 1 := by simp [offset, he]
          rw [hoffone]
          rcases hodd with ⟨k, hk⟩
          refine ⟨k + j.val + 1, ?_⟩
          omega
      simpa [base, offset, Nat.add_assoc] using hEven
  rw [hfilter, centralParityTarget_card m n hm start]
  rw [show ((8 * m - 1 + 1 : ℕ) : ℝ) = 8 * (m : ℝ) by
    have hNat : 8 * m - 1 + 1 = 8 * m := by omega
    exact_mod_cast hNat]
  push_cast
  nlinarith

/-- From any central-core starting site, a parity-compatible central target
has mass at least one quarter of the principal eigenvalue power, once the
paired principal modes dominate the geometric remainder. -/
theorem centralCoreTargetMass_lower
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (start : Fin (8 * m - 1))
    (hcore : IsCentralCoreStart m start)
    (hsmall : Real.cos (Real.pi / (8 * (m : ℝ))) ^ n ≤ 1 / 17) :
    (1 / 4 : ℝ) * Real.cos (Real.pi / (8 * (m : ℝ))) ^ n ≤
      ∑ finish ∈ centralParityTarget m n hm start,
        (intervalKernel (8 * m - 1) ^ n) start finish := by
  have hcount : 1 < 8 * m - 1 := by omega
  have hwidth : ((8 * m - 1 + 1 : ℕ) : ℝ) = 8 * (m : ℝ) := by
    have hNat : 8 * m - 1 + 1 = 8 * m := by omega
    exact_mod_cast hNat
  have hsqrtSq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsqrtProd : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
    nlinarith [hsqrtSq]
  have hprincipalCoefficient :
      4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * (1 / 4) = 1 / 2 := by
    calc
      _ = 4 * ((Real.sqrt 2 / 2) * (Real.sqrt 2 / 2)) * (1 / 4) := by ring
      _ = 4 * (1 / 2) * (1 / 4) := by rw [hsqrtProd]
      _ = 1 / 2 := by norm_num
  have hthreshold :
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * (1 / 4)) /
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * (1 / 4) + 8) =
        1 / 17 := by
    rw [hprincipalCoefficient]
    norm_num
  have hsmall' : Real.cos
      (Real.pi / ((8 * m - 1 + 1 : ℕ) : ℝ)) ^ n ≤
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * (1 / 4)) /
          (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * (1 / 4) + 8) := by
    rw [hwidth, hthreshold]
    exact hsmall
  have hstart := sqrt_two_div_two_le_intervalSineWeight_of_isCentralCoreStart
    m hm start hcore
  have htarget : ∀ finish ∈ intervalParityCompatibleTarget n start
      (centralParityTarget m n hm start),
      Real.sqrt 2 / 2 ≤ intervalSineWeight (8 * m - 1) finish := by
    intro finish hfinish
    exact sqrt_two_div_two_le_intervalSineWeight_of_mem_centralParityTarget
      m n hm start finish hfinish
  have hcard := quarter_mul_dirichletWidth_le_centralParityTarget_card
    m n hm start
  have hmass := half_principalScale_le_targetMass hcount hn
    (centralParityTarget m n hm start) start
    (startWeight := Real.sqrt 2 / 2)
    (targetWeight := Real.sqrt 2 / 2) (proportion := 1 / 4)
    (by positivity) (by positivity) (by norm_num)
    hstart htarget hcard hsmall'
  have hcoef : 2 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * (1 / 4) =
      (1 / 4 : ℝ) := by
    calc
      _ = 2 * ((Real.sqrt 2 / 2) * (Real.sqrt 2 / 2)) * (1 / 4) := by ring
      _ = 2 * (1 / 2) * (1 / 4) := by rw [hsqrtProd]
      _ = 1 / 4 := by norm_num
  rw [hwidth] at hmass
  rw [hcoef] at hmass
  exact hmass

/-- Uniform core-to-core block lower bound in the diffusive regime.  The
interval width is `8 * scale n`; the spectral limit is therefore the sharp
Brownian exponent `-π² c / 2`, uniformly over any sequence of central-core
starting sites. -/
theorem eventually_lowerBound_le_centralCoreTargetMass
    (scale time : ℕ → ℕ) (start : ∀ n, Fin (8 * scale n - 1))
    {c lowerBound : ℝ}
    (hscale : ∀ n, 0 < scale n) (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((8 * scale n : ℕ) : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) / ((8 * scale n : ℕ) : ℝ) ^ 2)
      atTop (nhds c))
    (hcore : ∀ n, IsCentralCoreStart (scale n) (start n))
    (hsmallLimit : Real.exp (c * (-(Real.pi ^ 2) / 2)) < 1 / 17)
    (hlowerBound : lowerBound <
      (1 / 4 : ℝ) * Real.exp (c * (-(Real.pi ^ 2) / 2))) :
    ∀ᶠ n in atTop, lowerBound ≤
      ∑ finish ∈ centralParityTarget (scale n) (time n) (hscale n) (start n),
        (intervalKernel (8 * scale n - 1) ^ time n) (start n) finish := by
  let radius : ℕ → ℕ := fun n => 4 * scale n - 1
  have hradius : ∀ n, 0 < radius n := by
    intro n
    have hm := hscale n
    dsimp [radius]
    omega
  have hwidthEqNat (n : ℕ) : 2 * (radius n + 1) = 8 * scale n := by
    have hm := hscale n
    dsimp [radius]
    omega
  have hwidthRadius : Tendsto
      (fun n => ((2 * (radius n + 1) : ℕ) : ℝ)) atTop atTop := by
    refine hwidth.congr' ?_
    filter_upwards with n
    exact_mod_cast (hwidthEqNat n).symm
  have hratioRadius : Tendsto
      (fun n => (time n : ℝ) / ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2)
      atTop (nhds c) := by
    refine hratio.congr' ?_
    filter_upwards with n
    rw [show ((2 * (radius n + 1) : ℕ) : ℝ) =
      ((8 * scale n : ℕ) : ℝ) by exact_mod_cast hwidthEqNat n]
  let qpow : ℕ → ℝ := fun n =>
    Real.cos (Real.pi / ((2 * (radius n + 1) : ℕ) : ℝ)) ^ time n
  have hpower : Tendsto qpow atTop
      (nhds (Real.exp (c * (-(Real.pi ^ 2) / 2)))) := by
    simpa [qpow] using tendsto_centeredPrincipalPower_of_diffusiveRatio
      radius time c hradius hwidthRadius hratioRadius
  have hsmallEventually : ∀ᶠ n in atTop, qpow n ≤ 1 / 17 := by
    have hlt : ∀ᶠ n in atTop, qpow n < 1 / 17 :=
      hpower.eventually (eventually_lt_nhds hsmallLimit)
    exact hlt.mono fun _ h => h.le
  have hprincipalLowerEventually : ∀ᶠ n in atTop,
      lowerBound < (1 / 4 : ℝ) * qpow n := by
    have hscaled : Tendsto (fun n => (1 / 4 : ℝ) * qpow n) atTop
        (nhds ((1 / 4 : ℝ) * Real.exp (c * (-(Real.pi ^ 2) / 2)))) :=
      tendsto_const_nhds.mul hpower
    exact hscaled.eventually (eventually_gt_nhds hlowerBound)
  filter_upwards [hsmallEventually, hprincipalLowerEventually] with n hsmallN hlowerN
  have hsmallCentral : Real.cos (Real.pi / (8 * (scale n : ℝ))) ^ time n ≤
      1 / 17 := by
    have harg : (8 * (scale n : ℝ)) =
        ((2 * (radius n + 1) : ℕ) : ℝ) := by
      exact_mod_cast (hwidthEqNat n).symm
    rw [harg]
    exact hsmallN
  have hblock := centralCoreTargetMass_lower (scale n) (time n)
    (hscale n) (htime n) (start n) (hcore n) hsmallCentral
  have hprincipalLower : lowerBound ≤ (1 / 4 : ℝ) *
      Real.cos (Real.pi / (8 * (scale n : ℝ))) ^ time n := by
    have harg : (8 * (scale n : ℝ)) =
        ((2 * (radius n + 1) : ℕ) : ℝ) := by
      exact_mod_cast (hwidthEqNat n).symm
    have hqeq : qpow n =
        Real.cos (Real.pi / (8 * (scale n : ℝ))) ^ time n := by
      dsimp [qpow]
      rw [harg]
    rw [← hqeq]
    exact hlowerN.le
  exact hprincipalLower.trans hblock

/-- The central site has ground-state weight one. -/
theorem centralIntervalStart_weight (m : ℕ) (hm : 0 < m) :
    intervalSineWeight (8 * m - 1) (centralIntervalStart m hm) = 1 := by
  simp only [centralIntervalStart, intervalSineWeight, dirichletSine]
  have hwidthNat : 8 * m - 1 + 1 = 8 * m := by omega
  have hsiteNat : 4 * m - 1 + 1 = 4 * m := by omega
  rw [show ((8 * m - 1 + 1 : ℕ) : ℝ) = 8 * (m : ℝ) by exact_mod_cast hwidthNat,
    show ((4 * m - 1 + 1 : ℕ) : ℝ) = 4 * (m : ℝ) by exact_mod_cast hsiteNat]
  have hmNe : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have harg : (Real.pi / (8 * (m : ℝ))) * (4 * (m : ℝ)) = Real.pi / 2 := by
    field_simp [hmNe]
    norm_num
  rw [harg, Real.sin_pi_div_two]

end ProbabilityTheory.RandomWalk.Mogulskii
