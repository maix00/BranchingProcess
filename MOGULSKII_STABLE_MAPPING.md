# Mogulskii (1974) small deviations: the original statements, and where each one lives

Source: А. А. Могульский, *Малые уклонения в пространстве траекторий*, Теория вероятностей и её применения
**XIX**(4), 1974. Local copy at `~/Downloads/Mogulskii_1974_Small_deviations.pdf` (11 pages, 21363 characters of
text layer, extracted to `/tmp/mogul.txt`). The statements below are transcribed from that text; the OCR is
noisy, so formulas are restored to their mathematical reading while the original numbering — (2), (3), (4),
(15), (16), (18)–(20), (30)–(34), (36), (44) — is kept verbatim.

## The original statements

* **(2)** `ξ₁, ξ₂, …` are i.i.d. with increment law `F` and
  `P((ξ₁+…+ξₙ)/B(n) < x) → F_a(x)`, where `F_a` is **strictly stable** and
  **`0 < a ≤ 2`**; for `a = 1` an extra centering is used. In (3), `F` is the
  increment law, while `F_a` is the limiting law.
* **(3)** `L*(u) = u^{a−2} ∫_{−u}^{u} ξ² F(dξ)`, a slowly varying function under the stable-domain assumptions. A finite positive limit is a special case (for example, under a pure power-tail asymptotic); general slow variation does not imply convergence. At `a = 2`, convergence to `E ξ²` requires a finite second moment.
* **(4)** `B*(B(n)) ↝ d·n` with `B*(u) = u^a / L*(u)`; after rescaling,
  `d = 1`. Equivalently `bₙ^a = n·L*(bₙ)·(1 + o(1))`; this does not imply
  `bₙ^a = Θ(n)` unless the slowly varying factor is bounded above and below.
* **(15) Теорема 1.** Let `0 < F_a(0) < 1`. Then for every `{x(n)}` with `x(n) → ∞` and `x(n)·B⁻¹(n) → 0`, and
  every set `G` of paths,
  `ln P(sₙ(·) ∈ G) ~ C · H^a_x(G) · n · x(n)^{-a} · L*(x(n))`,
  with `−∞ < C < 0` depending on `F_a` only (see Лемма 1).
* **(16) Теорема 2.** For `P(ξ(1) < x) = F_a(x)` of a strictly stable process with `0 < F_a(0) < 1`, as
  `a ↓ 0`, `ln P(a⁻¹ ξ(·) ∈ G) ~ C · H^a(G) · a^a` — the stable-process (single-block) statement, with the
  constant `C` of Теорема 1.
* **Лемма 1. I (18)** `a^a ln P(ξ(·) ∈ a𝔘) → C` as `a ↓ 0`, `C ∈ (−∞, 0)`. **II (19)(20)** the tubes
  `a𝔙_b^c` and `a𝔙_b^{d(1)}` are asymptotically equivalent to `a𝔘`.
* **Lemma 2, relations (21)–(25), is proved for the stable-process model** in
  `Probability/Process/Stable/SmallDeviation/{ShiftedCorridor,RangeComparison,Blocks/Upper/ArbitraryHorizon,BlockBounds,EndpointComparison}.lean`.
  The APIs retain the source's endpoint conventions and exponents. **Lemma 3** is the discrete walk version, with **(32)**
  `P(sₙ(·) ∈ 𝔘) ≤ P(sₙ(·) ∈ X(0, c)𝔘)` for `c = m/n`, **(33)**
  `P(sₙ(·) ∈ 𝔘 ∩ ε) ≥ [min_{−3<i<3} P(sₙ(·) ∈ X(0, c)𝔘)]^k` with `k = [c⁻¹] + 1`, and **(34)** the comparison
  `ln P(sₙ(·) ∈ Y_b^c(1) ∩ (+ε)) ≲ ln P(sₙ(·) ∈ 𝔘)`. These discrete estimates remain open. **Лемма 4. I** is (15) at `G = 𝔘`:
  `ln P(sₙ(·) ∈ 𝔘) ~ C · n · x(n)^{-a} · L*(x(n))`.

## What §3 («Доказательство теорем 1 и 2») actually does

Let `G` be a set whose boundary functions `L₁, L₂` have discontinuities at `0 < t₁ < … < 1`. On each interval
`(t_i, t_{i+1})`, `i = 0, …, N` (with `t₀ = 0`, `t_{N+1} = 1`), the set `G` is a **strip with straight
boundaries**: `X(t_i, t_{i+1} − 0)G = X(t_i, t_{i+1} − 0)[a_i, b_i]` with `a_i = L₁`, `b_i = L₂` there. The
upper bound comes from

```
P(sₙ(·) ∈ G) ≤ ∏_{i=0}^{N} P(sₙ(·) ∈ X(t_i, t_{i+1})[c_i]),   c_i = (a_i − b_i)/2,
```

together with Лемма 4, and the lower bound from the same product with a shrink `(1 − δ)` of the strip, together
with Лемма 3. Theorem 2 is proved "in exactly the same way with Лемма 1". Equation **(44)** is the
normalization statement in between: along `x(n) → ∞`, `x(n)B⁻¹(n) → 0` there is `a(n) ↑ ∞` with
`ln P(sₙ(·) ∈ … a(n)^{-1}[B*(x(n))] …) ~ a(n)·C`, and (36) is then obtained from (31)–(34) of Лемма 3.

Two consequences that matter for the formalization:

1. **The blocks are relative sub-intervals of the same `n`-step path**, of relative lengths `t_{i+1} − t_i`
   fixed by the discontinuities of the boundary. The product over blocks is taken over *disjoint step ranges*,
   which is exactly the independence structure the scale-free gluing in
   `Combinatorics/BranchingWalk/Walk/Path/Block/Partition/Basic.lean` formalizes.
2. **The proof partitions the horizon into time intervals with fixed relative lengths.** Those intervals contain order-`n` steps. This does not by itself identify them with the implementation's `stableBlockLength`, which is `⌊c · κν(aₙ)⌋₊` for the corridor scale `aₙ` and `κν(u) = u^α/L*ν(u)`. Showing the needed asymptotic relations for this block length under general slow variation is still open. The source's per-interval costs form the Riemann sum for `∫₀¹ dt/(g − f)^a`; the discrete probability estimates that justify this step remain open.

## Normalisation

```
λ_n := n · L*(x(n)) · x(n)^{-a}          -- the factor in (15) and Лемма 4
```

so that `−(1/λ_n) ln P(sₙ(·) ∈ G) → −C · H^a(G)`, and for a corridor `G = {f : g ≤ f ≤ h}` the functional
`H^a_x(G)` tends to `∫₀¹ dt / (g − f)^a`, the `corridorEnergy` of
`Combinatorics/BranchingWalk/Walk/Path/Corridor.lean`. `λ_n` is available in the library as
`stableRateNormalization α ν scale n`, defined as the reciprocal of `stableSmallDeviationRate` (commit
`7cccf6d4`), so every rate statement has both directions readable at the definition site.

## Where each piece lives

| original | module | state |
| --- | --- | --- |
| (2), (4): domain of attraction, norming | `Distributions/Stable/Attraction.lean`, `Distributions/Stable/Attraction/Norming.lean`, `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Scale.lean` | the input law `ν` and stable limit law `μ` are separate; norming and `L*` use `ν`. `IsStableNorming` states `B*ν(B(n))/n → 1` |
| Fixed block endpoint under a domain-of-attraction limit | `Distributions/DomainOfAttraction/Block.lean`; `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Scale.lean` | a general Slutsky adapter is proved for finite partial sums of increments with law `ν`, with stable limit `μ`; it preserves the centering contribution and states block, norming, and centering limits explicitly. The norming ratio for `m n = ⌊τ κν(aₙ)⌋₊` is only proved under the additional positive finite limit of `L*ν`; the general Potter application and asymptotic-inverse argument remain open |
| Characteristic functions for the attraction hypothesis | `Probability/Sequence/IID/CharacteristicFunction.lean`, `Probability/Distributions/DomainOfAttraction/CharacteristicFunction.lean`, `Probability/Distributions/Stable/CharacteristicFunction.lean`, `Probability/Distributions/Stable/Attraction/CharacteristicFunction.lean`, `Stable/Attraction/NormingRatios/{Index,UniformDefect,RegularVariation}.lean` | the exact finite-i.i.d.-sum formula and centered/scaled characteristic-function limit are proved. For the general affine `IsAlphaStable` predicate, including `α = 1`, the modulus is `exp(-c |t|^α)` with `c > 0`; attraction then gives both `n(-log |φν(t/Bₙ)|) → c|t|^α` and `n(1-|φν(t/Bₙ)|²) → 2c|t|^α` with the same `c` for every frequency. The norming-ratio theorem, compact-uniform squared-modulus defect limit, and continuous-frequency defect regular variation are also proved without monotonicity of the norming. These do not yet imply regular variation of the increment tail |
| Integer block-count arithmetic | `Analysis/Asymptotics/BlockScale.lean`; stable interface in `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Partition.lean` | floor length, quotient count, coverage bounds, and the `o(n)` coverage limit are general deterministic results. The stable file supplies definitions and delegates this arithmetic |
| Discrete block scale relations (Lemma 3/4 input) | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/{Scale,Partition}.lean`; generic ratio laws in `Analysis/Asymptotics/RegularVariation.lean` | the generic ratio-limit definition, product/reciprocal rules, a one-sided Potter bound for eventually nondecreasing functions, and `stableScaleTime_isRegularlyVaryingAtTop` are proved. The inverse-Tauberian chain for `0<α<2` is complete: it transfers regular variation of the characteristic-function defect to regular variation of the original two-sided increment tail. The separate `α=2` normal-attraction result, asymptotic inverse, compatibility with the chosen norming, and discrete corridor probability estimates remain open |
| (3): `L*` | `Distributions/Moments/Truncated.lean`, `Distributions/Stable/Attraction/Norming.lean`, `Analysis/Asymptotics/PowerTailIntegral.lean`, `Analysis/Asymptotics/RegularVariation/{Integral,MonotoneDensity,TailIntegral}.lean` | the exact layer-cake identity, pure-power asymptotic, general Karamata theorem, monotone-density theorem, and equivalence between regular variation of a bounded nonnegative antitone tail and its twice-integrated tail are proved in the general distribution/analysis layers. For `ν` the increment law, a two-sided tail regularly varying with index `−α`, `0<α<2`, gives `Hν(u)/(u²Tν(u)) → α/(2−α)` and makes `L*ν(u)=u^(α−2)Hν(u)` slowly varying. The inverse cosine-kernel identity, nonmonotone Potter bound, Mellin-kernel limit, tail transfer, and exact truncated-moment/defect ratio are proved in `Analysis/Fourier/CosineTauberian` and `Probability/Distributions/CharacteristicFunction/Tauberian/SecondTail.lean`. Still open are the `α=2` normal-attraction case and the compatible norming and asymptotic-inverse steps. |
| (15)/(16): the factor `λ_n` | `Distributions/Stable/Attraction/Norming.lean` | `stableRateNormalization` (and its reciprocal `stableSmallDeviationRate`) |
| §1: classes `M₁`, `M₂`, `M₃`, and `M` and the corridor energy | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/PathClass/{Basic,Energy,Approximation}.lean` | finite extended-real step boundaries impose strict corridor inequalities on all of `[0,1]`; `M₂` records a continuous admissible path; `M₃` is a finite union with positive minimum energy; `M` uses the source's inner/outer inclusions and signed energy gap. Finite energy and equality of inner/outer limits when either sequence converges are proved. Measurability, convergence existence, and approximation-witness independence remain open |
| Лемма 1 I: the constant `C = −C*` | `Probability/Process/Stable/SmallDeviation/EscapeRate.lean`, `EscapeRate/{Corridor,Endpoint,Law}.lean`, and `Probability/Process/Stable/Corridor/Law.lean` | The stable-process version of (18)–(20) is proved, including a finite strictly negative escape rate, the shared rate for translated and endpoint-constrained tubes, and equality of range-tube probabilities for processes with the same stable increment specification. The escape-rate lower bound uses a common small reference width; endpoint positivity uses fixed finite entrance times. The general `CadlagPath` packaging bridge and the final stable-domain theorem remain open |
| Лемма 2, Лемма 3: individual and gluing estimates | `Combinatorics/BranchingWalk/Walk/Path/Block/Partition/Basic.lean` (gluing, scale-free) | gluing present; the per-block estimates **missing** |
| Теорема 2: single stable block | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Corridor.lean` | the corridor objects are present (`stableBlockTube`, `stableBlockCorridorProbability`), the estimate is **missing** |
| §3: partition, product bound, `(1−δ)`-shrink | `Combinatorics/BranchingWalk/Walk/Path/Block/Partition/{Basic,Normalized}.lean` + `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Partition.lean` | gluing present and scale-free; block count present with its bracket (`stableBlockCount_mul_stableBlockLength_le_lt_succ`), asymptotic open |
| the two `ε`-approximations of a corridor | `Combinatorics/BranchingWalk/Walk/Path/Corridor.lean`, `Combinatorics/BranchingWalk/Walk/Path/Corridor/Energy.lean` | present (`InOpenCorridorOn.of_shrunk`, `.relax`, `corridorEnergy_add_sub`, `corridorEnergy_sub_add`) |
| Later `α = 2` input | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Gaussian/DonskerSpecialization.lean` | only the Gaussian domain-of-attraction adapter is present; it does not prove the `α = 2` Mogulskii theorem or compute the stable escape constant |

The stable-process scaling adapter is isolated in
`Probability/Process/Stable/SmallDeviation/RationalTube.lean`. It proves the
rational-coordinate target set is measurable and gives the exact stable
time-space/small-width-to-long-horizon reparameterization used by the proof
route. The process-level escape-rate limit and its strict negativity are now
proved in `Probability/Process/Stable/SmallDeviation/EscapeRate.lean`. The
application-level bridge to the `CadlagPath` tube law and the final stable
Mogulskii estimate remain open.

## Corrections to the block-scale interpretation

The implementation defines

```text
stableBlockLength α ν c a n = ⌊c · κν(a n)⌋₊
κν(u) = u^α / L*ν(u)
```

so the slowly varying factor is present in the block length. The earlier note that described this as `⌊c · a n^α⌋₊` and inferred an order-`n` block from boundedness of `L*` was incorrect. General slow variation permits unbounded or vanishing factors, so it does not give `L*ν(u) = Θ(1)` or allow that factor to be absorbed into a fixed partition constant. The current formal scale lemmas make their stronger hypotheses explicit; the monotone Potter upper bound is available, while its application to the scale and the asymptotic-inverse argument are still required.

The general ratio-limit interface is in `Analysis/Asymptotics/RegularVariation.lean`; the integral Karamata theorem is in `Analysis/Asymptotics/RegularVariation/Integral.lean`. It proves product and reciprocal closure, a Potter upper bound when the regularly varying function is eventually nondecreasing, and `stableScaleTime_isRegularlyVaryingAtTop`. The truncated-moment theorem applies Karamata to `Tν(√t)` and proves `Hν(u)/(u²Tν(u)) → α/(2−α)` for a regularly varying two-sided tail. Consequently, `stableSlowVariation_isSlowlyVarying_of_regularlyVaryingTail` establishes slow variation of `L*ν` under that tail hypothesis. The inverse cosine-kernel work and the probability-facing Tauberian bridge now prove the defect-to-tail implication for `0<α<2`, including nonmonotone Potter control, the kernel integral limit, transfer from the symmetrized law, and the truncated-moment ratio. Still open are the `α=2` normal-attraction result and the asymptotic-inverse argument.

The code parameter `a` is the corridor scale. The separate norming sequence `b` is used in the scale lemmas to compare block lengths with the horizon. The relation between these implemented block lengths and the fixed relative-time partition in §3 has not yet been proved under the source's general assumptions.

## The inverse norming function

`κν(u) = u ^ α / L*ν(u)` — the function `B*` of (4), whose asymptotic inverse is the norming `B`, and whose regular variation is used in (43) — is `stableScaleTime` in `Distributions/Stable/Attraction/Norming.lean`. The theorem `stableRateNormalization_eq_natCast_div_stableScaleTime` expresses `λ n = n / κν(aₙ)`.

The formal block length uses the corridor scale `aₙ` and includes `L*ν(aₙ)` in its denominator. The current conditional scale results show what follows when `L*ν` has a positive finite limit. The monotone Potter estimate is now available as an analysis lemma, but the results do not yet prove the relations needed for a general slowly varying factor or identify these blocks with the source's fixed relative-time partition.
