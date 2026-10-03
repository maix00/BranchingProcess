# Mogulskii (1974) small deviations: the original statements, and where each one lives

Source: А. А. Могульский, *Малые уклонения в пространстве траекторий*, Теория вероятностей и её применения
**XIX**(4), 1974. Local copy at `~/Downloads/Mogulskii_1974_Small_deviations.pdf` (11 pages, 21363 characters of
text layer, extracted to `/tmp/mogul.txt`). The statements below are transcribed from that text; the OCR is
noisy, so formulas are restored to their mathematical reading while the original numbering — (2), (3), (4),
(15), (16), (18)–(20), (30)–(34), (36), (44) — is kept verbatim.

## The original statements

* **(2)** `ξ₁, ξ₂, …` i.i.d. with `P((ξ₁+…+ξₙ)/B(n) < x) → F_a(x)`, `F_a` **strictly stable**,
  **`0 < a ≤ 2`**; for `a = 1` an extra centering `βₙ = ∫ sin(t B⁻¹(n)) F(dt)`.
* **(3)** `L*(u) = u^{a−2} ∫_{−u}^{u} ξ² F(dξ)`, a **slowly varying** function (for `a < 2` it converges to
  `2c/(2−a)` when the tails behave as `c|ξ|^{-a}`; for `a = 2` it converges to `E ξ²`).
* **(4)** `B*(B(n)) ↝ d·n` with `B*(u) = u^a / L*(u)`; without loss of generality `d = 1`. Equivalently
  `bₙ^a = n·L*(bₙ)·(1 + o(1))`, so `bₙ^a` is of order `n`.
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
   `Walk/Path/Block/Partition/Basic.lean` formalizes.
2. **The block length in steps is `c·n` for a fixed `c > 0`, i.e. it only has to be of order `n`.** By (4),
   `bₙ^a = n L*(bₙ)(1+o(1))` and `L*` is bounded between positive constants, so
   `stableBlockLength α constant b n = ⌊constant · b n ^ α⌋₊` *is* `Θ(n)`: the slowly varying factor only
   rescales the free partition constant and does not move the constant of the theorem. The per-block
   probabilities contribute `Σ_i (b_i − a_i)^{-α} (t_{i+1} − t_i)`, the Riemann sum for `∫₀¹ dt/(g − f)^a`.

## Normalisation

```
λ_n := n · L*(x(n)) · x(n)^{-a}          -- the factor in (15) and Лемма 4
```

so that `−(1/λ_n) ln P(sₙ(·) ∈ G) → −C · H^a(G)`, and for a corridor `G = {f : g ≤ f ≤ h}` the functional
`H^a_x(G)` tends to `∫₀¹ dt / (g − f)^a`, the `corridorEnergy` of
`Combinatorics/BranchingWalk/Walk/Path/Corridor.lean`. `λ_n` is available in the library as
`stableRateNormalization α μ scale n`, defined as the reciprocal of `stableSmallDeviationRate` (commit
`7cccf6d4`), so every rate statement has both directions readable at the definition site.

## Where each piece lives

| original | module | state |
| --- | --- | --- |
| (2), (4): domain of attraction, norming | `Distributions/Stable/{Attraction,Basic}.lean`, `Mogulskii/Stable/Scale.lean` | present as predicates (`IsInAlphaStableDomainOfAttractionAlong`, `IsStableNorming`, `IsStableMogulskiiScale`); `IsStableNorming` now states the source's asymptotic relation `B*(B(n))/n → 1` |
| Fixed block endpoint under a domain-of-attraction limit | `Distributions/Stable/Attraction/Block.lean`, `Mogulskii/Stable/Scale.lean` | a general Slutsky adapter is proved for `partialSum (m n) / x n`; it preserves the centering contribution and requires the block length, norming ratio, and centering ratio limits explicitly. The norming ratio for `m n = ⌊τ B*(x n)⌋₊` follows conditionally from a positive finite limit of `L*`; the law-specific proof of that limit and the centering ratio remain open |
| Discrete block scale relations (Lemma 3/4 input) | `Walk/SmallDeviation/Mogulskii/Stable/{Scale,Partition}.lean` | if `L*(u) → ℓ ∈ (0,∞)`, the two-scale hypothesis and `B*(B(n))/n → 1` imply the rate tends to zero, the rounded block length is `o(n)`, `mₙ/B*(aₙ) → τ`, `B*(aₙ)/n · ⌊n/mₙ⌋ → 1/τ`, and `B(mₙ)/aₙ → τ^(1/α)`. The remaining law-specific step is proving the positive finite limit of `L*` for the strictly stable limit law; these conditional scale lemmas do not yet establish the discrete corridor probability estimates |
| (3): `L*` | `Walk/SmallDeviation/Mogulskii/Stable/{Normalization,TruncatedMoment}.lean`; `Analysis/Asymptotics/PowerTailIntegral.lean` | `truncatedSecondMoment` is exactly the layer-cake integral of the squared tail minus the endpoint correction. A general power-tail integral theorem is now proved, and `tendsto_stableSlowVariation_of_twoSidedTail` shows that `u^α P(|ξ|>u) → B > 0` implies `L*(u) → αB/(2−α)` for `0<α<2`. The stable-law tail asymptotic that supplies this hypothesis is still open. |
| (15)/(16): the factor `λ_n` | `Walk/SmallDeviation/Mogulskii/Stable/Normalization.lean` | `stableRateNormalization` (and its reciprocal `stableSmallDeviationRate`) |
| §1: classes `M₁`, `M₂`, `M₃`, and `M` and the corridor energy | `Mogulskii/Stable/PathClass/{Basic,Energy,Approximation}.lean` | finite extended-real step boundaries impose strict corridor inequalities on all of `[0,1]`; `M₂` records a continuous admissible path; `M₃` is a finite union with positive minimum energy; `M` uses the source's inner/outer inclusions and signed energy gap. Finite energy and equality of inner/outer limits when either sequence converges are proved. Measurability, convergence existence, and approximation-witness independence remain open |
| Лемма 1 I: the constant `C = −C*` | `Probability/Process/Stable/SmallDeviation/EscapeRate.lean`, `EscapeRate/{Corridor,Endpoint,Law}.lean`, and `Probability/Process/Stable/Corridor/Law.lean` | The stable-process version of (18)–(20) is proved, including a finite strictly negative escape rate, the shared rate for translated and endpoint-constrained tubes, and equality of range-tube probabilities for processes with the same stable increment specification. The escape-rate lower bound uses a common small reference width; endpoint positivity uses fixed finite entrance times. The general `CadlagPath` packaging bridge and the final stable-domain theorem remain open |
| Лемма 2, Лемма 3: individual and gluing estimates | `Walk/Path/Block/Partition/Basic.lean` (gluing, scale-free) | gluing present; the per-block estimates **missing** |
| Теорема 2: single stable block | `Mogulskii/Stable/Corridor.lean` | the corridor objects are present (`stableBlockTube`, `stableBlockCorridorProbability`), the estimate is **missing** |
| §3: partition, product bound, `(1−δ)`-shrink | `Walk/Path/Block/Partition/{Basic,Normalized}.lean` + `Mogulskii/Stable/Partition.lean` | gluing present and scale-free; block count present with its bracket (`stableBlockCount_mul_stableBlockLength_le_lt_succ`), asymptotic open |
| the two `ε`-approximations of a corridor | `Walk/Path/Corridor.lean`, `Walk/Path/Corridor/Energy.lean` | present (`InOpenCorridorOn.of_shrunk`, `.relax`, `corridorEnergy_add_sub`, `corridorEnergy_sub_add`) |
| Later `α = 2` input | `Mogulskii/Gaussian/DonskerSpecialization.lean` | only the Gaussian domain-of-attraction adapter is present; it does not prove the `α = 2` Mogulskii theorem or compute the stable escape constant |

The stable-process scaling adapter is isolated in
`Probability/Process/Stable/SmallDeviation/RationalTube.lean`. It proves the
rational-coordinate target set is measurable and gives the exact stable
time-space/small-width-to-long-horizon reparameterization used by the proof
route. The process-level escape-rate limit and its strict negativity are now
proved in `Probability/Process/Stable/SmallDeviation/EscapeRate.lean`. The
application-level bridge to the `CadlagPath` tube law and the final stable
Mogulskii estimate remain open.

## A finding that did not survive checking

An earlier version of this note claimed that `stableBlockLength α constant b n = ⌊constant · b n ^ α⌋₊` was
missing the slowly varying factor `L*`, so that the block count and hence the theorem's constant would be off
by the law-dependent constant `L*(bₙ)`. **That is wrong**, and §3 is what settles it: the partition's blocks
are relative sub-intervals with lengths fixed by the discontinuities of the boundary functions, so the block
length only needs to be of order `n`; by (4) it is, and the slowly varying factor is absorbed into the free
partition constant (the same constant that becomes the mesh of the Riemann sum above). This note is corrected
here rather than quietly deleted, because the definition looked wrong until the proof's construction was read.

## Update: the inverse norming function, and the parameter name that misled the note above

`B* (u) = u ^ α / L* (u)` — the function of (4), whose inverse is the norming `B`, and whose regular
variation `B* (a * u) ~ a ^ α * B* u` is (43) — is now `stableScaleTime` in
`Walk/SmallDeviation/Mogulskii/Stable/Normalization.lean`, together with
`stableRateNormalization_eq_natCast_div_stableScaleTime`: `λ n = n / B* (x n)`, the number of blocks of
`B* (x n)` steps inside `n` steps.

The second note above was written before the construction of §3 had been read and was misled by a parameter
name: `stableBlockLength α constant scale n` calls its argument `scale`, but every call site passes the
*normalization* `b n`, not the small scale `x n`. For the normalization, `⌊constant * b n ^ α⌋` is `Θ (n)`
by (4), since `b n ^ α ≍ n * L* (b n)` with `L*` slowly varying and bounded, so the definition is a block
holding a fixed fraction of the steps, which is what the partition of §3 needs, and the slowly varying
factor only shifts the free partition constant. The argument name is still worth fixing while the
definition stays as it is.
