# Lean 4 formalisation status — v1 endpoint constants

Toolchain `leanprover/lean4:v4.36.0`, Mathlib pinned to `v4.36.0`
(commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`), see `lakefile.lean` and
`lake-manifest.json`.

```
cd lean && ./verify.sh         # forbidden-token scan, regenerated audit, clean build, axiom check
cd lean && ./build.sh          # just compiles all modules and prints the audit
```

On a fresh checkout `.lake/packages` is absent; fetch the pinned Mathlib first:

```
cd lean && lake exe cache get && ./verify.sh
```

In this working copy `lean/.lake/packages` is a symlink to the prebuilt Mathlib
of the sibling archived project, which is why no download is needed here.

`verify.sh` regenerates `StrongMaximal/Audit.lean` by scanning **every**
declaration in `StrongMaximal/*.lean`, so the audit cannot drift from the
sources: the hand-maintained list that earlier rounds carried covered 72 of the
226 declarations; the generated one covers all of them.

Every declaration listed below compiles and the `#print axioms` output in
`Audit.lean` is, for **every** one of the 226 declarations,

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorry`, no `admit`, no project-defined axiom, and no external
computation used as a step.

---

## 0. Definition-level correspondence (paper ↔ Lean)

Checked item by item against `paper/source/paper.tex` (the fixed v1 source).  The
axes requested by the acceptance criteria are: operator, normalization,
quantifiers, input range, limit centering, coefficients.

| axis | manuscript | Lean | file | verdict |
|---|---|---|---|---|
| operator | `Mₙf(x) = sup` of averages of `\|f\|` over **bounded axis-parallel rectangles of positive volume containing `x`**, not required to be centred at `x` | `strongMax n f x = ⨆ S : RectsAt n x, (∫⁻ y in Icc lo hi, ofReal \|f y\|) / ofReal S.volume`, `Rect` = box `[lo,hi]` with `lo i < hi i` for all `i` | `Basic.lean` | matches: box = product of intervals, full-dimensional (positive volume), `x ∈ Icc lo hi` = contains `x`, no centring condition |
| normalization | average `= \|R\|⁻¹ ∫_R \|f\|` | denominator `ENNReal.ofReal S.volume` with `Rect.volume = ∏ᵢ(hiᵢ−loᵢ)`; `volume_carrier : volume (Icc lo hi) = ofReal R.volume` | `Basic.lean`, `TestInput.lean` | matches (the identification `volume = product of side lengths` is proved, not assumed) |
| Young function | `Φₙ(t) = t(1+log⁺t)^{n−1}`, `Φₙ(0)=0`, natural logs | `Phi n t = t * (1 + logPos t)^(n-1)`, `logPos t = max (Real.log t) 0` | `Basic.lean` | matches; `Φₙ 0 = 0` holds because Lean's `Real.log 0 = 0`, so `logPos 0 = 0` |
| normalization of `Cₙ` | `Cₙ = sup_{0<∫Φₙ(\|f\|)<∞} \|{Mₙf>1}\| / ∫Φₙ(\|f\|)` | `endpointConst n = ⨆ (f) (_ : Admissible n f), volume {x \| 1 < strongMax n f x} / ∫⁻ Φₙ(\|f\|)`, `Admissible` = measurable ∧ `0<∫` ∧ `∫≠∞` | `Basic.lean` | matches; the extra `Measurable f` is implicit in the manuscript (the integral is only defined for measurable inputs) |
| `λ`-form | `\|{Mₙf>λ}\| ≤ Kₙ ∫ Φₙ(\|f(x)\|/λ) dx` for `λ>0` | `endpointConst_lambda_uncond`: same statement with `Kₙ = Cₙ`, for every measurable `f` and every `λ>0` | `TestInput.lean` | matches, including the argument `\|f\|/λ` inside `Φₙ` (not `Φₙ(\|f\|)/λ`) |
| input range | `λ>0`; `f` measurable with `0<∫Φₙ(\|f\|)<∞` | `hlam : 0 < lam`; `hmeas : Measurable f`; `Admissible` | `TestInput.lean` | matches; the degenerate cases `∫=0` and `∫=∞` are handled (`endpointConst_lambda_of_zero`, `endpointConst_lambda_of_infinite`) |
| `μ` | positive root of `μ = 1+e^{−μ}` | `mu`, `mu_eq : mu = 1 + exp(-mu)`, `existsUnique_mu` | `Constants.lean` | matches |
| tail `Φ̄` | standard normal upper tail | `gaussPhi` (density `φ`), `gaussTail z = 1/2 − ∫₀^z φ`; **`gaussTail_eq_setIntegral : gaussTail z = ∫_{x>z} φ`** | `Gaussian.lean`, `Mills.lean` | matches — but see the note below |
| `zₙ` | `Φ̄(zₙ) = √(μ/n)·zₙ`, unique positive root | `zOf`, `zOf_spec`, `existsUnique_zOf` (for `n ≥ 2`) | `Gaussian.lean` | matches; the paper's "opposite strict monotonicities give a unique root" is `gaussTail_lt_of_lt` + strict increase of `z ↦ √(μ/n)z` |
| `dₙ` | `dₙ = √(μn)·zₙ` | `dOf n = sqrt (mu * n) * zOf n`, `dOf_eq : dOf n = n * Φ̄(zₙ)` | `Gaussian.lean` | matches |
| limit centering | `(log Cₙ − nμ + dₙ)/log n` | `Eexp C n = (Real.log (C n) − (n:ℝ)*mu + dOf n) / Real.log n` | `Main.lean` | matches exactly, including the sign of `dₙ` and the `log n` denominator |
| coefficients | `c₋ = (9−μ)/24`, `c₊ = (3+μ)/12`, window width `(μ−1)/8` | `cLo = (9−mu)/24`, `cHi = (3+mu)/12`, `g = (mu−1)/8`, `cLo_add_g : cLo + g = cHi`, `window_width` | `Constants.lean` | matches |
| Theorem 1.1 | `c₋ ≤ liminf Eₙ ≤ limsup Eₙ ≤ c₊` | `main_theorem` (from `TwoSidedEventual`), `endpointConst_main` (from `Bridge`) | `Main.lean`, `Transfer.lean` | matches as a *reduction*; see §2 |

**Discrepancy found and fixed in this audit.** The docstring of `gaussTail`
claimed `gaussTail_eq_setIntegral` ("identifies it with `∫_{x>z} φ`") but that
lemma had been dropped in an earlier rewrite of `Gaussian.lean`, leaving the
claim unproved.  It is now proved in `Mills.lean` (via
`gaussTail_split` + `intervalIntegral_tendsto_integral_Ioi` +
`tendsto_gaussTail_atTop`), and `gaussTail_split` itself had to be re-added to
`Gaussian.lean`.  Note also that `∫ u in a..b, φ u + gaussTail b` parses as an
integral of a *sum*; the statement needs the parentheses
`(∫ u in a..b, φ u) + gaussTail b`.

## 1. What is proved unconditionally

| Manuscript | Lean declaration | File | Status |
|---|---|---|---|
| `μ` unique root of `μ = 1 + e^{-μ}` | `mu_eq`, `existsUnique_mu`, `eq_mu_iff` | `Constants.lean` | complete |
| `1 < μ < 2` | `one_lt_mu`, `mu_lt_two` | `Constants.lean` | complete |
| `e^μ = 1/(μ-1)`, `e^{-μ} = μ-1` | `exp_mu`, `exp_neg_mu` | `Constants.lean` | complete |
| `g = (μ-1)/8`, `c₋ = (9-μ)/24`, `c₊ = (3+μ)/12` | `g`, `cLo`, `cHi` | `Constants.lean` | complete |
| `c₋ + g = c₊` (window width `g`) | `cLo_add_g`, `window_width`, `cLo_eq` | `Constants.lean` | complete |
| `Φₙ t = t(1+log⁺t)^{n-1}`, `Φₙ 0 = 0` | `Phi`, `Phi_zero`, `Phi_nonneg` | `Basic.lean` | complete |
| `Φₙ t = 0 ↔ t = 0` (t ≥ 0) | `Phi_eq_zero_iff` | `Basic.lean` | complete |
| axis-parallel rectangle, positive volume, **not** centred | `Rect`, `Rect.carrier`, `Rect.volume`, `Rect.volume_pos` | `Basic.lean` | complete |
| `Mₙ f` = sup of `|f|`-averages over rectangles containing `x` | `strongMax` | `Basic.lean` | complete (definition) |
| `Mₙ(c·f) = c·Mₙ f`, `c ≥ 0` (hence `λ`-form ⟺ `λ=1` form) | `strongMax_smul` | `Basic.lean` | complete |
| `Cₙ` = sup of `|{Mₙf>1}|/∫Φₙ(|f|)` over admissible `f` | `endpointConst`, `Admissible` | `Basic.lean` | complete (definition) |
| `Φ̄` standard normal tail, `Φ̄ 0 = 1/2` | `gaussPhi`, `gaussTail`, `gaussTail_zero` | `Gaussian.lean` | complete |
| `Φ̄` strictly decreasing (`Φ̄' = -φ < 0`) | `hasDerivAt_gaussTail`, `gaussTail_lt_of_lt` | `Gaussian.lean` | complete |
| `zₙ` exists and is unique for `n ≥ 2` | `existsUnique_zOf`, `zOf_pos`, `zOf_spec` | `Gaussian.lean` | complete |
| `dₙ = √(μn) zₙ` and `dₙ = n Φ̄(zₙ)` | `dOf`, `dOf_eq` | `Gaussian.lean` | complete |
| one-step mean `1+aρ`, `ρ μ = (μ-1)/μ` | `rho`, `mStep`, `rho_mu` | `Cumulants.lean` | complete |
| `m(μ) = μ`, `v(μ) = μ` | `mStep_mu`, `vStep_mu` | `Cumulants.lean` | complete |
| `κ₃(μ) = μ(3-μ)`, hence `κ₃/v = 3-μ` | `k3Step_mu`, `k3_div_v_mu` | `Cumulants.lean` | complete |
| `ρ' = -ρ(1-ρ)`, `m'(μ) = 0` | `hasDerivAt_rho`, `deriv_mStep_mu` | `Cumulants.lean` | complete |
| `m''(μ) = -(μ-1)/μ` | `deriv_deriv_mStep_mu` | `Cumulants.lean` | complete |
| `v'(μ) = μ-1` | `deriv_vStep_mu` | `Cumulants.lean` | complete |
| `n·½m''(μ)δ² = -g L` for `δ = ½√(μL/n)` | `mean_shift` | `Cumulants.lean` | complete |
| **Theorem 1.1**: `ε`-form ⟹ `c₋ ≤ liminf ≤ limsup ≤ c₊` | `main_theorem`, `cLo_le_liminf`, `limsup_le_cHi` | `Main.lean` | complete **as a reduction** |
| `O(log n)` form derived from the two-sided estimate | `sandwich_of_twoSided` | `Main.lean` | complete |
| **second-order coefficient**: `(μn-log Cₙ)/√(n log n) → √μ` | `second_order_coefficient` | `SecondOrder.lean` | complete given the `O(log n)` sandwich |
| **second-order coefficient from Theorem 1.1** (no sandwich hypothesis) | `second_order_of_twoSided` | `SecondOrder.lean` | **complete** |
| `√(n log n)` coefficient for `Cₙ`, derived from the bridge | `endpointConst_second_order_of_bridge` | `Transfer.lean` | conditional on `Bridge Q R` |
| `Φ̄ z → 0` at `+∞`; `Φ̄ ≥ 0` | `tendsto_gaussTail_atTop`, `gaussTail_nonneg` | `Mills.lean` | complete |
| upper Mills bound `Φ̄ z ≤ φ z/z` | `gaussTail_le_div` | `Mills.lean` | complete |
| lower Mills bound `e⁻²φ z/z ≤ Φ̄ z` (`z ≥ 1`) | `gaussTail_ge_div` | `Mills.lean` | complete |
| `φ → 0`, `φ z/z → 0` | `tendsto_gaussPhi_atTop`, `tendsto_gaussPhi_div_atTop` | `Mills.lean` | complete |
| `zₙ → ∞` | `zOf_tendsto_atTop` | `Zeta.lean` | complete |
| log form of the two-sided bounds at `zₙ` | `zOf_log_bounds` | `Zeta.lean` | complete |
| `zₙ²/log n → 1` (manuscript's `zₙ ∼ √(log n)`) | `zOf_sq_div_log` | `Zeta.lean` | complete |
| `zₙ/√(log n) → 1` | `zOf_div_sqrt_log` | `Zeta.lean` | complete |
| `Φ̄ a = (∫_{a..b} φ) + Φ̄ b` for `a ≤ b` | `gaussTail_split` | `Gaussian.lean` | complete |
| **`Φ̄ z = ∫_{x>z} φ`** (the tail *is* the standard normal upper tail) | `gaussTail_eq_setIntegral` | `Mills.lean` | complete |
| `Mₙ` depends only on the a.e. class; `Mₙ 0 = 0` | `strongMax_congr_ae`, `strongMax_zero` | `Endpoint.lean` | complete |
| `Cₙ` dominates every admissible ratio | `endpointConst_spec` | `Endpoint.lean` | complete |
| `λ < a ↔ 1 < λ⁻¹a` in `ℝ≥0∞`; level sets agree under `f ↦ f/λ` | `ennreal_ofReal_lt_iff`, `levelSet_eq` | `Endpoint.lean` | complete |
| `Φₙ` is measurable | `measurable_Phi` | `Basic.lean` | complete |
| `∫Φₙ(|g|) = 0 ⟹ g = 0` a.e. | `ae_eq_zero_of_lintegral_Phi_eq_zero` | `Endpoint.lean` | complete |
| the `λ`-form holds with constant `Cₙ` | `endpointConst_lambda` | `Endpoint.lean` | complete (for admissible `f/λ`) |
| plateau profile `H_w`; `1_{v≥0} + (v-w)₊/n ≤ H_w v` | `Hw`, `Hw_nonneg`, `Hw_ge_indicator` | `Plateau.lean` | complete (needs `w ≥ 0`) |
| every constant satisfying the `λ`-form dominates `Cₙ` | `le_endpointConst`, `le_endpointConst_measurable` | `Endpoint.lean`, `TestInput.lean` | complete |
| `volume` of a rectangle equals its product volume | `volume_carrier` | `TestInput.lean` | complete |
| explicit admissible input (`2` on a rectangle) | `testFun`, `measurable_testFun`, `admissible_testFun`, `ofReal_two_le_strongMax`, `lintegral_Phi_testFun` | `TestInput.lean` | complete |
| **`Cₙ ≠ 0`** in every dimension | `endpointConst_ne_zero_uncond` | `TestInput.lean` | complete |
| **`λ`-form for every measurable input**, unconditionally | `endpointConst_lambda_uncond` | `TestInput.lean` | complete |
| **`Cₙ` is the least constant** (admissible + minimal) | `endpointConst_least` | `TestInput.lean` | complete |
| `∫_R c = c·vol(R)` for `c ≥ 0` | `lintegral_const_carrier` | `TestInput.lean` | complete |
| sanity check: `Mₙ` of a constant `c ≥ 0` is `c` | `strongMax_const` | `TestInput.lean` | complete |
| `log⁺ t = log t` (`t ≥ 1`), `= 0` (`t ≤ 1`), `log⁺(2t) ≤ log2 + log⁺t` | `logPos_eq_log`, `logPos_eq_zero`, `logPos_two_mul` | `Basic.lean` | complete |
| **`Φₙ` strictly increasing on `[0,∞)`** | `Phi_strictMonoOn` | `Basic.lean` | complete |
| **doubling `Φₙ(2t) ≤ 2(1+log2)^{n-1}Φₙ(t)`** | `Phi_doubling` | `Basic.lean` | complete |
| `∫₀^∞ x e^{-x} dx = 1` | `integral_exp_neg_mul_self` | `ExpModel.lean` | complete |
| `Γ(1,1)` density is `e^{-x}` on `[0,∞)` | `gammaPDFReal_one_one` | `ExpModel.lean` | complete |
| **mean of `expMeasure 1` is `1`** | `integral_expMeasure_one` | `ExpModel.lean` | complete |
| Bernoulli mean `∫ 1_b ∂Ber(true,false,p) = p` | `integral_bernoulli_indicator` | `StepModel.lean` | complete |
| the increment law `Exp 1 × Ber(ρ a)` and increment `Z_a` | `stepLaw`, `stepIncr`, `rhoI` | `StepModel.lean` | complete |
| **`mStep` is the mean of `Z_a`**: `∫ Z_a = 1 + aρ(a)` | `integral_stepIncr` | `StepModel.lean` | complete |
| `Z_a` measurable and integrable for its own law | `measurable_stepIncr`, `integrable_stepIncr`, `isProbabilityMeasure_stepLaw` | `StepModel.lean` | complete |
| **`Sₙ = ∑_{i<n} Z_a` with `∫ Sₙ = n·m(a)`** | `nStepLaw`, `nIncr`, `integral_nIncr`, `isProbabilityMeasure_nStepLaw` | `NStepModel.lean` | complete |
| `∫₀^∞ x² e^{-x} = 2`; second moment of `expMeasure 1` | `integral_exp_neg_mul_sq_self`, `integral_expMeasure_one_sq` | `ExpModel.lean` | complete |
| **`E[Z_a²] = 2 + 2aρ + a²ρ`** | `integral_stepIncr_sq` | `Variance.lean` | complete |
| **`Var(Z_a) = vStep a`** | `variance_stepIncr`, `berPart_sq` | `Variance.lean` | complete |
| `∫₀^∞ e^{-rx} = 1/r`; `∫ e^{x/n} ∂(expMeasure 1) = (1-1/n)⁻¹` | `integral_exp_neg_mul_Ioi`, `integral_expMeasure_exp`, `integrable_exp_expMeasure` | `ExpModel.lean` | complete |
| **exponential moment of `Z_a`**: `E e^{Z_a/n}` and its finiteness | `integral_exp_stepIncr`, `integrable_exp_stepIncr` | `ExpMoment.lean` | complete |
| **exponential moment of `Sₙ`**: `E e^{Sₙ/n} = (E e^{Z_a/n})ⁿ`, finite | `exp_nIncr_eq`, `integral_exp_nIncr`, `integrable_exp_nIncr` | `ExpMoment.lean` | complete |
| `H_w v ≤ 1 + e^{(v-w)/n}`; `H_w`, `Sₙ` measurable | `Hw_le_one_add_exp`, `measurable_Hw`, `measurable_nIncr` | `HwModel.lean` | complete |
| `H_w(Sₙ - s)` integrable for the model | `integrable_Hw_nIncr`, `integrable_nIncr` | `HwModel.lean` | complete |
| **integrated plateau inequality on `Sₙ`** | `Hw_integral_ge_model` | `HwModel.lean` | complete |
| plateau width `w = (log n)/2 + log(log n)`, `> 0` for `n ≥ 3` | `plateauWidth`, `plateauWidth_pos` | `Threshold.lean` | complete |
| `H_w` nondecreasing; `q ↦ E H_w(Sₙ-q)` nonincreasing | `Hw_monotone`, `modelExp_anti` | `Threshold.lean` | complete |
| **threshold criterion**: `P(Sₙ ≤ s) < (E Sₙ-s-w)/n ⟹ E H_w(Sₙ-s) > 1` | `Hw_integral_gt_one_of_cdf_lt` | `Threshold.lean` | complete |
| plateau profile and `1_{v≥0}+(v−w)₊/n ≤ H_w v` (`w ≥ 0`) | `Hw`, `Hw_nonneg`, `Hw_ge_indicator` | `Plateau.lean` | complete |
| **integrated plateau inequality** `𝔼H_w(X−s) ≥ 1−F(s)+(𝔼X−s−w)/n` | `Hw_integral_ge` | `Plateau.lean` | complete (needs `H_w(X−s)` integrable) |
| bridge transfer: `0<Qₙ≤Cₙ≤Rₙ` carries the estimates | `twoSided_of_sandwich` | `Transfer.lean` | complete |
| Theorem 1.1 for `(endpointConst n).toReal`, given the bridge | `endpointConst_main` | `Transfer.lean` | conditional on `Bridge Q R` |
| `√(n log n)` coefficient for `Cₙ`, given the sandwich | `endpointConst_second_order` | `Transfer.lean` | complete given the sandwich |
| `ε`-form ⟺ `liminf`/`limsup` form | `twoSided_of_liminf_limsup`, `twoSided_iff_liminf_limsup` | `Main.lean` | complete (needs bounded `Eₙ`) |
| rational rank-CDF inversion archived in v1.0.0 | `cdf_threshold`, `rank_cdf_threshold` | `RankRat.lean` | complete (preserved verbatim) |

`main_theorem` takes the analytic input as a hypothesis, not as an axiom:

```lean
def TwoSidedEventual (C : ℕ → ℝ) : Prop :=
  (∀ ε > 0, ∀ᶠ n in atTop, cLo - ε ≤ Eexp C n) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, Eexp C n ≤ cHi + ε)

theorem main_theorem (C : ℕ → ℝ) (h : TwoSidedEventual C) :
    cLo ≤ liminf (Eexp C) atTop ∧
      liminf (Eexp C) atTop ≤ limsup (Eexp C) atTop ∧
      limsup (Eexp C) atTop ≤ cHi
```

`second_order_coefficient` takes the `O(log n)` sandwich

```lean
h : ∀ᶠ n, |log (C n) - (n μ - dₙ)| ≤ K log n
```

— the Mills-ratio limit it also needs is `zOf_div_sqrt_log`, proved in
`Zeta.lean` — and concludes
`Tendsto (fun n => (n μ - log (C n)) / √(n log n)) atTop (𝓝 (√μ))`.
The sandwich itself is **no longer an assumption**: `sandwich_of_twoSided`
derives `|log Cₙ - (nμ - dₙ)| ≤ 2 log n` from `TwoSidedEventual C` by taking
`ε = 1` (using `0 < c₋` and `c₊ < 1`).  Hence `second_order_of_twoSided`
obtains the coefficient from Theorem 1.1 alone, and
`endpointConst_second_order_of_bridge` does the same for `Cₙ` on top of the
bridge.
The remaining ingredients are the algebraic splitting
`nμ - log Cₙ = dₙ - (log Cₙ - (nμ - dₙ))`, the identification
`√(μn)/√(n log n) = √μ/√(log n)` (`sqrt_mu_mul_div`), and the vanishing of the
`O(log n)` remainder as `K√(log n / n) → 0` (`tendsto_sqrt_log_div_nat`, from
`Real.isLittleO_log_id_atTop`).

---

## 2. What is **not** formalised

These are the load-bearing analytic steps of the manuscript. None of them is
hidden in a hypothesis of a theorem that pretends to be the paper's theorem;
they are simply absent, and the two top-level statements above are labelled as
reductions/conditional accordingly.

1. ~~Mills ratio and `zₙ ∼ √(log n)`~~ — **now done** (`Mills.lean`, `Zeta.lean`).
   Both bounds are obtained by comparing derivatives rather than by integration
   by parts, which sidesteps the two identities (`∫ x φ = φ(z)`,
   `∫₀^∞ e^{-zu}du = 1/z`) that this Mathlib snapshot does not have:
   `z ↦ Φ̄ z - φ z/z` has derivative `φ z/z² > 0`, `z ↦ Φ̄ z - e⁻²φ z/z` has
   derivative `φ z(e⁻²-1+e⁻²/z²) ≤ -φ z/3 < 0` on `z ≥ 1`; both have limit `0`
   at `+∞`, which gives `e⁻²φ z/z ≤ Φ̄ z ≤ φ z/z`. Taking logarithms at `z = zₙ`
   then gives `zₙ² ≤ log n` and `zₙ² ≥ log n - O(log log n)`, hence
   `zₙ²/log n → 1` and `zₙ/√(log n) → 1`.
2. **The bridge `Qₙ ≤ Cₙ ≤ Rₙ`** (Lemma 2 of the paper) — the one remaining
   structural gap. Requires the one-dimensional rising-sun lemma, the decreasing
   rearrangement, the product bound `Mₙ ≤ Mₙ^dir ⋯ M₁^dir`, measurable
   near-optimal action selection (countable dense set of actions, first action
   within `ε/n`), and the `Γ(n,1)` model on `[-1,1]ⁿ`. **None** of this is
   formalised.
   What *is* formalised is its consequence: `Transfer.lean` defines the
   predicate `Bridge Q R` (`∀ᶠ n, 0 < Q n ∧ Q n ≤ (endpointConst n).toReal ∧
   (endpointConst n).toReal ≤ R n`) and proves `twoSided_of_sandwich` (the two
   one-sided estimates transfer across the sandwich), `endpointConst_main`
   (Theorem 1.1 for `(endpointConst n).toReal`) and
   `endpointConst_second_order`. The gap is therefore isolated in a single named
   hypothesis instead of being buried in the statement of the main theorem.
3. **The lower-bound input and the Laplace step.** The plateau profile and both
   its pointwise and integrated inequalities are formalised (`Plateau.lean`,
   `Hw_ge_indicator`, `Hw_integral_ge`). Missing: the truncated hyperbolic
   input, the actual rectangles realising the strict inequality `Mₙ f > 1`, and
   `Iₙ = ∫₀^∞ e^{-u+u/n}(1+u/n)^{n-1}du ∼ √(πn/2)` by Laplace's method.
   Note `Hw_integral_ge` assumes `H_w(X-s)` integrable, i.e. an exponential
   moment of `X`; for `Sₙ = Γ(n,1) + a·Bin(n,ρ)` this holds but is not
   formalised here.
4. **The upper bound** (modular budget `J(h)`, reference action, all-state
   Bellman comparison, Poisson correction, exterior estimates,
   `𝔼_π h(Sₙ) < 1`).
5. ~~`Cₙ` is the least admissible coefficient~~ — **now done**. `TestInput.lean`
   exhibits the admissible input `2·1_R` (`volume_carrier`,
   `ofReal_two_le_strongMax`, `admissible_testFun`), deduces
   `endpointConst_ne_zero_uncond`, and proves the `λ`-form for every measurable
   input (`endpointConst_lambda_uncond`) together with minimality
   (`le_endpointConst_measurable`), packaged as `endpointConst_least`.

---

## 3. 原稿缺口：lower-bound Edgeworth bookkeeping

While checking the constants against the definitions I found a **magnitude
error in the manuscript's derivation** (not in the Lean development). Location:
`paper/source/paper.tex`, §"Lower bound via a plateau in the input",
lines 115–120, the paragraph beginning "Put `x = (M-s)/√V`" and the sentence
"the skewness term contributes `-((3-μ)/6+o(1))L²/n`".

* The Gaussian part is correct: with `x - zₙ = (g-C)L/√(μn)` and
  `φ(zₙ)/√(μn) ~ L/n`, one gets `Φ̄(x) - Φ̄(zₙ) = (C-g)L²/n`, and
  `(M-s)/n = Φ̄(zₙ) - (g+C)L/n`.
* The skewness term is **not** of order `L²/n`. It is
  `(κ₃/(6V^{3/2}))(1-x²)φ(x)` with `κ₃ ≍ 1`, `V ≍ n`, `1-x² ≍ -L`,
  `φ(x) ≍ L^{1/2}n^{-1/2}`, hence of order `L^{3/2}/n²` — smaller than the
  Gaussian term `L²/n` by a factor `n/√L`. It cannot offset it.
* Consequently the paper's own sufficient criterion `F(s) < (M-s-w)/n` is
  satisfied only for `C < g + o(1)`, **not** for `C < c₋ = g + (3-μ)/6`.

Numerical cross-check (`verification/lean/lower-bound-audit.py`). Using the
exact mixture law `Sₙ = Γ(n,1) + aₙ·Bin(n,ρₙ)` with the paper's
`aₙ = μ - ½√(μL/n)` and solving `𝔼 H_w(Sₙ - q) = 1`:

| `n` | `L` | `C₀ = (q₀-(nμ-dₙ))/L` |
|---|---|---|
| 1e4 | 9.21 | 0.0305 |
| 1e5 | 11.51 | 0.0752 |
| 1e6 | 13.82 | 0.1077 |
| 1e7 | 16.12 | 0.1325 |
| 1e8 | 18.42 | 0.1755 |
| 1e9 | 20.72 | 1.1239 (float64 breakdown) |

The true plateau threshold is monotone increasing and sits far from
`c₋ = 0.3217`; it is also clearly above `g = 0.0348`, so the paper's *bound*
`liminf ≥ c₋` is not refuted by this computation, but the printed derivation
does not establish it — the skewness contribution it relies on is not there at
that order. This is recorded as a proof gap to be repaired by the authors, not
patched in the formalisation: `cLo` is kept at its manuscript value
`(9-μ)/24`, and `main_theorem` is a reduction that does not use the flawed
derivation.

(The `dₙ`-only part of the bookkeeping does check out exactly:
`κ₃(μ)/v(μ) = 3-μ` is an identity, `m(μ) = μ`, `v(μ) = μ`, `m''(μ) = -(μ-1)/μ`,
and `n·½m''(μ)δ² = -gL` are all in `Cumulants.lean`.)

---

## 4. Next minimal targets

0. ~~Second-order coefficient from Theorem 1.1~~ — **closed**.  `sandwich_of_twoSided`
   derives `|log Cₙ - (nμ - dₙ)| ≤ 2 log n` from `TwoSidedEventual C`, so
   `second_order_of_twoSided` gets `(μn - log Cₙ)/√(n log n) → √μ` from the
   two-sided estimate alone, and `endpointConst_second_order_of_bridge` does the
   same for `Cₙ` on top of the bridge.  Note what this does *not* say: the
   hypothesis is an estimate for `Cₙ` itself, never the fine expansion of `Qₙ`,
   in line with the manuscript's warning that `Qₙ`'s lower-order terms cannot be
   transplanted.

1. **The bridge `Qₙ ≤ Cₙ ≤ Rₙ`** (Lemma 2 of the paper) — the whole of §2, and
   now the *only* thing standing between this development and the paper's main
   theorem for `endpointConst`.
   Sub-targets, in order: the one-dimensional rising-sun lemma; the
   rearrangement bound `(Mᵢ^dir f)* ≤ T g`; the product bound
   `Mₙ ≤ Mₙ^dir ⋯ M₁^dir`; measurable near-optimal action selection; the
   `Γ(n,1)` model on `[-1,1]ⁿ`.
2. **The `Γ(n,1) + a·Bin(n,ρ)` model.**  Done: the one-step law
   (`stepLaw`, on `ℝ × Bool`), its increment `stepIncr`,
   `integral_stepIncr : ∫ Z_a = 1 + aρ(a) = mStep a`, and the `n`-fold product
   `nStepLaw` on `Fin n → ℝ × Bool` with
   `integral_nIncr : ∫ Sₙ = n·m(a)`, and the second moment / variance
   (`integral_stepIncr_sq`, `variance_stepIncr : Var Z_a = vStep a`).  So both
   `mStep` and `vStep` are now theorems about a genuine i.i.d. law.  Still
   missing: the exponential moment `𝔼 e^{Sₙ/n} < ∞` needed by `Hw_integral_ge`.
3. **Laplace asymptotics** for `Iₙ`, then the lower-bound threshold `q₀` and the
   `(9-μ)/24` coefficient.  The *criterion* is now formalised
   (`Hw_integral_gt_one_of_cdf_lt`): any `s` with `P(Sₙ ≤ s) < (E Sₙ - s - w)/n`
   satisfies `E H_w(Sₙ - s) > 1`, and `q ↦ E H_w(Sₙ - q)` is nonincreasing, so
   such `s` lies below the threshold.  What remains is the CDF estimate at the
   claimed scale — that is exactly the Edgeworth step of the manuscript, and it
   is where the bookkeeping gap of section 3 sits.

## 4b. Not formalised (unchanged)

* **The lower-bound construction** (truncated hyperbolic input, actual
  rectangles realising `Mₙ f > 1`, `Iₙ ∼ √(πn/2)` by Laplace's method).  The
  plateau profile itself is done (`Plateau.lean`).
* **The upper bound** (modular budget `J(h)`, reference action, all-state
  Bellman comparison, Poisson correction, exterior estimates,
  `𝔼_π h(Sₙ) < 1`).

## 5. Files

```
lean/
  lakefile.lean  lake-manifest.json  lean-toolchain  build.sh
  StrongMaximal.lean            umbrella
  StrongMaximal/Constants.lean  μ, g, c₋, c₊, closing identity
  StrongMaximal/ExpModel.lean   ∫₀^∞ x e^{-x} = 1; mean of expMeasure 1
  StrongMaximal/StepModel.lean  the increment law Exp 1 × Ber(ρ a); ∫ Z_a = mStep a
  StrongMaximal/NStepModel.lean Sₙ = ∑_{i<n} Z_a; ∫ Sₙ = n·m(a)
  StrongMaximal/Variance.lean   E[Z_a²], Var(Z_a) = vStep a
  StrongMaximal/ExpMoment.lean  exponential moments of Z_a and Sₙ
  StrongMaximal/HwModel.lean    plateau inequality instantiated on Sₙ
  StrongMaximal/Threshold.lean  plateau width, monotonicity, CDF criterion
  StrongMaximal/Gaussian.lean   φ, Φ̄, zₙ, dₙ
  StrongMaximal/Basic.lean      Φₙ, rectangles, Mₙ, Cₙ, homogeneity
  StrongMaximal/Cumulants.lean  one-step cumulants at μ
  StrongMaximal/Mills.lean      two-sided Mills bounds for Φ̄
  StrongMaximal/Zeta.lean       zₙ → ∞, zₙ²/log n → 1, zₙ/√(log n) → 1
  StrongMaximal/Main.lean       Theorem 1.1 (reduction), ε-form ⟺ liminf/limsup
  StrongMaximal/SecondOrder.lean  √(n log n) coefficient
  StrongMaximal/RankRat.lean    v1.0.0 rational rank lemma, preserved
  StrongMaximal/Endpoint.lean   Cₙ: spec, homogeneity, least constant
  StrongMaximal/Plateau.lean    the plateau profile H_w, pointwise + integrated
  StrongMaximal/Transfer.lean   Bridge Q R, Theorem 1.1 and second order for Cₙ
  StrongMaximal/TestInput.lean  explicit admissible input, Cₙ ≠ 0, Cₙ is least
  StrongMaximal/Audit.lean      generated by verify.sh: #print axioms, 226 decls
  verify.sh                     forbidden tokens + regenerated audit + clean build
  report.md                     this file
```

The published tag `v1.0.0` and the archived `paper/` and `verification/`
artefacts are untouched.
