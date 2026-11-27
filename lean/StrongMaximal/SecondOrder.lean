/-
The second-order coefficient of the v1 manuscript: from
`log Cₙ = nμ - dₙ + O(log n)` and the Mills-ratio limit `zₙ / √(log n) → 1` one gets

  `(μn - log Cₙ) / √(n log n) → √μ`,

i.e. the second term of `log Cₙ` is `-√μ √(n log n)`.

Both inputs are available: the Mills-ratio limit is `zOf_div_sqrt_log`
(`StrongMaximal.Zeta`), the `O(log n)` sandwich is the hypothesis `h` below.
The algebraic splitting, the identification `√(μn)/√(n log n) = √μ/√(log n)`,
and the vanishing of the remainder are all proved here.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import StrongMaximal.Main
import StrongMaximal.Zeta

namespace StrongMaximalEndpoint

open Filter Asymptotics
open scoped Topology

/-- `log x / x → 0`. -/
theorem tendsto_log_div_id : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- `log n / n → 0` along the naturals. -/
theorem tendsto_log_div_nat : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_log_div_id.comp tendsto_natCast_atTop_atTop

/-- `√(log n / n) → 0`. -/
theorem tendsto_sqrt_log_div_nat :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp tendsto_log_div_nat
  simpa only [Function.comp_def, Real.sqrt_zero] using h

/-- `√(μn) / √(n log n) = √μ / √(log n)` for `n ≥ 2`. -/
lemma sqrt_mu_mul_div {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (mu * (n : ℝ)) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
      = Real.sqrt mu / Real.sqrt (Real.log (n : ℝ)) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < Real.log (n : ℝ) := by
    have : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos this
  have hmu : 0 < mu := by linarith [one_lt_mu]
  rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ mu * (n:ℝ))]
  have hfrac : mu * (n:ℝ) / ((n:ℝ) * Real.log (n:ℝ)) = mu / Real.log (n:ℝ) := by
    field_simp
  rw [hfrac, Real.sqrt_div hmu.le]

/-- **Second-order coefficient.**

If `log Cₙ = nμ - dₙ + O(log n)`, then `(μn - log Cₙ) / √(n log n) → √μ`. -/
theorem second_order_coefficient (C : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ᶠ n in atTop, |Real.log (C n) - ((n : ℝ) * mu - dOf n)| ≤ K * Real.log (n : ℝ)) :
    Tendsto (fun n : ℕ => ((n : ℝ) * mu - Real.log (C n))
      / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 (Real.sqrt mu)) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos hn1
  -- the remainder vanishes
  have hrem : Tendsto (fun n : ℕ =>
      (Real.log (C n) - ((n : ℝ) * mu - dOf n))
        / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 0) := by
    have hbound : ∀ᶠ n : ℕ in atTop,
        ‖(Real.log (C n) - ((n : ℝ) * mu - dOf n))
          / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))‖
        ≤ K * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := by
      filter_upwards [h, hlog, eventually_ge_atTop 2] with n hn hL hn2
      have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hsq : 0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
        Real.sqrt_pos.mpr (by positivity)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
      set u : ℝ := Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) with hu
      have hu2 : Real.log (n : ℝ) = (n:ℝ) * u ^ 2 := by
        rw [hu, Real.sq_sqrt (by positivity)]
        field_simp
      have hsqn : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) = (n:ℝ) * u := by
        rw [hu2, show (n:ℝ) * ((n:ℝ) * u^2) = ((n:ℝ) * u)^2 by ring]
        rw [Real.sqrt_sq (by positivity)]
      rw [hsqn]
      have hu0 : 0 ≤ u := Real.sqrt_nonneg _
      nlinarith [hn, hu2, hK, hu0, hn0]
    refine squeeze_zero_norm' hbound ?_
    simpa [mul_comm] using tendsto_sqrt_log_div_nat.const_mul K
  -- the centering part converges to `√μ`
  have hmain : Tendsto (fun n : ℕ => dOf n / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (Real.sqrt mu)) := by
    have heq : ∀ᶠ n : ℕ in atTop, dOf n / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
        = Real.sqrt mu * (zOf n / Real.sqrt (Real.log (n : ℝ))) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      rw [dOf]
      calc Real.sqrt (mu * (n:ℝ)) * zOf n / Real.sqrt ((n:ℝ) * Real.log (n:ℝ))
          = (Real.sqrt (mu * (n:ℝ)) / Real.sqrt ((n:ℝ) * Real.log (n:ℝ))) * zOf n := by ring
        _ = (Real.sqrt mu / Real.sqrt (Real.log (n:ℝ))) * zOf n := by
              rw [sqrt_mu_mul_div hn]
        _ = Real.sqrt mu * (zOf n / Real.sqrt (Real.log (n:ℝ))) := by ring
    have hlim : Tendsto (fun n : ℕ => Real.sqrt mu * (zOf n / Real.sqrt (Real.log (n : ℝ))))
        atTop (𝓝 (Real.sqrt mu * 1)) := tendsto_const_nhds.mul zOf_div_sqrt_log
    rw [mul_one] at hlim
    exact hlim.congr' (EventuallyEq.symm heq)
  -- assemble
  have hsplit : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) * mu - Real.log (C n)) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
        = dOf n / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
          - (Real.log (C n) - ((n : ℝ) * mu - dOf n))
            / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    filter_upwards with n
    ring
  have hfin := hmain.sub hrem
  simpa using hfin.congr' (EventuallyEq.symm hsplit)

/-- **The second-order coefficient follows from Theorem 1.1.**  The `O(log n)`
sandwich used by `second_order_coefficient` is no longer a hypothesis: it is
`sandwich_of_twoSided`, derived from the two-sided estimate. -/
theorem second_order_of_twoSided {C : ℕ → ℝ} (h : TwoSidedEventual C) :
    Tendsto (fun n : ℕ => ((n : ℝ) * mu - Real.log (C n))
      / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 (Real.sqrt mu)) :=
  second_order_coefficient C (by norm_num) (sandwich_of_twoSided h)

end StrongMaximalEndpoint
