/-
Progress towards `zₙ ∼ √(log n)`, the Mills-ratio step of the manuscript.

From the two-sided bounds `e⁻² φ(z) ≤ √(μ/n) z² ≤ φ(z)` at `z = zₙ`, taking
logarithms gives, with `L = log n`,

  `L - log μ - log(2π) - 4 log zₙ - 4 ≤ zₙ² ≤ L - log μ - log(2π) - 4 log zₙ`.

Since `zₙ → ∞` the right-hand side is `≤ L`, so `zₙ² ≤ L` and hence
`log zₙ ≤ ½ log L`; the left-hand side then gives `zₙ² ≥ L - O(log L)`.
Dividing by `L` and using `log L / L → 0` yields `zₙ²/L → 1`, and taking square
roots `zₙ/√L → 1`.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.Lemmas
import StrongMaximal.Mills

namespace StrongMaximalEndpoint

open Filter Topology MeasureTheory
open scoped Real Topology Interval

set_option maxHeartbeats 1200000

theorem tendsto_const_sqrt_div : Tendsto (fun n : ℕ => Real.sqrt (mu / n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => mu / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat mu
  have h2 : Tendsto (fun n : ℕ => Real.sqrt (mu / (n : ℝ))) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.continuousAt).tendsto.comp h1
  simpa using h2

/-- `zₙ → ∞`. -/
theorem zOf_tendsto_atTop : Tendsto zOf atTop atTop := by
  rw [tendsto_atTop]
  intro M
  set A : ℝ := max M 0 + 1 with hA
  have hA0 : 0 < A := by rw [hA]; nlinarith [le_max_right M 0]
  have hM : M < A := by rw [hA]; linarith [le_max_left M 0]
  have hA1 : 1 ≤ A := by rw [hA]; linarith [le_max_right M 0]
  have hApos : 0 < gaussTail A := by
    have h := gaussTail_ge_div (z := A) hA1
    have h2 : 0 < Real.exp (-2) * gaussPhi A / A :=
      div_pos (mul_pos (Real.exp_pos _) (gaussPhi_pos A)) hA0
    linarith
  have hc : ∀ᶠ n : ℕ in atTop, Real.sqrt (mu / n) * A < gaussTail A := by
    have h0 : Tendsto (fun n : ℕ => Real.sqrt (mu / n) * A) atTop (𝓝 (0 * A)) :=
      tendsto_const_sqrt_div.mul_const A
    rw [zero_mul] at h0
    exact h0.eventually (Iio_mem_nhds hApos)
  filter_upwards [hc, eventually_ge_atTop 2] with n hgt hn2
  by_contra hle
  push_neg at hle
  have hspec := zOf_spec hn2
  have hleA : zOf n < A := lt_trans hle hM
  have hmono : gaussTail A ≤ gaussTail (zOf n) := (gaussTail_lt_of_lt hleA).le
  have hc0 : 0 ≤ Real.sqrt (mu / n) := Real.sqrt_nonneg _
  nlinarith [hgt, hmono, hspec]

/-- `log φ z = -log √(2π) - z²/2`. -/
lemma log_gaussPhi {z : ℝ} (hz : 0 < z) :
    Real.log (gaussPhi z) = -Real.log (Real.sqrt (2 * π)) - z ^ 2 / 2 := by
  have hpos : (0:ℝ) < (Real.sqrt (2 * π))⁻¹ := inv_sqrt_two_pi_pos
  unfold gaussPhi
  rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
  ring

/-- `log √(μ/n) = (log μ - log n)/2`. -/
lemma log_sqrt_mu_div {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Real.sqrt (mu / n)) = (Real.log mu - Real.log n) / 2 := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmu : 0 < mu := by linarith [one_lt_mu]
  rw [Real.log_sqrt (by positivity), Real.log_div hmu.ne' hn0.ne']

/-- The two-sided bounds at `z = zₙ`, in the form `e⁻² φ(z) ≤ √(μ/n) z² ≤ φ(z)`. -/
theorem zOf_bounds {n : ℕ} (hn : 2 ≤ n) (hz1 : 1 ≤ zOf n) :
    Real.exp (-2) * gaussPhi (zOf n) ≤ Real.sqrt (mu / n) * (zOf n) ^ 2 ∧
      Real.sqrt (mu / n) * (zOf n) ^ 2 ≤ gaussPhi (zOf n) := by
  have hz : 0 < zOf n := zOf_pos hn
  have hspec := zOf_spec hn
  have hc0 : 0 ≤ Real.sqrt (mu / n) := Real.sqrt_nonneg _
  constructor
  · have h := gaussTail_ge_div hz1
    rw [hspec] at h
    have := mul_le_mul_of_nonneg_right h hz.le
    calc Real.exp (-2) * gaussPhi (zOf n) = Real.exp (-2) * gaussPhi (zOf n) / zOf n * zOf n := by
          field_simp
      _ ≤ Real.sqrt (mu / n) * zOf n * zOf n := this
      _ = Real.sqrt (mu / n) * (zOf n) ^ 2 := by ring
  · have h := gaussTail_le_div hz
    rw [hspec] at h
    have := mul_le_mul_of_nonneg_right h hz.le
    calc Real.sqrt (mu / n) * (zOf n) ^ 2 = Real.sqrt (mu / n) * zOf n * zOf n := by ring
      _ ≤ gaussPhi (zOf n) / zOf n * zOf n := this
      _ = gaussPhi (zOf n) := by field_simp

/-- `log log n / log n → 0`. -/
theorem tendsto_log_log_div_log :
    Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero |>.comp hlog
/-- The logarithmic form of the two-sided bounds at `z = zₙ`. -/
lemma zOf_log_bounds {n : ℕ} (hn : 2 ≤ n) (hz1 : 1 ≤ zOf n) :
    Real.log (n : ℝ) - Real.log (2 * π) - Real.log mu - 4 * Real.log (zOf n) - 4
        ≤ (zOf n) ^ 2 ∧
      (zOf n) ^ 2
        ≤ Real.log (n : ℝ) - Real.log (2 * π) - Real.log mu - 4 * Real.log (zOf n) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmu : 0 < mu := by linarith [one_lt_mu]
  have hz : 0 < zOf n := zOf_pos hn
  have hb := zOf_bounds hn hz1
  have hlogc : Real.log (Real.sqrt (mu / n)) = (Real.log mu - Real.log n) / 2 :=
    log_sqrt_mu_div (by omega)
  have hcpos : (0:ℝ) < Real.sqrt (mu / n) := Real.sqrt_pos.mpr (by positivity)
  have hlogphi : Real.log (gaussPhi (zOf n)) = -Real.log (2 * π) / 2 - (zOf n) ^ 2 / 2 := by
    rw [log_gaussPhi hz, Real.log_sqrt (by positivity)]
    ring
  have hlog1 : Real.log (Real.sqrt (mu / n) * (zOf n) ^ 2)
      = (Real.log mu - Real.log n) / 2 + 2 * Real.log (zOf n) := by
    rw [Real.log_mul hcpos.ne' (pow_ne_zero 2 hz.ne'), Real.log_pow, hlogc]
    ring
  have hlog3 : Real.log (Real.exp (-2) * gaussPhi (zOf n))
      = -2 + (-Real.log (2 * π) / 2 - (zOf n) ^ 2 / 2) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (gaussPhi_pos _).ne', Real.log_exp, hlogphi]
  constructor
  · have h := Real.log_le_log (mul_pos (Real.exp_pos _) (gaussPhi_pos _)) hb.1
    rw [hlog3, hlog1] at h
    linarith
  · have h := Real.log_le_log (mul_pos hcpos (pow_pos hz 2)) hb.2
    rw [hlog1, hlogphi] at h
    linarith

/-- `zₙ² ≤ log n` eventually. -/
theorem zOf_sq_le_log : ∀ᶠ n : ℕ in atTop, (zOf n) ^ 2 ≤ Real.log (n : ℝ) := by
  filter_upwards [eventually_ge_atTop 2, zOf_tendsto_atTop.eventually (eventually_ge_atTop 1)]
    with n hn2 hz1
  have h := (zOf_log_bounds hn2 hz1).2
  have hlogz : 0 ≤ Real.log (zOf n) := Real.log_nonneg hz1
  have h1 : (0:ℝ) < Real.log (2 * π) := Real.log_pos (by nlinarith [Real.pi_gt_d20])
  have h2 : (0:ℝ) < Real.log mu := Real.log_pos one_lt_mu
  linarith

/-- `zₙ²` is at least `log n` minus `O(log log n)`. -/
theorem zOf_sq_ge_log : ∀ᶠ n : ℕ in atTop,
    Real.log (n : ℝ) - (Real.log (2 * π) + Real.log mu + 4) - 2 * Real.log (Real.log (n : ℝ))
      ≤ (zOf n) ^ 2 := by
  filter_upwards [eventually_ge_atTop 2, zOf_sq_le_log,
    zOf_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn2 hsq hz1
  have hz : 0 < zOf n := zOf_pos hn2
  have h := (zOf_log_bounds hn2 hz1).1
  have hlogz_le : Real.log (zOf n) ≤ Real.log (Real.log (n : ℝ)) / 2 := by
    have h1 : Real.log ((zOf n) ^ 2) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log (pow_pos hz 2) hsq
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  linarith

/-- **`zₙ² / log n → 1`**, the manuscript's `zₙ ∼ √(log n)` in squared form. -/
theorem zOf_sq_div_log :
    Tendsto (fun n : ℕ => (zOf n) ^ 2 / Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos hn1
  set X : ℕ → ℝ := fun n =>
    Real.log (2 * π) + Real.log mu + 4 + 2 * Real.log (Real.log (n : ℝ)) with hX
  have hzeroX : Tendsto (fun n : ℕ => X n / Real.log (n : ℝ)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hC : Tendsto (fun n : ℕ => (Real.log (2 * π) + Real.log mu + 4) / Real.log (n : ℝ))
        atTop (𝓝 0) := hbase.const_div_atTop _
    have h2 : Tendsto (fun n : ℕ => 2 * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
        atTop (𝓝 0) := by
      simpa using tendsto_log_log_div_log.const_mul 2
    have hsum := hC.add h2
    have heq : (fun n : ℕ => X n / Real.log (n : ℝ))
        = fun n : ℕ => (Real.log (2 * π) + Real.log mu + 4) / Real.log (n : ℝ)
            + 2 * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by
      funext n; simp only [hX]; ring
    rw [heq]
    simpa using hsum
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖1 - (zOf n) ^ 2 / Real.log (n : ℝ)‖ ≤ X n / Real.log (n : ℝ) := by
    filter_upwards [hlog, zOf_sq_le_log, zOf_sq_ge_log] with n hL hup hlo
    have hLpos : 0 < Real.log (n : ℝ) := hL
    have h1 : 0 ≤ 1 - (zOf n) ^ 2 / Real.log (n : ℝ) := by
      rw [sub_nonneg, div_le_one hLpos]; exact hup
    have h2 : 1 - (zOf n) ^ 2 / Real.log (n : ℝ) ≤ X n / Real.log (n : ℝ) := by
      have h3 : (Real.log (n : ℝ) - X n) / Real.log (n : ℝ)
          ≤ (zOf n) ^ 2 / Real.log (n : ℝ) := by
        rw [div_le_div_iff_of_pos_right hLpos]
        simp only [hX]
        linarith
      have h4 : (Real.log (n : ℝ) - X n) / Real.log (n : ℝ) = 1 - X n / Real.log (n : ℝ) := by
        field_simp
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2
  have hzero := squeeze_zero_norm' hbound hzeroX
  have h1 : Tendsto (fun n : ℕ => 1 - (1 - (zOf n) ^ 2 / Real.log (n : ℝ))) atTop (𝓝 (1 - 0)) :=
    hzero.const_sub 1
  rw [sub_zero] at h1
  refine h1.congr' ?_
  exact Eventually.of_forall fun n => by ring

/-- **`zₙ / √(log n) → 1`**. -/
theorem zOf_div_sqrt_log :
    Tendsto (fun n : ℕ => zOf n / Real.sqrt (Real.log (n : ℝ))) atTop (𝓝 1) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos hn1
  have hsq : Tendsto (fun n : ℕ => ((zOf n) / Real.sqrt (Real.log (n : ℝ))) ^ 2) atTop (𝓝 1) := by
    have heq : ∀ᶠ n : ℕ in atTop,
        ((zOf n) / Real.sqrt (Real.log (n : ℝ))) ^ 2 = (zOf n) ^ 2 / Real.log (n : ℝ) := by
      filter_upwards [hlog] with n hL
      rw [div_pow, Real.sq_sqrt hL.le]
    exact zOf_sq_div_log.congr' (EventuallyEq.symm heq)
  have hnn : ∀ᶠ n : ℕ in atTop, 0 ≤ zOf n / Real.sqrt (Real.log (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (zOf_pos hn).le (Real.sqrt_nonneg _)
  have hsq' : Tendsto (fun n : ℕ => ((zOf n) / Real.sqrt (Real.log (n : ℝ))) ^ 2) atTop (𝓝 1) := by
    simpa using hsq
  have hcont : Tendsto (fun n : ℕ => Real.sqrt (((zOf n) / Real.sqrt (Real.log (n : ℝ))) ^ 2))
      atTop (𝓝 (Real.sqrt 1)) := Real.continuous_sqrt.continuousAt.tendsto.comp hsq'
  rw [Real.sqrt_one] at hcont
  refine hcont.congr' ?_
  filter_upwards [hnn] with n hn
  exact Real.sqrt_sq hn


end StrongMaximalEndpoint
