/-
The mean of the exponential law, and hence the first moment of the
`Γ(1,1)` factor of the increment `Z_a = Exp 1 + a · Bernoulli (ρ a)`.

Mathlib has the Gamma density, its total mass, and the Gamma integral
`∫₀^∞ x^{a-1} e^{-rx} dx = Γ(a)/r^a`, but no moment computation for
`gammaMeasure`.  Here:

* `integral_exp_neg_mul_self`: `∫₀^∞ x e^{-x} dx = 1` (the `a = 2`, `r = 1`
  case of the Gamma integral, using `Γ(2) = 1`);
* `gammaPDFReal_one_one`: the `Γ(1,1)` density is `e^{-x}` on `[0,∞)`;
* `integral_expMeasure_one`: `∫ x ∂(expMeasure 1) = 1`.
-/
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

/-- `∫₀^∞ x e^{-x} dx = 1`. -/
theorem integral_exp_neg_mul_self :
    ∫ x in Set.Ioi (0:ℝ), x * Real.exp (-x) = 1 := by
  have hgamma : Real.Gamma 2 = 1 := by
    have := Real.Gamma_nat_eq_factorial 1
    simpa using this
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1)
    (by norm_num) (by norm_num)
  rw [hgamma] at h
  norm_num at h
  simpa [Real.rpow_one, mul_comm] using h

/-- The `Γ(1,1)` density is `e^{-x}` on `[0,∞)` and `0` below. -/
theorem gammaPDFReal_one_one (x : ℝ) :
    ProbabilityTheory.gammaPDFReal 1 1 x = if 0 ≤ x then Real.exp (-x) else 0 := by
  rw [ProbabilityTheory.gammaPDFReal]
  split_ifs with hx
  · simp only [Real.Gamma_one, Real.rpow_one, div_one, mul_one, one_mul,
      show (1:ℝ) - 1 = 0 by norm_num, Real.rpow_zero]
  · rfl

theorem gammaPDFReal_one_one_nonneg (x : ℝ) :
    0 ≤ ProbabilityTheory.gammaPDFReal 1 1 x := by
  rw [gammaPDFReal_one_one]
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

/-- **The mean of `expMeasure 1` is `1`.** -/
theorem integral_expMeasure_one :
    ∫ x, x ∂(ProbabilityTheory.expMeasure 1) = 1 := by
  have hmeas : Measurable (ProbabilityTheory.gammaPDF 1 1) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.gammaPDF 1 1 x < ∞ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  have hpt : ∀ x : ℝ, (ProbabilityTheory.gammaPDF 1 1 x).toReal • (x : ℝ)
      = (Set.Ioi (0:ℝ)).indicator (fun y : ℝ => y * Real.exp (-y)) x := by
    intro x
    rw [ProbabilityTheory.gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_one_one_nonneg x),
      smul_eq_mul, gammaPDFReal_one_one]
    by_cases hx : 0 < x
    · rw [if_pos hx.le, Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]
      ring
    · rcases lt_or_eq_of_le (not_lt.mp hx) with h | h
      · have hnot : x ∉ Set.Ioi (0:ℝ) := by
          simp only [Set.mem_Ioi, not_lt]
          linarith
        rw [if_neg (not_le.mpr h), Set.indicator_of_notMem hnot, zero_mul]
      · subst h
        rw [if_pos le_rfl, Set.indicator_of_notMem (by simp)]
        norm_num
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul hmeas hae]
  simp only [hpt]
  rw [integral_indicator measurableSet_Ioi]
  exact integral_exp_neg_mul_self
/-- `∫₀^∞ x² e^{-x} dx = 2`. -/
theorem integral_exp_neg_mul_sq_self :
    ∫ x in Set.Ioi (0:ℝ), x ^ 2 * Real.exp (-x) = 2 := by
  have hgamma : Real.Gamma 3 = 2 := by
    have := Real.Gamma_nat_eq_factorial 2
    simpa using this
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1)
    (by norm_num) (by norm_num)
  rw [hgamma] at h
  norm_num at h
  simpa [show (3:ℝ) - 1 = 2 by norm_num, Real.rpow_two, mul_comm] using h

/-- The second moment of `expMeasure 1` is `2`. -/
theorem integral_expMeasure_one_sq :
    ∫ x, x ^ 2 ∂(ProbabilityTheory.expMeasure 1) = 2 := by
  have hmeas : Measurable (ProbabilityTheory.gammaPDF 1 1) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.gammaPDF 1 1 x < ∞ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  have hpt : ∀ x : ℝ, (ProbabilityTheory.gammaPDF 1 1 x).toReal • (x ^ 2 : ℝ)
      = (Set.Ioi (0:ℝ)).indicator (fun y => y ^ 2 * Real.exp (-y)) x := by
    intro x
    rw [ProbabilityTheory.gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_one_one_nonneg x),
      smul_eq_mul, gammaPDFReal_one_one]
    by_cases hx : 0 < x
    · rw [if_pos hx.le, Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]
      ring
    · rcases lt_or_eq_of_le (not_lt.mp hx) with h | h
      · have hnot : x ∉ Set.Ioi (0:ℝ) := by
          simp only [Set.mem_Ioi, not_lt]
          linarith
        rw [if_neg (not_le.mpr h), Set.indicator_of_notMem hnot, zero_mul]
      · subst h
        rw [if_pos le_rfl, Set.indicator_of_notMem (by simp)]
        norm_num
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul hmeas hae]
  simp only [hpt]
  rw [integral_indicator measurableSet_Ioi]
  exact integral_exp_neg_mul_sq_self

/-- `∫₀^∞ e^{-r x} dx = 1/r` for `r > 0` (the `a = 1` case of the Gamma integral). -/
theorem integral_exp_neg_mul_Ioi {r : ℝ} (hr : 0 < r) :
    ∫ x in Set.Ioi (0:ℝ), Real.exp (-r * x) = r⁻¹ := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := r)
    (by norm_num) hr
  rw [Real.Gamma_one, mul_one] at h
  norm_num at h
  simpa [show (1:ℝ) - 1 = 0 by norm_num, Real.rpow_zero, one_mul] using h

/-- **The exponential moment of `expMeasure 1`**:
`∫ e^{x/n} ∂(expMeasure 1) = (1 - 1/n)⁻¹` for `n ≥ 2`. -/
theorem integral_expMeasure_exp (n : ℕ) (hn : 2 ≤ n) :
    ∫ x, Real.exp (x / n) ∂(ProbabilityTheory.expMeasure 1)
      = (1 - (1:ℝ) / n)⁻¹ := by
  have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < (1:ℝ) - 1 / n := by
    rw [sub_pos, div_lt_one hn0]
    exact hn1
  have hmeas : Measurable (ProbabilityTheory.gammaPDF 1 1) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.gammaPDF 1 1 x < ∞ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  have hpt : ∀ x : ℝ, (ProbabilityTheory.gammaPDF 1 1 x).toReal • Real.exp (x / n)
      = (Set.Ici (0:ℝ)).indicator (fun y => Real.exp (-y) * Real.exp (y / n)) x := by
    intro x
    rw [ProbabilityTheory.gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_one_one_nonneg x),
      smul_eq_mul, gammaPDFReal_one_one]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, Set.indicator_of_mem (Set.mem_Ici.mpr hx)]
    · rw [if_neg hx, Set.indicator_of_notMem (by simp [hx]), zero_mul]
  have hexp : ∀ y : ℝ, Real.exp (-y) * Real.exp (y / n)
      = Real.exp (-((1:ℝ) - 1 / n) * y) := by
    intro y
    rw [← Real.exp_add]
    ring_nf
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul hmeas hae]
  simp only [hpt]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  simp only [hexp]
  exact integral_exp_neg_mul_Ioi hr

/-- The exponential moment is integrable (`integral_undef` would force `0`). -/
theorem integrable_exp_expMeasure (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun x : ℝ => Real.exp (x / n)) (ProbabilityTheory.expMeasure 1) := by
  have h1 := integral_expMeasure_exp n hn
  by_contra h
  rw [integral_undef h] at h1
  have hpos : (0:ℝ) < (1 - (1:ℝ) / n)⁻¹ := by
    have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hr : 0 < (1:ℝ) - 1 / n := by
      rw [sub_pos, div_lt_one hn0]; exact hn1
    exact inv_pos.mpr hr
  linarith


end StrongMaximalEndpoint
