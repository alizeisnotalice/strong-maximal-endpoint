/-
The exponential moment of one increment, `E[e^{Z_a/n}]`, and its finiteness.

  `E[e^{Z_a/n}] = (1 - 1/n)⁻¹ · (ρ(a) e^{a/n} + 1 - ρ(a))`   (`n ≥ 2`).

This is the integrability input of the integrated plateau inequality
`Hw_integral_ge`, applied to the model `Sₙ`.
-/
import StrongMaximal.NStepModel
import StrongMaximal.Variance
import StrongMaximal.ExpModel

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

/-- `e^{Z/n} = e^{X/n} · e^{a·B/n}`. -/
theorem exp_stepIncr_eq (n : ℕ) (a : ℝ) (ω : ℝ × Bool) :
    Real.exp (stepIncr a ω / n)
      = Real.exp (ω.1 / n) * Real.exp (a * (if ω.2 then (1:ℝ) else 0) / n) := by
  rw [stepIncr_eq, add_div, Real.exp_add]
  rfl

/-- **The exponential moment of `Z_a`**. -/
theorem integral_exp_stepIncr (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    ∫ ω, Real.exp (stepIncr a ω / n) ∂(stepLaw a)
      = (1 - (1:ℝ) / n)⁻¹ * (rho a * Real.exp (a / n) + (1 - rho a)) := by
  haveI hμ : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  haveI hν : IsProbabilityMeasure
      (ProbabilityTheory.bernoulliMeasure true false (rhoI a)) := inferInstance
  rw [stepLaw_def]
  have hexp : ∀ ω : ℝ × Bool, Real.exp (stepIncr a ω / n)
      = Real.exp (ω.1 / n) * Real.exp (a * (if ω.2 then (1:ℝ) else 0) / n) :=
    exp_stepIncr_eq n a
  simp only [hexp]
  have h := integral_prod_mul (μ := ProbabilityTheory.expMeasure 1)
    (ν := ProbabilityTheory.bernoulliMeasure true false (rhoI a))
    (f := fun x : ℝ => Real.exp (x / n))
    (g := fun b : Bool => Real.exp (a * (if b then (1:ℝ) else 0) / n))
  rw [h, integral_expMeasure_exp n hn, ProbabilityTheory.integral_bernoulliMeasure]
  simp [mul_comm, add_comm]

/-- The exponential moment is integrable (`integral_undef` would force `0`). -/
theorem integrable_exp_stepIncr (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    Integrable (fun ω : ℝ × Bool => Real.exp (stepIncr a ω / n)) (stepLaw a) := by
  have h1 := integral_exp_stepIncr n hn a
  by_contra h
  rw [integral_undef h] at h1
  have hpos : (0:ℝ) < (1 - (1:ℝ) / n)⁻¹ := by
    have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hr : 0 < (1:ℝ) - 1 / n := by
      rw [sub_pos, div_lt_one hn0]; exact hn1
    exact inv_pos.mpr hr
  have h2 : 0 < rho a * Real.exp (a / n) + (1 - rho a) := by
    have h3 : 0 ≤ Real.exp (a / n) := (Real.exp_pos _).le
    have h4 : 0 < rho a := by unfold rho; positivity
    have h5 : rho a < 1 := by
      unfold rho
      rw [div_lt_one (by positivity)]
      linarith [Real.exp_pos a]
    nlinarith [mul_nonneg h3 h4.le]
  nlinarith [mul_pos hpos h2]
/-- `e^{Sₙ/n} = ∏_{i<n} e^{Z_a(i)/n}`. -/
theorem exp_nIncr_eq (n : ℕ) (a : ℝ) (ω : Fin n → ℝ × Bool) :
    Real.exp (nIncr n a ω / n)
      = ∏ i : Fin n, Real.exp (stepIncr a (ω i) / n) := by
  rw [nIncr, Finset.sum_div, Real.exp_sum]

/-- **The exponential moment of `Sₙ`** is the `n`-th power of the one-step moment. -/
theorem integral_exp_nIncr (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    ∫ ω : Fin n → ℝ × Bool, Real.exp (nIncr n a ω / n) ∂(nStepLaw n a)
      = ((1 - (1:ℝ) / n)⁻¹ * (rho a * Real.exp (a / n) + (1 - rho a))) ^ n := by
  rw [nStepLaw_def]
  haveI : IsProbabilityMeasure (stepLaw a) := isProbabilityMeasure_stepLaw a
  have h : ∀ ω : Fin n → ℝ × Bool,
      Real.exp (nIncr n a ω / n) = ∏ i : Fin n, Real.exp (stepIncr a (ω i) / n) :=
    exp_nIncr_eq n a
  simp only [h]
  rw [integral_fintype_prod_eq_pow
    (f := fun ω : ℝ × Bool => Real.exp (stepIncr a ω / n)), integral_exp_stepIncr n hn a]
  simp [Fintype.card_fin]

/-- The `n`-fold exponential moment is integrable. -/
theorem integrable_exp_nIncr (n : ℕ) (hn : 2 ≤ n) (a : ℝ) :
    Integrable (fun ω : Fin n → ℝ × Bool => Real.exp (nIncr n a ω / n)) (nStepLaw n a) := by
  have h1 := integral_exp_nIncr n hn a
  by_contra h
  rw [integral_undef h] at h1
  have hpos : (0:ℝ) < (1 - (1:ℝ) / n)⁻¹ := by
    have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hr : 0 < (1:ℝ) - 1 / n := by
      rw [sub_pos, div_lt_one hn0]; exact hn1
    exact inv_pos.mpr hr
  have h2 : 0 < rho a * Real.exp (a / n) + (1 - rho a) := by
    have h3 : 0 ≤ Real.exp (a / n) := (Real.exp_pos _).le
    have h4 : 0 < rho a := by unfold rho; positivity
    have h5 : rho a < 1 := by
      unfold rho
      rw [div_lt_one (by positivity)]
      linarith [Real.exp_pos a]
    nlinarith [mul_nonneg h3 h4.le]
  have h3 : 0 < ((1 - (1:ℝ) / n)⁻¹ * (rho a * Real.exp (a / n) + (1 - rho a))) ^ n :=
    pow_pos (mul_pos hpos h2) n
  linarith


end StrongMaximalEndpoint
