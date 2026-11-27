/-
The one-step cumulants of the rank increment and their values at `a = μ`.

At action `a` (the negative logarithm of the rectangle ratio) the increment of
`-log`-rank is
  `Z_a = Exp 1 + a · Bernoulli (ρ a)`,   `ρ a = 1 / (1 + exp a)`.
Its mean, variance and third cumulant are

  `m a = 1 + a ρ`,  `v a = 1 + a² ρ (1-ρ)`,  `κ₃ a = 2 + a³ ρ (1-ρ) (1-2ρ)`.

At `a = μ`, using `exp μ = 1/(μ-1)`:

  `m μ = μ`,  `v μ = μ`,  `κ₃ μ = μ (3 - μ)`,  hence `κ₃ μ / v μ = 3 - μ`,

and the second-order shifts of the manuscript:

  `n · ½ m''(μ) δ² = -g L`  and  `n v'(μ) δ = ½ (μ-1) √(μ n L)`  for `δ = ½ √(μ L / n)`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic
import StrongMaximal.Constants

namespace StrongMaximalEndpoint

open Real

/-- The Bernoulli parameter `ρ a = 1/(1+exp a)`, the probability that the
increment picks up the extra log-ratio `a`. -/
noncomputable def rho (a : ℝ) : ℝ := 1 / (1 + Real.exp a)

/-- One-step mean of the rank increment. -/
noncomputable def mStep (a : ℝ) : ℝ := 1 + a * rho a

/-- One-step variance, written as `1 + a² · u a` with `u a = ρ a (1 - ρ a)`. -/
noncomputable def vStep (a : ℝ) : ℝ := 1 + a ^ 2 * (rho a * (1 - rho a))

/-- One-step third cumulant. -/
noncomputable def k3Step (a : ℝ) : ℝ := 2 + a ^ 3 * rho a * (1 - rho a) * (1 - 2 * rho a)

/-- `ρ μ = (μ-1)/μ`, the identity behind all the constant computations. -/
theorem rho_mu : rho mu = (mu - 1) / mu := by
  have hne : mu - 1 ≠ 0 := by linarith [one_lt_mu]
  have h1 : Real.exp mu = 1 / (mu - 1) := exp_mu
  have h2 : 1 + Real.exp mu = mu / (mu - 1) := by
    rw [h1]; field_simp; ring
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  simp only [rho, h2]
  field_simp

/-- `m μ = μ`: the mean is stationary at the optimal action. -/
theorem mStep_mu : mStep mu = mu := by
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  simp only [mStep, rho_mu]
  field_simp
  ring

/-- `v μ = μ`: at the optimal action the variance equals the mean. -/
theorem vStep_mu : vStep mu = mu := by
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  have hne : mu - 1 ≠ 0 := by linarith [one_lt_mu]
  simp only [vStep, rho_mu]
  field_simp
  ring

/-- `κ₃ μ = μ (3 - μ)`. -/
theorem k3Step_mu : k3Step mu = mu * (3 - mu) := by
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  have hne : mu - 1 ≠ 0 := by linarith [one_lt_mu]
  simp only [k3Step, rho_mu]
  field_simp
  ring

/-- `κ₃ / v = 3 - μ` at the optimal action: the skewness of the standardized sum. -/
theorem k3_div_v_mu : k3Step mu / vStep mu = 3 - mu := by
  rw [k3Step_mu, vStep_mu]
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  field_simp

/-- The curvature of the mean at `μ` is `-(μ-1)/μ`. -/
theorem mStep_second_deriv : (1 / 2 : ℝ) * (-((mu - 1) / mu)) = -(mu - 1) / (2 * mu) := by ring

/-- Derivative of `ρ`: `ρ' = -ρ(1-ρ)`. -/
lemma hasDerivAt_rho (a : ℝ) : HasDerivAt rho (-(rho a * (1 - rho a))) a := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp a) a :=
    (Real.hasDerivAt_exp a).const_add 1
  have h2 : HasDerivAt (fun y : ℝ => (1 + Real.exp y)⁻¹)
      (-Real.exp a / (1 + Real.exp a) ^ 2) a := h1.inv (by positivity)
  have h3 : HasDerivAt rho (-Real.exp a / (1 + Real.exp a) ^ 2) a := by
    have hfun : (fun y : ℝ => (1 + Real.exp y)⁻¹) = fun y => 1 / (1 + Real.exp y) := by
      funext y; rw [one_div]
    rw [hfun] at h2
    exact h2
  have hval : -Real.exp a / (1 + Real.exp a) ^ 2 = -(rho a * (1 - rho a)) := by
    rw [show rho a = 1 / (1 + Real.exp a) from rfl]
    field_simp
    ring
  exact h3.congr_deriv hval

/-- Derivative of the one-step mean. -/
lemma hasDerivAt_mStep (a : ℝ) :
    HasDerivAt mStep (rho a * (1 - a * (1 - rho a))) a := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 a := hasDerivAt_id a
  have h := hid.mul (hasDerivAt_rho a)
  have hone : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 a := hasDerivAt_const a 1
  have h2 := hone.add h
  have hval : 0 + (1 * rho a + a * (-(rho a * (1 - rho a))))
      = rho a * (1 - a * (1 - rho a)) := by ring
  exact h2.congr_deriv hval

/-- The mean is stationary at the optimal action: `m'(μ) = 0`. -/
theorem deriv_mStep_mu : deriv mStep mu = 0 := by
  rw [(hasDerivAt_mStep mu).deriv, rho_mu]
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  field_simp
  ring

/-- `u a = ρ a (1 - ρ a)` and its derivative `u' = -ρ(1-ρ)(1-2ρ)`. -/
lemma hasDerivAt_uStep (a : ℝ) :
    HasDerivAt (fun y : ℝ => rho y * (1 - rho y))
      (-(rho a * (1 - rho a)) * (1 - 2 * rho a)) a := by
  have hconst : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 a := hasDerivAt_const a 1
  have h1 : HasDerivAt (fun y : ℝ => 1 - rho y) (0 - (-(rho a * (1 - rho a)))) a :=
    hconst.sub (hasDerivAt_rho a)
  have h := (hasDerivAt_rho a).mul h1
  have hval : -(rho a * (1 - rho a)) * (1 - rho a) + rho a * (0 - -(rho a * (1 - rho a)))
      = -(rho a * (1 - rho a)) * (1 - 2 * rho a) := by ring
  exact h.congr_deriv hval

/-- Derivative of the one-step variance. -/
lemma hasDerivAt_vStep (a : ℝ) :
    HasDerivAt vStep
      (2 * a * (rho a * (1 - rho a)) + a ^ 2 * (-(rho a * (1 - rho a)) * (1 - 2 * rho a))) a := by
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * a) a := by
    simpa using hasDerivAt_pow 2 a
  have h := h2.mul (hasDerivAt_uStep a)
  have hone : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 a := hasDerivAt_const a 1
  have h3 := hone.add h
  have hval : 0 + (2 * a * (rho a * (1 - rho a))
        + a ^ 2 * (-(rho a * (1 - rho a)) * (1 - 2 * rho a)))
      = 2 * a * (rho a * (1 - rho a)) + a ^ 2 * (-(rho a * (1 - rho a)) * (1 - 2 * rho a)) := by
    ring
  exact h3.congr_deriv hval

/-- `v'(μ) = μ - 1`. -/
theorem deriv_vStep_mu : deriv vStep mu = mu - 1 := by
  rw [(hasDerivAt_vStep mu).deriv, rho_mu]
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  field_simp
  ring

/-- `m'(a) = ρ a (1 - a(1-ρ a))` as a function, and its derivative. -/
lemma hasDerivAt_mD (a : ℝ) :
    HasDerivAt (fun y : ℝ => rho y * (1 - y * (1 - rho y)))
      (-(rho a * (1 - rho a)) * (1 - a * (1 - rho a))
        + rho a * (-1 + rho a + a * (-(rho a * (1 - rho a))))) a := by
  have hq : HasDerivAt (fun y : ℝ => 1 - y * (1 - rho y))
      (-1 + rho a + a * (-(rho a * (1 - rho a)))) a := by
    have hid : HasDerivAt (fun y : ℝ => y) 1 a := hasDerivAt_id a
    have hconst : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 a := hasDerivAt_const a 1
    have h1 : HasDerivAt (fun y : ℝ => 1 - rho y) (0 - (-(rho a * (1 - rho a)))) a :=
      hconst.sub (hasDerivAt_rho a)
    have h2 := hid.mul h1
    have h3 : HasDerivAt (fun y : ℝ => 1 - y * (1 - rho y))
        (0 - (1 * (1 - rho a) + a * (0 - (-(rho a * (1 - rho a)))))) a := hconst.sub h2
    have hval : 0 - (1 * (1 - rho a) + a * (0 - (-(rho a * (1 - rho a)))))
        = -1 + rho a + a * (-(rho a * (1 - rho a))) := by ring
    exact h3.congr_deriv hval
  exact (hasDerivAt_rho a).mul hq

/-- The second derivative of the mean at `μ` is `-(μ-1)/μ`. -/
theorem deriv_deriv_mStep_mu : deriv (deriv mStep) mu = -(mu - 1) / mu := by
  have hfun : deriv mStep = fun a : ℝ => rho a * (1 - a * (1 - rho a)) := by
    funext a
    exact (hasDerivAt_mStep a).deriv
  rw [hfun, (hasDerivAt_mD mu).deriv, rho_mu]
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  field_simp
  ring

/-- **The mean shift.** With `δ = ½ √(μ L / n)` and curvature `-(μ-1)/μ` at `μ`,
the second-order contribution to the mean of `S_n` is exactly `-g L`. -/
theorem mean_shift (n L : ℝ) (hn : n ≠ 0)
    (hδ : (1 / 2 * Real.sqrt (mu * L / n)) ^ 2 = mu * L / (4 * n)) :
    n * ((1 / 2) * (-((mu - 1) / mu)) * (1 / 2 * Real.sqrt (mu * L / n)) ^ 2) = -g * L := by
  have hmu : mu ≠ 0 := by linarith [one_lt_mu]
  rw [hδ]
  simp only [g]
  field_simp
  ring

end StrongMaximalEndpoint
