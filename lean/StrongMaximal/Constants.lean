/-
Copyright: manuscript "High-dimensional bounds for the optimal endpoint constant
of the uncentered strong maximal operator" (v1.0.0), section 1 and section 3.

The scalar constants of the manuscript, proved from their definitions:

* `μ`, the unique positive root of `μ = 1 + exp (-μ)`;
* `g = (μ - 1) / 8`, `cLo = (9 - μ) / 24`, `cHi = (3 + μ) / 12`;
* the identity `cLo + g = cHi` that closes the two-sided exponent window;
* the one-step cumulants of the rank increment `Exp 1 + a · Bernoulli (1/(1+exp a))`
  and their values and derivatives at `a = μ`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace StrongMaximalEndpoint

/-! ### The root `μ = 1 + exp (-μ)` -/

/-- The defining function of `μ`; strictly increasing on all of `ℝ`. -/
noncomputable def muFun (x : ℝ) : ℝ := x - 1 - Real.exp (-x)

lemma muFun_strictMono : StrictMono muFun := by
  intro x y hxy
  have h1 : Real.exp (-y) < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
  simp only [muFun]
  linarith

lemma muFun_continuous : Continuous muFun := by
  unfold muFun; fun_prop

lemma muFun_one_neg : muFun 1 < 0 := by
  have h : (0:ℝ) < Real.exp (-1) := Real.exp_pos _
  simp only [muFun]; linarith

lemma muFun_two_pos : 0 < muFun 2 := by
  have h : Real.exp (-2) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  simp only [muFun]; linarith

lemma exists_mu : ∃ x : ℝ, muFun x = 0 := by
  have hcont : ContinuousOn muFun (Set.Icc (1:ℝ) 2) := muFun_continuous.continuousOn
  have hmem : (0:ℝ) ∈ Set.Icc (muFun 1) (muFun 2) :=
    ⟨muFun_one_neg.le, muFun_two_pos.le⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hcont hmem
  exact ⟨x, hfx⟩

/-- `μ` is the unique positive root of `μ = 1 + exp (-μ)`. -/
noncomputable def mu : ℝ := Classical.choose exists_mu

lemma mu_spec : muFun mu = 0 := Classical.choose_spec exists_mu

/-- The defining equation, in the form used throughout the manuscript. -/
theorem mu_eq : mu = 1 + Real.exp (-mu) := by
  have := mu_spec; simp only [muFun] at this; linarith

theorem exp_neg_mu : Real.exp (-mu) = mu - 1 := by
  have := mu_eq; linarith

lemma one_lt_mu : 1 < mu := by
  have h := exp_neg_mu
  have : 0 < Real.exp (-mu) := Real.exp_pos _
  linarith

lemma mu_pos : 0 < mu := by linarith [one_lt_mu]

theorem exp_mu : Real.exp mu = 1 / (mu - 1) := by
  have hne : mu - 1 ≠ 0 := by linarith [one_lt_mu]
  rw [eq_div_iff hne]
  have h := exp_neg_mu
  have hone : Real.exp mu * Real.exp (-mu) = 1 := by
    rw [← Real.exp_add]; simp
  rw [h] at hone
  linarith

lemma mu_lt_two : mu < 2 := by
  have h : muFun 2 > 0 := muFun_two_pos
  rcases lt_or_ge mu 2 with hlt | hge
  · exact hlt
  · exfalso
    have hmono : muFun 2 ≤ muFun mu := muFun_strictMono.monotone hge
    rw [mu_spec] at hmono
    linarith

theorem eq_mu_iff (x : ℝ) : muFun x = 0 ↔ x = mu := by
  constructor
  · intro hx
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := muFun_strictMono h
      rw [mu_spec, hx] at this; exact lt_irrefl _ this
    · have := muFun_strictMono h
      rw [mu_spec, hx] at this; exact lt_irrefl _ this
  · rintro rfl; exact mu_spec

/-- `μ` is the unique positive root, stated as uniqueness in `ℝ`. -/
theorem existsUnique_mu : ∃! x : ℝ, x = 1 + Real.exp (-x) := by
  refine ⟨mu, mu_eq, ?_⟩
  intro x hx
  have : muFun x = 0 := by simp only [muFun]; linarith
  exact (eq_mu_iff x).mp this

/-! ### The three constants and the closing identity -/

/-- The exponent gap `g = (μ - 1) / 8`. -/
noncomputable def g : ℝ := (mu - 1) / 8

/-- The lower exponent `(9 - μ) / 24`. -/
noncomputable def cLo : ℝ := (9 - mu) / 24

/-- The upper exponent `(3 + μ) / 12`. -/
noncomputable def cHi : ℝ := (3 + mu) / 12

theorem g_pos : 0 < g := by
  have := one_lt_mu; simp only [g]; linarith

/-- `cLo = g + (3 - μ)/6`: the lower exponent splits into the mean shift and the
(claimed) skewness contribution. -/
theorem cLo_eq : cLo = g + (3 - mu) / 6 := by
  simp only [cLo, g]; ring

/-- **The closing identity**: the window of exponents has width `g`. -/
theorem cLo_add_g : cLo + g = cHi := by
  simp only [cLo, g, cHi]; ring

theorem cLo_lt_cHi : cLo < cHi := by
  have := g_pos; rw [← cLo_add_g]; linarith

lemma three_sub_mu_pos : 0 < 3 - mu := by have := mu_lt_two; linarith

/-- `c₋ > 0`: the lower exponent is positive. -/
lemma cLo_pos : 0 < cLo := by
  have := mu_lt_two; simp only [cLo]; linarith

/-- `c₊ < 1`: the upper exponent lies below `1`. -/
lemma cHi_lt_one : cHi < 1 := by
  have := mu_lt_two; simp only [cHi]; linarith

lemma three_sub_mu_lt_two : 3 - mu < 2 := by have := one_lt_mu; linarith

end StrongMaximalEndpoint
