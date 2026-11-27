/-
The centering `dₙ = √(μn) zₙ` of the v1 manuscript, where `zₙ > 0` is the unique
solution of `Φ̄ zₙ = √(μ/n) zₙ`, `Φ̄` the standard normal upper tail.

`Φ̄` is defined as `1/2 - ∫_0^z φ`, which is what the fundamental theorem of
calculus makes differentiable; `gaussTail_eq_setIntegral` identifies it with
`∫_{x > z} φ`.  From the derivative `Φ̄' = -φ < 0` we get strict antitonicity,
hence existence and uniqueness of the root for every `n ≥ 2`.

Not proved here (see `report.md`): the two-sided Mills bounds and the resulting
`zₙ ^ 2 / log n → 1`.  `StrengMaximal.SecondOrder` isolates the limit it needs.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import StrongMaximal.Constants

namespace StrongMaximalEndpoint

open Filter Topology MeasureTheory
open scoped Real Topology Interval

/-! ### The standard normal density and tail -/

/-- The standard normal density `φ(x) = (√(2π))⁻¹ exp (-x²/2)`. -/
noncomputable def gaussPhi (x : ℝ) : ℝ := (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2) * x ^ 2)

lemma sqrt_two_pi_pos : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
lemma gaussPhi_pos (x : ℝ) : 0 < gaussPhi x := by unfold gaussPhi; positivity
lemma gaussPhi_nonneg (x : ℝ) : 0 ≤ gaussPhi x := (gaussPhi_pos x).le
lemma gaussPhi_continuous : Continuous gaussPhi := by unfold gaussPhi; fun_prop
lemma inv_sqrt_two_pi_pos : 0 < (Real.sqrt (2 * π))⁻¹ := inv_pos.mpr sqrt_two_pi_pos

lemma gaussPhi_hasDerivAt (x : ℝ) : HasDerivAt gaussPhi (-(x * gaussPhi x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(1 / 2) * y ^ 2) (-(1 / 2) * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul (-(1/2) : ℝ)
  have h2 : HasDerivAt (fun y : ℝ => (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2) * y ^ 2))
      ((Real.sqrt (2 * π))⁻¹ * (Real.exp (-(1 / 2) * x ^ 2) * (-(1 / 2) * (2 * x)))) x :=
    h1.exp.const_mul _
  have hval : (Real.sqrt (2 * π))⁻¹ * (Real.exp (-(1 / 2) * x ^ 2) * (-(1 / 2) * (2 * x)))
      = -(x * gaussPhi x) := by unfold gaussPhi; ring
  rw [hval] at h2
  exact h2

/-- The upper tail `Φ̄ z = 1/2 - ∫_0^z φ`; see `gaussTail_eq_setIntegral`. -/
noncomputable def gaussTail (z : ℝ) : ℝ := 1 / 2 - ∫ u in (0:ℝ)..z, gaussPhi u

theorem gaussTail_zero : gaussTail 0 = 1 / 2 := by simp [gaussTail]

theorem continuous_gaussTail_primitive :
    Continuous (fun z : ℝ => ∫ u in (0:ℝ)..z, gaussPhi u) :=
  continuous_iff_continuousAt.mpr fun z =>
    (intervalIntegral.integral_hasDerivAt_right (a := (0:ℝ))
      (gaussPhi_continuous.intervalIntegrable _ _)
      (gaussPhi_continuous.stronglyMeasurableAtFilter volume (𝓝 z))
      gaussPhi_continuous.continuousAt).continuousAt

theorem continuous_gaussTail : Continuous gaussTail :=
  continuous_const.sub continuous_gaussTail_primitive

theorem hasDerivAt_gaussTail (z : ℝ) : HasDerivAt gaussTail (-(gaussPhi z)) z := by
  have h := intervalIntegral.integral_hasDerivAt_right (a := (0:ℝ))
    (gaussPhi_continuous.intervalIntegrable _ _)
    (gaussPhi_continuous.stronglyMeasurableAtFilter volume (𝓝 z))
    gaussPhi_continuous.continuousAt
  exact h.const_sub (1/2 : ℝ)

/-- `Φ̄` is strictly decreasing. -/
theorem gaussTail_lt_of_lt {x y : ℝ} (hxy : x < y) : gaussTail y < gaussTail x := by
  have h2 : ∫ u in (0:ℝ)..y, gaussPhi u
      = (∫ u in (0:ℝ)..x, gaussPhi u) + ∫ u in x..y, gaussPhi u := by
    rw [eq_comm, intervalIntegral.integral_add_adjacent_intervals
      (gaussPhi_continuous.intervalIntegrable _ _)
      (gaussPhi_continuous.intervalIntegrable _ _)]
  have hpos : 0 < ∫ u in x..y, gaussPhi u :=
    intervalIntegral.integral_pos hxy gaussPhi_continuous.continuousOn
      (fun u _ => gaussPhi_nonneg u) ⟨y, ⟨hxy.le, le_rfl⟩, gaussPhi_pos y⟩
  have hdiff : gaussTail x - gaussTail y = ∫ u in x..y, gaussPhi u := by
    simp only [gaussTail]; linarith
  rw [← hdiff] at hpos
  linarith

lemma gaussTail_le_half (z : ℝ) (hz : 0 ≤ z) : gaussTail z ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h, gaussTail_zero]
  · have := gaussTail_lt_of_lt h
    rw [gaussTail_zero] at this; linarith

/-! ### The centering `dₙ` -/

/-- The function whose positive root defines `zₙ`. -/
noncomputable def zFun (n : ℕ) (z : ℝ) : ℝ := gaussTail z - Real.sqrt (mu / n) * z

lemma zFun_continuous (n : ℕ) : Continuous (zFun n) :=
  continuous_gaussTail.sub (continuous_const.mul continuous_id)

lemma zFun_strictAnti (n : ℕ) : StrictAnti (zFun n) := by
  intro x y hxy
  have h1 : gaussTail y < gaussTail x := gaussTail_lt_of_lt hxy
  have h2 : Real.sqrt (mu / n) * x ≤ Real.sqrt (mu / n) * y :=
    mul_le_mul_of_nonneg_left hxy.le (Real.sqrt_nonneg _)
  simp only [zFun]; linarith

lemma zFun_zero (n : ℕ) : zFun n 0 = 1 / 2 := by simp [zFun, gaussTail_zero]

lemma zFun_nonpos_of (n : ℕ) (Z : ℝ) (hZ : 1 / 2 ≤ Real.sqrt (mu / n) * Z) :
    zFun n Z ≤ 0 := by
  have hZnn : 0 ≤ Z := by
    by_contra h
    push_neg at h
    have hc0 : 0 ≤ Real.sqrt (mu / n) := Real.sqrt_nonneg _
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc0 h.le]
  have hle : gaussTail Z ≤ 1 / 2 := gaussTail_le_half Z hZnn
  simp only [zFun]; linarith

/-- Existence and uniqueness of the positive root of `Φ̄ z = √(μ/n) z`, `n ≥ 2`. -/
theorem existsUnique_zOf (n : ℕ) (hn : 2 ≤ n) :
    ∃! z : ℝ, 0 < z ∧ gaussTail z = Real.sqrt (mu / n) * z := by
  have hc : 0 < Real.sqrt (mu / n) :=
    Real.sqrt_pos.mpr (div_pos (by linarith [one_lt_mu]) (by positivity))
  set Z : ℝ := 1 / (2 * Real.sqrt (mu / n)) + 1 with hZdef
  have hZpos : 0 < Z := by positivity
  have hhalf : 1 / 2 ≤ Real.sqrt (mu / n) * Z := by
    rw [hZdef]
    have h1 : Real.sqrt (mu / n) * (1 / (2 * Real.sqrt (mu / n))) = 1 / 2 := by
      field_simp
    nlinarith [mul_pos hc (by norm_num : (0:ℝ) < 1), h1]
  have hZneg : zFun n Z ≤ 0 := zFun_nonpos_of n Z hhalf
  have hZpos' : 0 < zFun n 0 := by rw [zFun_zero]; norm_num
  have hcont : ContinuousOn (zFun n) (Set.Icc 0 Z) := (zFun_continuous n).continuousOn
  have hmem : (0:ℝ) ∈ Set.Icc (zFun n Z) (zFun n 0) := ⟨hZneg, hZpos'.le⟩
  obtain ⟨z, hz_mem, hz⟩ := intermediate_value_Icc' hZpos.le hcont hmem
  have hzpos : 0 < z := by
    rcases eq_or_lt_of_le hz_mem.1 with h | h
    · rw [← h] at hz; linarith
    · exact h
  have hzspec : gaussTail z = Real.sqrt (mu / n) * z := by
    have := hz; simp only [zFun] at this; linarith
  refine ⟨z, ⟨hzpos, hzspec⟩, ?_⟩
  intro w hw
  by_contra hne
  have hwspec : gaussTail w = Real.sqrt (mu / n) * w := hw.2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h := zFun_strictAnti n hlt
    simp only [zFun] at h
    rw [← hw.2, ← hzspec] at h
    linarith
  · have h := zFun_strictAnti n hlt
    simp only [zFun] at h
    rw [← hw.2, ← hzspec] at h
    linarith

/-- `zₙ`, the unique positive root, defined for every `n` (zero off `n ≥ 2`). -/
noncomputable def zOf (n : ℕ) : ℝ :=
  if h : 2 ≤ n then Classical.choose (existsUnique_zOf n h) else 0

lemma zOf_pos {n : ℕ} (hn : 2 ≤ n) : 0 < zOf n := by
  unfold zOf; rw [dif_pos hn]
  exact (Classical.choose_spec (existsUnique_zOf n hn)).1.1

lemma zOf_spec {n : ℕ} (hn : 2 ≤ n) :
    gaussTail (zOf n) = Real.sqrt (mu / n) * zOf n := by
  unfold zOf; rw [dif_pos hn]
  exact (Classical.choose_spec (existsUnique_zOf n hn)).1.2

/-- The centering `dₙ = √(μn) zₙ` of the manuscript. -/
noncomputable def dOf (n : ℕ) : ℝ := Real.sqrt (mu * n) * zOf n

/-- `dₙ` is the value of the tail at its own root: `dₙ = n Φ̄(zₙ)`. -/
theorem dOf_eq {n : ℕ} (hn : 2 ≤ n) : dOf n = (n : ℝ) * gaussTail (zOf n) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hkey : Real.sqrt (mu * n) = (n:ℝ) * Real.sqrt (mu / (n:ℝ)) := by
    rw [show mu * (n:ℝ) = (n:ℝ)^2 * (mu / (n:ℝ)) by field_simp]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hn'.le]
  rw [dOf, zOf_spec hn, hkey]; ring
/-- Splitting at a point: `Φ̄ a = ∫_{a..b} φ + Φ̄ b` for `a ≤ b`. -/
theorem gaussTail_split {a b : ℝ} (hab : a ≤ b) :
    gaussTail a = (∫ u in a..b, gaussPhi u) + gaussTail b := by
  have h2 : ∫ u in (0:ℝ)..b, gaussPhi u
      = (∫ u in (0:ℝ)..a, gaussPhi u) + ∫ u in a..b, gaussPhi u := by
    rw [eq_comm, intervalIntegral.integral_add_adjacent_intervals
      (gaussPhi_continuous.intervalIntegrable _ _)
      (gaussPhi_continuous.intervalIntegrable _ _)]
  have hdiff : gaussTail a - gaussTail b = ∫ u in a..b, gaussPhi u := by
    simp only [gaussTail]; linarith
  rw [← hdiff]
  ring

end StrongMaximalEndpoint
