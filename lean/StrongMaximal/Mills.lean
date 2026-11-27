/-
Two-sided Mills bounds for the standard normal tail, and the resulting
asymptotics of `zₙ`.

Both bounds are obtained by comparing derivatives, so no integration by parts
and no improper-integral identity beyond `∫_{x>0} φ = 1/2` is needed:

* `z ↦ Φ̄ z - φ z / z` has derivative `φ z / z² > 0` and limit `0` at `+∞`,
  hence `Φ̄ z ≤ φ z / z`;
* `z ↦ Φ̄ z - e⁻² φ z / z` has derivative `φ z (e⁻² - 1 + e⁻²/z²) < 0` on
  `z ≥ 1` and limit `0`, hence `e⁻² φ z / z ≤ Φ̄ z`.

The constant `e⁻²` is deliberately non-sharp; only its positivity is used.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import StrongMaximal.Gaussian

namespace StrongMaximalEndpoint

set_option maxHeartbeats 1200000

open Filter Topology MeasureTheory
open scoped Real Topology Interval

/-! ### The total mass on `(0, ∞)` -/

lemma integrable_gaussPhi : Integrable gaussPhi :=
  (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul _

/-- `∫_{x>0} φ = 1/2`. -/
theorem integral_Ioi_gaussPhi : ∫ x in Set.Ioi (0:ℝ), gaussPhi x = 1 / 2 := by
  unfold gaussPhi
  rw [integral_const_mul, integral_gaussian_Ioi (1/2)]
  have hpi : Real.sqrt (π / (1/2)) = Real.sqrt (2 * π) := by
    norm_num [div_eq_mul_inv, mul_comm]
  rw [hpi]
  have hne : Real.sqrt (2 * π) ≠ 0 := ne_of_gt sqrt_two_pi_pos
  field_simp

/-- `z ↦ ∫_0^z φ` is monotone. -/
theorem monotone_primitive_gaussPhi :
    Monotone (fun z : ℝ => ∫ x in (0:ℝ)..z, gaussPhi x) := by
  intro x y hxy
  have h1 : ∫ u in (0:ℝ)..y, gaussPhi u
      = (∫ u in (0:ℝ)..x, gaussPhi u) + ∫ u in x..y, gaussPhi u := by
    rw [eq_comm, intervalIntegral.integral_add_adjacent_intervals
      (gaussPhi_continuous.intervalIntegrable _ _)
      (gaussPhi_continuous.intervalIntegrable _ _)]
  have h2 : 0 ≤ ∫ u in x..y, gaussPhi u :=
    intervalIntegral.integral_nonneg_of_forall hxy (fun u => gaussPhi_nonneg u)
  linarith

/-- `∫_0^z φ → 1/2`. -/
theorem tendsto_primitive_gaussPhi :
    Tendsto (fun z : ℝ => ∫ x in (0:ℝ)..z, gaussPhi x) atTop (𝓝 (1 / 2)) := by
  have hmono : Monotone (fun z : ℝ => Set.Ioc (0:ℝ) z) :=
    fun a b hab => Set.Ioc_subset_Ioc_right hab
  have hunion : (⋃ z : ℝ, Set.Ioc (0:ℝ) z) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨z, h1, _⟩; exact h1
    · intro h; exact ⟨x, h, le_rfl⟩
  have hint : IntegrableOn gaussPhi (⋃ z : ℝ, Set.Ioc (0:ℝ) z) := by
    rw [hunion]; exact integrable_gaussPhi.integrableOn
  have h : Tendsto (fun z : ℝ => ∫ x in Set.Ioc (0:ℝ) z, gaussPhi x) atTop
      (𝓝 (∫ x in ⋃ n : ℝ, Set.Ioc (0:ℝ) n, gaussPhi x)) :=
    tendsto_setIntegral_of_monotone (μ := volume) (s := fun z : ℝ => Set.Ioc (0:ℝ) z)
      (fun z => measurableSet_Ioc) hmono hint
  rw [hunion, integral_Ioi_gaussPhi] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with z hz
  exact (intervalIntegral.integral_of_le (f := gaussPhi) (μ := volume) hz).symm

/-- `Φ̄ z → 0`. -/
theorem tendsto_gaussTail_atTop : Tendsto gaussTail atTop (𝓝 0) := by
  have h : Tendsto (fun z : ℝ => (1:ℝ)/2 - ∫ x in (0:ℝ)..z, gaussPhi x) atTop
      (𝓝 ((1:ℝ)/2 - 1/2)) := tendsto_const_nhds.sub tendsto_primitive_gaussPhi
  rw [sub_self] at h
  exact h

/-- `Φ̄ ≥ 0`. -/
theorem gaussTail_nonneg (z : ℝ) : 0 ≤ gaussTail z := by
  have hlim := tendsto_primitive_gaussPhi
  have hmono := monotone_primitive_gaussPhi
  rcases le_or_gt 0 z with hz | hz
  · have hzle : (∫ x in (0:ℝ)..z, gaussPhi x) ≤ 1 / 2 := by
      refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
      filter_upwards [eventually_ge_atTop z] with w hw
      exact hmono hw
    simp only [gaussTail]; linarith
  · have h := gaussTail_lt_of_lt hz
    rw [gaussTail_zero] at h
    linarith

/-- `φ → 0` at `+∞`. -/
theorem tendsto_gaussPhi_atTop : Tendsto gaussPhi atTop (𝓝 0) := by
  have hb : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hupper : Tendsto (fun x : ℝ => (Real.sqrt (2 * π))⁻¹ * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using hb.const_mul ((Real.sqrt (2 * π))⁻¹)
  refine squeeze_zero_norm' ?_ hupper
  filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (gaussPhi_pos x)]
  have h1 : Real.exp (-(1 / 2) * x ^ 2) ≤ Real.exp (-x) := by
    rw [Real.exp_le_exp]; nlinarith
  calc gaussPhi x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2) * x ^ 2) := rfl
    _ ≤ (Real.sqrt (2 * π))⁻¹ * Real.exp (-x) :=
        mul_le_mul_of_nonneg_left h1 inv_sqrt_two_pi_pos.le

theorem tendsto_gaussPhi_div_atTop : Tendsto (fun z : ℝ => gaussPhi z / z) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => (1:ℝ) / z) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
  have h := tendsto_gaussPhi_atTop.mul h1
  simpa [div_eq_mul_inv, mul_comm] using h

/-! ### The two Mills bounds -/

/-- Upper Mills bound `Φ̄ z ≤ φ z / z`: `z ↦ Φ̄ z - φ z/z` has derivative
`φ z/z² > 0` and limit `0`. -/
theorem gaussTail_le_div (hz : 0 < z) : gaussTail z ≤ gaussPhi z / z := by
  set F : ℝ → ℝ := fun t => gaussTail t - gaussPhi t / t with hF
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt F (gaussPhi t / t ^ 2) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => gaussPhi s / s)
        ((-(t * gaussPhi t) * t - gaussPhi t * 1) / t ^ 2) t :=
      (gaussPhi_hasDerivAt t).div (hasDerivAt_id t) ht.ne'
    have h2 : HasDerivAt F (gaussPhi t / t ^ 2) t := by
      have h3 := (hasDerivAt_gaussTail t).sub h1
      convert h3 using 1
      field_simp
      ring
    simpa [hF] using h2
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => gaussTail t) atTop (𝓝 0) := tendsto_gaussTail_atTop
    have h2 : Tendsto (fun t : ℝ => gaussPhi t / t) atTop (𝓝 0) := tendsto_gaussPhi_div_atTop
    simpa [hF] using h1.sub h2
  have hcont : ∀ y : ℝ, z ≤ y → ContinuousOn F (Set.Icc z y) := by
    intro y _
    have hdiv : ContinuousOn (fun t : ℝ => gaussPhi t / t) (Set.Icc z y) := by
      refine ContinuousOn.div gaussPhi_continuous.continuousOn continuous_id.continuousOn ?_
      intro t ht
      exact (lt_of_lt_of_le hz ht.1).ne'
    exact continuous_gaussTail.continuousOn.sub hdiv
  have hmono : ∀ y : ℝ, z ≤ y → F z ≤ F y := by
    intro y hzy
    rcases eq_or_lt_of_le hzy with h | h
    · rw [← h]
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F (fun t => gaussPhi t / t ^ 2)
        h (hcont y hzy) (fun t ht => hderiv t (lt_of_lt_of_le hz ht.1.le))
      have hc0 : 0 < c := lt_of_lt_of_le hz hc.1.le
      have hpos : 0 < gaussPhi c / c ^ 2 := div_pos (gaussPhi_pos c) (pow_pos hc0 2)
      have hyz : 0 < y - z := by linarith
      have hq : 0 < (F y - F z) / (y - z) := by rw [← hslope]; exact hpos
      rcases div_pos_iff.mp hq with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · linarith
  have hF0 : F z ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [eventually_ge_atTop z] with y hy
    exact hmono y hy
  simpa [hF] using hF0

/-- Lower Mills bound `e⁻² φ z / z ≤ Φ̄ z` for `z ≥ 1`: `z ↦ Φ̄ z - e⁻²φ z/z`
has derivative `φ z (e⁻² - 1 + e⁻²/z²) ≤ -φ z/3 < 0` there and limit `0`. -/
theorem gaussTail_ge_div (hz : 1 ≤ z) :
    Real.exp (-2) * gaussPhi z / z ≤ gaussTail z := by
  set G : ℝ → ℝ := fun t => gaussTail t - Real.exp (-2) * (gaussPhi t / t) with hG
  have hexp2 : Real.exp (-2) ≤ 1 / 3 := by
    have h3 : (3:ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp 2
      linarith
    rw [Real.exp_neg, show (1:ℝ)/3 = 3⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) h3
  have hexp2pos : 0 < Real.exp (-2) := Real.exp_pos _
  have hderiv : ∀ t : ℝ, 1 ≤ t →
      HasDerivAt G (gaussPhi t * (Real.exp (-2) - 1 + Real.exp (-2) / t ^ 2)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => gaussPhi s / s)
        ((-(t * gaussPhi t) * t - gaussPhi t * 1) / t ^ 2) t :=
      (gaussPhi_hasDerivAt t).div (hasDerivAt_id t) (by positivity)
    have h2 := (hasDerivAt_gaussTail t).sub (h1.const_mul (Real.exp (-2)))
    have hval : -(gaussPhi t) - Real.exp (-2) * ((-(t * gaussPhi t) * t - gaussPhi t * 1) / t ^ 2)
        = gaussPhi t * (Real.exp (-2) - 1 + Real.exp (-2) / t ^ 2) := by
      field_simp; ring
    rw [hval] at h2
    have h2' : HasDerivAt (fun s => gaussTail s - Real.exp (-2) * (gaussPhi s / s))
        (gaussPhi t * (Real.exp (-2) - 1 + Real.exp (-2) / t ^ 2)) t := h2
    simpa only [hG] using h2'
  have hcont : ∀ y : ℝ, z ≤ y → ContinuousOn G (Set.Icc z y) := by
    intro y _
    have hdiv : ContinuousOn (fun t : ℝ => gaussPhi t / t) (Set.Icc z y) := by
      refine ContinuousOn.div gaussPhi_continuous.continuousOn continuous_id.continuousOn ?_
      intro t ht
      exact (lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) hz) ht.1).ne'
    exact continuous_gaussTail.continuousOn.sub (hdiv.const_mul _)
  have hdec : ∀ y : ℝ, z ≤ y → G y ≤ G z := by
    intro y hzy
    rcases eq_or_lt_of_le hzy with h | h
    · rw [← h]
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G
        (fun t => gaussPhi t * (Real.exp (-2) - 1 + Real.exp (-2) / t ^ 2))
        h (hcont y hzy) (fun t ht => hderiv t (le_trans hz ht.1.le))
      have hc1 : 1 ≤ c := le_trans hz hc.1.le
      have hneg : gaussPhi c * (Real.exp (-2) - 1 + Real.exp (-2) / c ^ 2) < 0 := by
        have h1 : Real.exp (-2) / c ^ 2 ≤ Real.exp (-2) := by
          have : c ^ 2 ≥ 1 := by nlinarith
          exact div_le_self hexp2pos.le this
        nlinarith [gaussPhi_pos c, hexp2]
      have hyz : 0 < y - z := by linarith
      have hq : (G y - G z) / (y - z) < 0 := by rw [← hslope]; exact hneg
      rcases div_neg_iff.mp hq with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · linarith
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => gaussTail t) atTop (𝓝 0) := tendsto_gaussTail_atTop
    have h2 : Tendsto (fun t : ℝ => gaussPhi t / t) atTop (𝓝 0) := tendsto_gaussPhi_div_atTop
    have h3 : Tendsto (fun t : ℝ => Real.exp (-2) * (gaussPhi t / t)) atTop (𝓝 0) := by
      simpa using h2.const_mul (Real.exp (-2))
    simpa [hG] using h1.sub h3
  have hz0 : 0 ≤ G z := by
    by_contra hneg
    push_neg at hneg
    have hε : 0 < -G z / 2 := by linarith
    have hev : ∀ᶠ y : ℝ in atTop, -(-G z / 2) < G y :=
      hlim.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨y, hy1, hy2⟩ := (hev.and (eventually_ge_atTop z)).exists
    have := hdec y hy2
    linarith
  have hz0' : 0 ≤ gaussTail z - Real.exp (-2) * (gaussPhi z / z) := by
    simpa only [hG, sub_apply] using hz0
  have hrw : Real.exp (-2) * gaussPhi z / z = Real.exp (-2) * (gaussPhi z / z) := by ring
  linarith

/-- **The definition agrees with the set integral over `(z, ∞)`**, i.e. `gaussTail`
is the standard normal upper tail `∫_{x>z} φ(x) dx`. -/
theorem gaussTail_eq_setIntegral (z : ℝ) :
    gaussTail z = ∫ x in Set.Ioi z, gaussPhi x := by
  have hInt : IntegrableOn gaussPhi (Set.Ioi z) := integrable_gaussPhi.integrableOn
  have hconv : Tendsto (fun b : ℝ => ∫ x in z..b, gaussPhi x) atTop
      (𝓝 (∫ x in Set.Ioi z, gaussPhi x)) :=
    intervalIntegral_tendsto_integral_Ioi z hInt tendsto_id
  have hlim : Tendsto (fun b : ℝ => (∫ x in z..b, gaussPhi x) + gaussTail b) atTop
      (𝓝 (∫ x in Set.Ioi z, gaussPhi x)) := by
    have h := hconv.add tendsto_gaussTail_atTop
    simpa [add_zero] using h
  have heq : (fun b : ℝ => gaussTail z)
      =ᶠ[atTop] (fun b : ℝ => (∫ x in z..b, gaussPhi x) + gaussTail b) := by
    filter_upwards [eventually_ge_atTop z] with b hb
    exact gaussTail_split hb
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq) hlim

end StrongMaximalEndpoint
