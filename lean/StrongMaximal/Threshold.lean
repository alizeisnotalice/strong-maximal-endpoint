/-
The plateau width and the threshold criterion of the lower-bound construction.

The manuscript takes `w = (log n)/2 + log(log n)`; here `plateauWidth n` is that
number, and the two facts used to define the threshold are proved:

* `Hw_monotone`, `modelExp_anti`: `q ↦ E H_w(Sₙ - q)` is nonincreasing, so the
  threshold `q` with `E H_w(Sₙ - q) = 1` is unique when it exists;
* `Hw_integral_gt_one_of_cdf_lt`: **the criterion** — any `s` with
  `P(Sₙ ≤ s) < (E Sₙ - s - w)/n` satisfies `E H_w(Sₙ - s) > 1`, and hence lies
  below the threshold.

The analytic step that turns this into the coefficient `(9-μ)/24` is a CDF
estimate at the threshold; that is where the manuscript's Edgeworth bookkeeping
sits (see `report.md`, section 3), and it is *not* claimed here.
-/
import StrongMaximal.HwModel

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

/-- The plateau width of the manuscript: `w = (log n)/2 + log(log n)`. -/
noncomputable def plateauWidth (n : ℕ) : ℝ := Real.log n / 2 + Real.log (Real.log n)

theorem plateauWidth_pos {n : ℕ} (hn : 3 ≤ n) : 0 < plateauWidth n := by
  have hlog3 : (1:ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hlogn : (1:ℝ) < Real.log n := by
    have h3n : (3:ℝ) ≤ n := by exact_mod_cast hn
    exact lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) h3n)
  have h2 : 0 < Real.log n / 2 := by linarith
  have h3 : 0 < Real.log (Real.log n) := Real.log_pos hlogn
  simp only [plateauWidth]
  linarith

/-- `H_w` is nondecreasing. -/
theorem Hw_monotone (n : ℕ) (w : ℝ) : Monotone (Hw n w) := by
  intro x y hxy
  unfold Hw
  rcases lt_or_ge x 0 with hx | hx
  · rw [if_pos hx]
    rcases lt_or_ge y 0 with hy | hy
    · rw [if_pos hy]
    · rcases le_or_gt y w with hyw | hyw
      · rw [if_neg (not_lt.mpr hy), if_pos hyw]
        norm_num
      · rw [if_neg (not_lt.mpr hy), if_neg (not_le.mpr hyw)]
        exact (Real.exp_pos _).le
  · rcases le_or_gt x w with hxw | hxw
    · rw [if_neg (not_lt.mpr hx), if_pos hxw]
      have hy : ¬ y < 0 := by linarith
      rcases le_or_gt y w with hyw | hyw
      · rw [if_neg hy, if_pos hyw]
      · rw [if_neg hy, if_neg (not_le.mpr hyw)]
        have hpos : 0 ≤ (y - w) / (n:ℝ) :=
          div_nonneg (by linarith) (by exact_mod_cast (by omega : 0 ≤ n))
        exact (Real.one_le_exp_iff).mpr hpos
    · rw [if_neg (not_lt.mpr hx), if_neg (not_le.mpr hxw)]
      have hy : ¬ y < 0 := by linarith
      have hyw : ¬ y ≤ w := by linarith
      rw [if_neg hy, if_neg hyw]
      exact (Real.exp_le_exp).mpr
        (div_le_div_of_nonneg_right (by linarith : x - w ≤ y - w)
          (by exact_mod_cast (by omega : 0 ≤ n)))

/-- `q ↦ E H_w(Sₙ - q)` is nonincreasing. -/
theorem modelExp_anti (n : ℕ) (hn : 2 ≤ n) (w : ℝ) (a : ℝ) {q q' : ℝ} (hqq' : q ≤ q') :
    (∫ ω : Fin n → ℝ × Bool, Hw n w (nIncr n a ω - q') ∂(nStepLaw n a))
      ≤ ∫ ω : Fin n → ℝ × Bool, Hw n w (nIncr n a ω - q) ∂(nStepLaw n a) := by
  refine integral_mono (integrable_Hw_nIncr n hn w q' a) (integrable_Hw_nIncr n hn w q a) ?_
  intro ω
  exact Hw_monotone n w (by linarith : nIncr n a ω - q' ≤ nIncr n a ω - q)

/-- **The threshold criterion**: any `s` whose CDF beats the linear term lies
below the threshold, i.e. `E H_w(Sₙ - s) > 1`. -/
theorem Hw_integral_gt_one_of_cdf_lt (n : ℕ) (hn : 2 ≤ n) {w s : ℝ} (hw0 : 0 ≤ w) (a : ℝ)
    (h : (nStepLaw n a).real {ω : Fin n → ℝ × Bool | nIncr n a ω ≤ s}
      < (∫ ω, nIncr n a ω ∂(nStepLaw n a) - s - w) / (n : ℝ)) :
    1 < ∫ ω : Fin n → ℝ × Bool, Hw n w (nIncr n a ω - s) ∂(nStepLaw n a) := by
  have hmodel := Hw_integral_ge_model n hn (w := w) (s := s) hw0 a
  have h2 : (1:ℝ) < 1 - (nStepLaw n a).real {ω : Fin n → ℝ × Bool | nIncr n a ω ≤ s}
      + (∫ ω, nIncr n a ω ∂(nStepLaw n a) - s - w) / (n : ℝ) := by linarith
  exact lt_of_lt_of_le h2 hmodel

end StrongMaximalEndpoint
