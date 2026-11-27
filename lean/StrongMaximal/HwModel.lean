/-
The integrated plateau inequality applied to the actual model `Sₙ`.

The plateau profile `H_w` is dominated by `1 + e^{(v-w)/n}`, so `H_w(Sₙ - s)` is
integrable once `e^{Sₙ/n}` is — which is `integrable_exp_nIncr`.  Hence
`Hw_integral_ge` applies to `X = nIncr n a`:

  `1 - P(Sₙ ≤ s) + (E Sₙ - s - w)/n ≤ E H_w(Sₙ - s)`.
-/
import StrongMaximal.ExpMoment
import StrongMaximal.Plateau

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

/-- `H_w v ≤ 1 + e^{(v-w)/n}` for every `v`. -/
theorem Hw_le_one_add_exp (n : ℕ) (w v : ℝ) :
    Hw n w v ≤ 1 + Real.exp ((v - w) / n) := by
  unfold Hw
  split_ifs
  · linarith [Real.exp_pos ((v - w) / n)]
  · linarith [Real.exp_pos ((v - w) / n)]
  · linarith

/-- `H_w` is measurable. -/
theorem measurable_Hw (n : ℕ) (w : ℝ) : Measurable (Hw n w) := by
  have h : Measurable fun v : ℝ =>
      if v < 0 then (0:ℝ) else if v ≤ w then 1 else Real.exp ((v - w) / n) := by
    refine Measurable.ite ?_ measurable_const ?_
    · exact measurableSet_Iio
    · refine Measurable.ite ?_ measurable_const ?_
      · exact measurableSet_Iic
      · fun_prop
  change Measurable fun v => if v < 0 then (0:ℝ) else if v ≤ w then 1 else Real.exp ((v - w) / n)
  exact h

/-- `Sₙ` is measurable. -/
theorem measurable_nIncr (n : ℕ) (a : ℝ) : Measurable (nIncr n a) := by
  change Measurable fun ω : Fin n → ℝ × Bool => ∑ i, stepIncr a (ω i)
  fun_prop

/-- `Sₙ` is integrable. -/
theorem integrable_nIncr (n : ℕ) (a : ℝ) :
    Integrable (fun ω : Fin n → ℝ × Bool => nIncr n a ω) (nStepLaw n a) := by
  haveI : IsProbabilityMeasure (nStepLaw n a) := isProbabilityMeasure_nStepLaw n a
  haveI : ∀ i : Fin n, IsProbabilityMeasure (stepLaw a) :=
    fun _ => isProbabilityMeasure_stepLaw a
  rw [nStepLaw_def]
  change Integrable (fun ω : Fin n → ℝ × Bool => ∑ i, stepIncr a (ω i)) _
  exact integrable_finsetSum Finset.univ
    (fun i _ => integrable_comp_eval (integrable_stepIncr a))

/-- **`H_w(Sₙ - s)` is integrable** for the model law. -/
theorem integrable_Hw_nIncr (n : ℕ) (hn : 2 ≤ n) (w s : ℝ) (a : ℝ) :
    Integrable (fun ω : Fin n → ℝ × Bool => Hw n w (nIncr n a ω - s)) (nStepLaw n a) := by
  haveI : IsProbabilityMeasure (nStepLaw n a) := isProbabilityMeasure_nStepLaw n a
  have hmeas : AEStronglyMeasurable
      (fun ω : Fin n → ℝ × Bool => Hw n w (nIncr n a ω - s)) (nStepLaw n a) :=
    ((measurable_Hw n w).comp ((measurable_nIncr n a).sub_const s)).aestronglyMeasurable
  have hIntg : Integrable
      (fun ω : Fin n → ℝ × Bool => 1 + Real.exp (-(s + w) / n) * Real.exp (nIncr n a ω / n))
      (nStepLaw n a) :=
    (integrable_const 1).add ((integrable_exp_nIncr n hn a).const_mul _)
  have hle : ∀ ω : Fin n → ℝ × Bool,
      Hw n w (nIncr n a ω - s)
        ≤ 1 + Real.exp (-(s + w) / n) * Real.exp (nIncr n a ω / n) := by
    intro ω
    have h := Hw_le_one_add_exp n w (nIncr n a ω - s)
    have hexp : Real.exp ((nIncr n a ω - s - w) / n)
        = Real.exp (-(s + w) / n) * Real.exp (nIncr n a ω / n) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hexp] at h
    exact h
  refine Integrable.mono hIntg hmeas ?_
  filter_upwards with ω
  have h2 : 0 ≤ Hw n w (nIncr n a ω - s) := Hw_nonneg n w _
  have h3 : 0 ≤ 1 + Real.exp (-(s + w) / n) * Real.exp (nIncr n a ω / n) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h2, abs_of_nonneg h3]
  exact hle ω

/-- **The integrated plateau inequality for `Sₙ`**. -/
theorem Hw_integral_ge_model (n : ℕ) (hn : 2 ≤ n) {w s : ℝ} (hw0 : 0 ≤ w) (a : ℝ) :
    1 - (nStepLaw n a).real {ω : Fin n → ℝ × Bool | nIncr n a ω ≤ s}
      + (∫ ω, nIncr n a ω ∂(nStepLaw n a) - s - w) / (n : ℝ)
      ≤ ∫ ω, Hw n w (nIncr n a ω - s) ∂(nStepLaw n a) := by
  haveI : IsProbabilityMeasure (nStepLaw n a) := isProbabilityMeasure_nStepLaw n a
  exact Hw_integral_ge (n := n) (by exact_mod_cast (by omega : 0 < n)) hw0
    (measurable_nIncr n a) (integrable_nIncr n a) (integrable_Hw_nIncr n hn w s a)

end StrongMaximalEndpoint
