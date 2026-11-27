/-
The `n`-fold increment: `Sₙ = ∑_{i<n} Z_a` for i.i.d. copies of the one-step
increment, and its mean `n · m(a)`.

The law is the product `Measure.pi (fun _ => stepLaw a)` on `Fin n → ℝ × Bool`,
i.e. exactly the `Γ(n,1) + a·Bin(n,ρ)` model of the manuscript: the exponential
coordinates sum to `Γ(n,1)` and the Bernoulli coordinates to `Bin(n, ρ a)`.
-/
import Mathlib.MeasureTheory.Integral.Pi
import StrongMaximal.StepModel

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

/-- `n` independent copies of the one-step law. -/
noncomputable def nStepLaw (n : ℕ) (a : ℝ) : Measure (Fin n → ℝ × Bool) :=
  Measure.pi (fun _ : Fin n => stepLaw a)

lemma nStepLaw_def (n : ℕ) (a : ℝ) :
    nStepLaw n a = Measure.pi (fun _ : Fin n => stepLaw a) := rfl

/-- The `n`-fold increment `Sₙ = ∑_{i<n} Z_a(i)`. -/
noncomputable def nIncr (n : ℕ) (a : ℝ) (ω : Fin n → ℝ × Bool) : ℝ :=
  ∑ i, stepIncr a (ω i)

/-- **The mean of `Sₙ` is `n · m(a)`**: `∫ Sₙ = n (1 + a ρ(a))`. -/
theorem integral_nIncr (n : ℕ) (a : ℝ) :
    ∫ ω, nIncr n a ω ∂(nStepLaw n a) = (n : ℝ) * mStep a := by
  haveI hprob : ∀ i : Fin n, IsProbabilityMeasure (stepLaw a) :=
    fun _ => isProbabilityMeasure_stepLaw a
  simp only [nStepLaw_def, nIncr]
  rw [integral_finsetSum Finset.univ
    (f := fun i (ω : Fin n → ℝ × Bool) => stepIncr a (ω i))
    (fun i _ => integrable_comp_eval (integrable_stepIncr a))]
  have h : ∀ i : Fin n, ∫ ω : Fin n → ℝ × Bool, stepIncr a (ω i)
      ∂(Measure.pi (fun _ : Fin n => stepLaw a)) = mStep a := by
    intro i
    exact (@integral_comp_eval (Fin n) inferInstance (fun _ : Fin n => ℝ × Bool)
      (fun _ => inferInstance) (fun _ : Fin n => stepLaw a) ℝ
      inferInstance inferInstance (fun _ => isProbabilityMeasure_stepLaw a)
      i (stepIncr a) ((measurable_stepIncr a).aestronglyMeasurable)).trans
      (integral_stepIncr a)
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The `n`-fold law is a probability measure. -/
theorem isProbabilityMeasure_nStepLaw (n : ℕ) (a : ℝ) :
    IsProbabilityMeasure (nStepLaw n a) := by
  rw [nStepLaw_def]
  haveI : ∀ i : Fin n, IsProbabilityMeasure (stepLaw a) :=
    fun _ => isProbabilityMeasure_stepLaw a
  infer_instance

end StrongMaximalEndpoint
