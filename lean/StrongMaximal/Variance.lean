/-
The second moment and variance of the one-step increment `Z_a`.

  `E[Z_a²] = 2 + 2a ρ(a) + a² ρ(a)`  and  `Var(Z_a) = 1 + a² ρ(a)(1-ρ(a)) = vStep a`.

So `vStep`, like `mStep`, is a genuine variance of the increment law and not
just a definition.  The exponential second moment `∫₀^∞ x² e^{-x} = 2` is the
`a = 3` case of the Gamma integral (`Γ(3) = 2!`).
-/
import StrongMaximal.StepModel
import StrongMaximal.ExpModel

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

/-- The Bernoulli part `1_{ω.2}` of the increment. -/
noncomputable def berPart (ω : ℝ × Bool) : ℝ := if ω.2 then 1 else 0

theorem measurable_berPart : Measurable berPart := by
  have hset : MeasurableSet {ω : ℝ × Bool | ω.2 = true} :=
    measurableSet_singleton true |>.preimage measurable_snd
  have heq : berPart = {ω : ℝ × Bool | ω.2 = true}.indicator (fun _ => (1:ℝ)) := by
    funext ω
    by_cases h : ω.2 = true <;> simp [berPart, Set.indicator, h]
  rw [heq]
  exact Measurable.indicator measurable_const hset

theorem berPart_sq (ω : ℝ × Bool) : berPart ω ^ 2 = berPart ω := by
  by_cases h : ω.2 = true <;> simp [berPart, h]

theorem stepIncr_eq (a : ℝ) (ω : ℝ × Bool) :
    stepIncr a ω = ω.1 + a * berPart ω := rfl

/-- The exponential factor has second moment `2` (again read off from its
integral, via `integral_undef`). -/
theorem integrable_id_sq_expMeasure :
    Integrable (fun x : ℝ => x ^ 2) (ProbabilityTheory.expMeasure 1) := by
  have h1 := integral_expMeasure_one_sq
  by_contra h
  rw [integral_undef h] at h1
  norm_num at h1

/-- **The second moment of `Z_a`**. -/
theorem integral_stepIncr_sq (a : ℝ) :
    ∫ ω, (stepIncr a ω) ^ 2 ∂(stepLaw a)
      = 2 + 2 * a * rho a + a ^ 2 * rho a := by
  haveI hμ : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  haveI hν : IsProbabilityMeasure
      (ProbabilityTheory.bernoulliMeasure true false (rhoI a)) := inferInstance
  rw [stepLaw_def]
  have hexp : ∀ ω : ℝ × Bool, (stepIncr a ω) ^ 2
      = ω.1 ^ 2 + ((2 * a) * (ω.1 * berPart ω) + (a ^ 2) * (berPart ω) ^ 2) := by
    intro ω
    rw [stepIncr_eq]
    ring
  have hI1 : Integrable (fun ω : ℝ × Bool => ω.1 ^ 2)
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) :=
    Integrable.comp_fst integrable_id_sq_expMeasure _
  have hI2 : Integrable (fun ω : ℝ × Bool => (2 * a) * (ω.1 * berPart ω))
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) := by
    have h : Integrable (fun ω : ℝ × Bool => ω.1 * berPart ω)
        ((ProbabilityTheory.expMeasure 1).prod
          (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) :=
      Integrable.mono (Integrable.comp_fst integrable_id_expMeasure_one _)
        ((measurable_fst.mul measurable_berPart).aestronglyMeasurable) (by
          filter_upwards with ω
          by_cases h : ω.2 = true <;> simp [berPart, h, abs_mul, abs_of_nonneg])
    exact h.const_mul _
  have hI3 : Integrable (fun ω : ℝ × Bool => (a ^ 2) * (berPart ω) ^ 2)
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) := by
    have h : Integrable (fun ω : ℝ × Bool => (berPart ω) ^ 2)
        ((ProbabilityTheory.expMeasure 1).prod
          (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) := by
      have heq : (fun ω : ℝ × Bool => (berPart ω) ^ 2) = berPart := by
        funext ω; exact berPart_sq ω
      rw [heq]
      exact (Integrable.of_bound measurable_berPart.aestronglyMeasurable 1 (by
        filter_upwards with ω
        by_cases h : ω.2 = true <;> simp [berPart, h]))
    exact h.const_mul _
  have hBC : Integrable (fun ω : ℝ × Bool =>
      (2 * a) * (ω.1 * berPart ω) + (a ^ 2) * (berPart ω) ^ 2)
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) := hI2.add hI3
  simp only [hexp]
  rw [integral_add hI1 hBC, integral_add hI2 hI3]
  have p1 : ∫ ω : ℝ × Bool, ω.1 ^ 2
      ∂((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) = 2 := by
    have h := integral_prod_mul (μ := ProbabilityTheory.expMeasure 1)
      (ν := ProbabilityTheory.bernoulliMeasure true false (rhoI a))
      (f := fun x : ℝ => x ^ 2) (g := fun _ : Bool => (1:ℝ))
    simp only [mul_one] at h
    rw [h, integral_expMeasure_one_sq]
    simp
  have p2 : ∫ ω : ℝ × Bool, ω.1 * berPart ω
      ∂((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) = rho a := by
    have h := integral_prod_mul (μ := ProbabilityTheory.expMeasure 1)
      (ν := ProbabilityTheory.bernoulliMeasure true false (rhoI a))
      (f := fun x : ℝ => x) (g := fun b : Bool => if b then (1:ℝ) else 0)
    simp only [berPart]
    rw [h, integral_expMeasure_one, integral_bernoulli_indicator]
    simp
  have p3 : ∫ ω : ℝ × Bool, (berPart ω) ^ 2
      ∂((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) = rho a := by
    have heq : (fun ω : ℝ × Bool => (berPart ω) ^ 2)
        = fun ω : ℝ × Bool => if ω.2 then (1:ℝ) else 0 := by
      funext ω
      rw [berPart_sq]
      rfl
    rw [heq]
    have h := integral_prod_mul (μ := ProbabilityTheory.expMeasure 1)
      (ν := ProbabilityTheory.bernoulliMeasure true false (rhoI a))
      (f := fun _ : ℝ => (1:ℝ)) (g := fun b : Bool => if b then (1:ℝ) else 0)
    simp only [one_mul] at h
    rw [h, integral_bernoulli_indicator]
    simp
  have h2 : ∫ ω : ℝ × Bool, (2 * a) * (ω.1 * berPart ω)
      ∂((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a)))
      = (2 * a) * rho a := by
    rw [integral_const_mul, p2]
  have h3 : ∫ ω : ℝ × Bool, (a ^ 2) * (berPart ω) ^ 2
      ∂((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a)))
      = (a ^ 2) * rho a := by
    rw [integral_const_mul, p3]
  rw [p1, h2, h3]
  ring

/-- **The variance of `Z_a` is `vStep a`**. -/
theorem variance_stepIncr (a : ℝ) :
    ∫ ω, (stepIncr a ω) ^ 2 ∂(stepLaw a)
      - (∫ ω, stepIncr a ω ∂(stepLaw a)) ^ 2 = vStep a := by
  rw [integral_stepIncr_sq, integral_stepIncr, mStep, vStep]
  ring

end StrongMaximalEndpoint
