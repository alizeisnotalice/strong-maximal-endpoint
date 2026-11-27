/-
The one-step increment law of the lower-bound model.

At action `a` the increment of the `-log`-rank is
`Z_a = Exp 1 + a · Bernoulli (ρ a)` with `ρ a = 1/(1+e^a)`, i.e. the law
`expMeasure 1 × bernoulliMeasure true false (ρ a)` on `ℝ × Bool`.  This file

* builds that law (`stepLaw`) and the increment (`stepIncr`);
* proves `∫ Z_a = 1 + a ρ(a) = mStep a` — so `mStep` is genuinely the mean of
  the increment, not just a definition;
* proves the Bernoulli mean `∫ (1_{b}) ∂Ber(true,false,p) = p` separately.
-/
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Integral.Prod
import StrongMaximal.ExpModel
import StrongMaximal.Cumulants

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

/-- `ρ a` as an element of the unit interval. -/
noncomputable def rhoI (a : ℝ) : unitInterval :=
  ⟨rho a, by
    have hpos : (0:ℝ) < 1 + Real.exp a := by positivity
    constructor
    · simp only [rho]; positivity
    · simp only [rho]
      rw [div_le_one hpos]
      linarith [Real.exp_pos a]⟩

@[simp] lemma coe_rhoI (a : ℝ) : ((rhoI a : unitInterval) : ℝ) = rho a := rfl

/-- The law of one increment: `Exp 1 × Bernoulli (ρ a)` on `ℝ × Bool`. -/
noncomputable def stepLaw (a : ℝ) : Measure (ℝ × Bool) :=
  (ProbabilityTheory.expMeasure 1).prod
    (ProbabilityTheory.bernoulliMeasure true false (rhoI a))

lemma stepLaw_def (a : ℝ) :
    stepLaw a = (ProbabilityTheory.expMeasure 1).prod
      (ProbabilityTheory.bernoulliMeasure true false (rhoI a)) := rfl

/-- The increment itself: the exponential part plus `a` times the Bernoulli part. -/
noncomputable def stepIncr (a : ℝ) (ω : ℝ × Bool) : ℝ :=
  ω.1 + a * (if ω.2 then 1 else 0)

/-- **The Bernoulli mean**: `∫ 1_{b} ∂Ber(true,false,p) = p`. -/
theorem integral_bernoulli_indicator (p : unitInterval) :
    ∫ b : Bool, (if b then (1:ℝ) else 0)
      ∂(ProbabilityTheory.bernoulliMeasure true false p) = (p : ℝ) := by
  rw [ProbabilityTheory.integral_bernoulliMeasure]
  simp

/-- The exponential factor is integrable — read off from its integral being `1`
(`integral_undef` would force the integral to be `0` otherwise). -/
theorem integrable_id_expMeasure_one :
    Integrable (fun x : ℝ => x) (ProbabilityTheory.expMeasure 1) := by
  have h1 := integral_expMeasure_one
  by_contra h
  rw [integral_undef h] at h1
  norm_num at h1

/-- `stepIncr a` is measurable. -/
@[fun_prop] theorem measurable_stepIncr (a : ℝ) : Measurable (stepIncr a) := by
  have h1 : Measurable fun ω : ℝ × Bool => ω.1 := measurable_fst
  have h2 : Measurable fun ω : ℝ × Bool => (if ω.2 then (1:ℝ) else 0) := by
    have hset : MeasurableSet {ω : ℝ × Bool | ω.2 = true} :=
      measurableSet_singleton true |>.preimage measurable_snd
    have heq : (fun ω : ℝ × Bool => if ω.2 then (1:ℝ) else 0)
        = {ω : ℝ × Bool | ω.2 = true}.indicator (fun _ => (1:ℝ)) := by
      funext ω
      by_cases h : ω.2 = true <;> simp [h]
    rw [heq]
    exact Measurable.indicator measurable_const hset
  exact h1.add (h2.const_mul a)

/-- `stepLaw a` is a probability measure. -/
theorem isProbabilityMeasure_stepLaw (a : ℝ) : IsProbabilityMeasure (stepLaw a) := by
  rw [stepLaw_def]
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  haveI : IsProbabilityMeasure
      (ProbabilityTheory.bernoulliMeasure true false (rhoI a)) := inferInstance
  infer_instance

/-- The increment is integrable for its own law. -/
theorem integrable_stepIncr (a : ℝ) : Integrable (stepIncr a) (stepLaw a) := by
  haveI hμ : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  haveI hν : IsProbabilityMeasure
      (ProbabilityTheory.bernoulliMeasure true false (rhoI a)) := inferInstance
  rw [stepLaw_def]
  have hInt1 : Integrable (fun ω : ℝ × Bool => ω.1)
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) :=
    Integrable.comp_fst integrable_id_expMeasure_one
      (ProbabilityTheory.bernoulliMeasure true false (rhoI a))
  have hset : MeasurableSet {ω : ℝ × Bool | ω.2 = true} :=
    measurableSet_singleton true |>.preimage measurable_snd
  have hbdd : Integrable (fun ω : ℝ × Bool => if ω.2 then (1:ℝ) else 0)
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) := by
    have heq : (fun ω : ℝ × Bool => if ω.2 then (1:ℝ) else 0)
        = {ω : ℝ × Bool | ω.2 = true}.indicator (fun _ => (1:ℝ)) := by
      funext ω
      by_cases h : ω.2 = true <;> simp [h]
    rw [heq]
    exact (integrable_const (1:ℝ)).indicator hset
  exact hInt1.add (hbdd.const_mul a)

/-- **`mStep` is the mean of the increment**: `∫ Z_a = 1 + a ρ(a)`. -/
theorem integral_stepIncr (a : ℝ) :
    ∫ ω, stepIncr a ω ∂(stepLaw a) = mStep a := by
  haveI hμ : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  haveI hν : IsProbabilityMeasure
      (ProbabilityTheory.bernoulliMeasure true false (rhoI a)) := inferInstance
  rw [stepLaw_def]
  have hInt1 : Integrable (fun ω : ℝ × Bool => ω.1)
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) :=
    Integrable.comp_fst integrable_id_expMeasure_one
      (ProbabilityTheory.bernoulliMeasure true false (rhoI a))
  have hset : MeasurableSet {ω : ℝ × Bool | ω.2 = true} :=
    measurableSet_singleton true |>.preimage measurable_snd
  have hbdd : Integrable (fun ω : ℝ × Bool => if ω.2 then (1:ℝ) else 0)
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) := by
    have heq : (fun ω : ℝ × Bool => if ω.2 then (1:ℝ) else 0)
        = {ω : ℝ × Bool | ω.2 = true}.indicator (fun _ => (1:ℝ)) := by
      funext ω
      by_cases h : ω.2 = true <;> simp [h]
    rw [heq]
    exact (integrable_const (1:ℝ)).indicator hset
  have hInt2 : Integrable (fun ω : ℝ × Bool => a * (if ω.2 then (1:ℝ) else 0))
      ((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) := hbdd.const_mul a
  have hfst : ∫ ω : ℝ × Bool, ω.1
      ∂((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) = 1 := by
    have h := integral_prod_mul (μ := ProbabilityTheory.expMeasure 1)
      (ν := ProbabilityTheory.bernoulliMeasure true false (rhoI a))
      (f := fun x : ℝ => x) (g := fun _ : Bool => (1:ℝ))
    simp only [mul_one] at h
    rw [h, integral_expMeasure_one]
    simp
  have hsnd : ∫ ω : ℝ × Bool, a * (if ω.2 then (1:ℝ) else 0)
      ∂((ProbabilityTheory.expMeasure 1).prod
        (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) = a * rho a := by
    rw [integral_const_mul]
    have h := integral_prod_mul (μ := ProbabilityTheory.expMeasure 1)
      (ν := ProbabilityTheory.bernoulliMeasure true false (rhoI a))
      (f := fun _ : ℝ => (1:ℝ)) (g := fun b : Bool => if b then (1:ℝ) else 0)
    simp only [one_mul] at h
    rw [h, integral_bernoulli_indicator]
    simp
  calc ∫ ω, stepIncr a ω
        ∂((ProbabilityTheory.expMeasure 1).prod
          (ProbabilityTheory.bernoulliMeasure true false (rhoI a)))
      = ∫ ω, (ω.1 + a * (if ω.2 then (1:ℝ) else 0))
          ∂((ProbabilityTheory.expMeasure 1).prod
            (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) := rfl
    _ = ∫ ω, ω.1 ∂((ProbabilityTheory.expMeasure 1).prod
            (ProbabilityTheory.bernoulliMeasure true false (rhoI a)))
          + ∫ ω, a * (if ω.2 then (1:ℝ) else 0)
            ∂((ProbabilityTheory.expMeasure 1).prod
              (ProbabilityTheory.bernoulliMeasure true false (rhoI a))) :=
        integral_add hInt1 hInt2
    _ = 1 + a * rho a := by rw [hfst, hsnd]
    _ = mStep a := by simp only [mStep]

end StrongMaximalEndpoint
