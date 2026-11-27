/-
An explicit admissible input for the endpoint constant.

`testFun R` is `2` on the axis-parallel rectangle `R` and `0` elsewhere.  Its
`Φₙ`-modular is `Φₙ(2)·vol(R)`, finite and positive, and its level set contains
`R`, so the ratio `|{Mₙ f > 1}| / ∫Φₙ(|f|)` is positive.  Hence `Cₙ ≠ 0`, which
is the last input needed for the unconditional `λ`-form of the endpoint
inequality.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import StrongMaximal.Basic
import StrongMaximal.Endpoint

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

variable {n : ℕ}

/-- The unit rectangle in `ℝⁿ`, used to exhibit an admissible input in every
dimension (including `n = 0`). -/
def unitRect (n : ℕ) : Rect n where
  lo := 0
  hi := 1
  lt := fun _ => zero_lt_one

/-- `2` on `R`, `0` elsewhere. -/
noncomputable def testFun (R : Rect n) : (Fin n → ℝ) → ℝ :=
  R.carrier.indicator fun _ => (2 : ℝ)

theorem measurable_testFun (R : Rect n) : Measurable (testFun R) :=
  measurable_const.indicator measurableSet_Icc

/-- The Lebesgue measure of a rectangle is its volume. -/
theorem volume_carrier (R : Rect n) : volume R.carrier = ENNReal.ofReal R.volume := by
  rw [Rect.carrier, Real.volume_Icc_pi, Rect.volume, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact (sub_pos.mpr (R.lt i)).le

theorem carrier_pos (R : Rect n) : 0 < volume R.carrier := by
  rw [volume_carrier]
  exact ENNReal.ofReal_pos.mpr R.volume_pos

theorem carrier_ne_top (R : Rect n) : volume R.carrier ≠ ⊤ := by
  rw [volume_carrier]
  exact ENNReal.ofReal_ne_top

/-- `∫_R |testFun R| = 2 vol(R)`. -/
theorem lintegral_testFun (R : Rect n) :
    ∫⁻ y in R.carrier, ENNReal.ofReal |testFun R y|
      = ENNReal.ofReal 2 * ENNReal.ofReal R.volume := by
  rw [← lintegral_indicator (s := R.carrier) measurableSet_Icc]
  have hfun : R.carrier.indicator (fun y => ENNReal.ofReal |testFun R y|)
      = R.carrier.indicator (fun _ => ENNReal.ofReal (2 : ℝ)) := by
    funext y
    by_cases hy : y ∈ R.carrier
    · have h2 : testFun R y = 2 := by rw [testFun, Set.indicator_of_mem hy]
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, h2]
      norm_num
    · simp [testFun, Set.indicator, hy]
  rw [hfun, lintegral_indicator (s := R.carrier)
      (show MeasurableSet R.carrier from measurableSet_Icc), lintegral_const,
    Measure.restrict_apply_univ, volume_carrier]

/-- Inside `R`, the strong maximal function of `testFun R` is at least `2`. -/
theorem ofReal_two_le_strongMax {R : Rect n} {x : Fin n → ℝ} (hx : x ∈ R.carrier) :
    ENNReal.ofReal 2 ≤ strongMax n (testFun R) x := by
  have hV0 : ENNReal.ofReal R.volume ≠ 0 := by
    rw [← volume_carrier]
    exact ne_of_gt (carrier_pos R)
  have hVtop : ENNReal.ofReal R.volume ≠ ⊤ := ENNReal.ofReal_ne_top
  have hratio : (∫⁻ y in R.carrier, ENNReal.ofReal |testFun R y|) / ENNReal.ofReal R.volume
      = ENNReal.ofReal 2 := by
    rw [lintegral_testFun, mul_div_assoc, ENNReal.div_self hV0 hVtop, mul_one]
  rw [← hratio]
  exact le_iSup_of_le (⟨R, hx⟩ : RectsAt n x) le_rfl

/-- The level set `{Mₙ (testFun R) > 1}` contains `R`. -/
theorem carrier_subset_level (R : Rect n) :
    R.carrier ⊆ {x | 1 < strongMax n (testFun R) x} := by
  intro x hx
  have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal 2 := by
    rw [ENNReal.ofReal_ofNat]
    norm_num
  exact lt_of_lt_of_le h1 (ofReal_two_le_strongMax hx)

/-- The `Φₙ`-modular of `testFun R` is `Φₙ(2) vol(R)`. -/
theorem lintegral_Phi_testFun (R : Rect n) :
    ∫⁻ x, ENNReal.ofReal (Phi n |testFun R x|)
      = ENNReal.ofReal (Phi n 2) * ENNReal.ofReal R.volume := by
  have hfun : (fun x => ENNReal.ofReal (Phi n |testFun R x|))
      = R.carrier.indicator (fun _ => ENNReal.ofReal (Phi n 2)) := by
    funext x
    by_cases hx : x ∈ R.carrier
    · have h2 : testFun R x = 2 := by rw [testFun, Set.indicator_of_mem hx]
      rw [h2]
      exact (Set.indicator_of_mem hx (fun _ => ENNReal.ofReal (Phi n 2))).symm
    · simp [testFun, Set.indicator, hx, Phi_zero]
  rw [hfun, lintegral_indicator (s := R.carrier)
      (show MeasurableSet R.carrier from measurableSet_Icc), lintegral_const,
    Measure.restrict_apply_univ, volume_carrier]

/-- `testFun R` is admissible. -/
theorem admissible_testFun (R : Rect n) : Admissible n (testFun R) := by
  have hphi : 0 < Phi n 2 := Phi_pos n (by norm_num)
  refine ⟨measurable_testFun R, ?_, ?_⟩
  · rw [lintegral_Phi_testFun, ← ENNReal.ofReal_mul hphi.le]
    exact ENNReal.ofReal_pos.mpr (mul_pos hphi R.volume_pos)
  · rw [lintegral_Phi_testFun]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- **`Cₙ ≠ 0`** in every dimension. -/
theorem endpointConst_ne_zero_uncond (n : ℕ) : endpointConst n ≠ 0 := by
  refine endpointConst_ne_zero (admissible_testFun (unitRect n)) ?_
  exact lt_of_lt_of_le (carrier_pos (unitRect n))
    (measure_mono (carrier_subset_level (unitRect n)))

/-- **The `λ`-form of the endpoint inequality, unconditionally**: for every
`λ > 0` and every measurable `f`,
`|{Mₙ f > λ}| ≤ Cₙ ∫ Φₙ(|f|/λ)`. -/
theorem endpointConst_lambda_uncond {f : (Fin n → ℝ) → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hmeas : Measurable f) :
    volume {x | ENNReal.ofReal lam < strongMax n f x}
      ≤ endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|) :=
  endpointConst_lambda_all hlam (endpointConst_ne_zero_uncond n) hmeas
/-- Minimality in the measurable formulation: every constant satisfying the
`λ`-form for all measurable inputs dominates `Cₙ`. -/
theorem le_endpointConst_measurable {n : ℕ} {K : ℝ≥0∞}
    (hK : ∀ (lam : ℝ) (f : (Fin n → ℝ) → ℝ), 0 < lam → Measurable f →
      volume {x | ENNReal.ofReal lam < strongMax n f x}
        ≤ K * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|)) :
    endpointConst n ≤ K := by
  refine iSup_le fun f => iSup_le fun hf => ?_
  have h1 := hK 1 f one_pos hf.1
  have harg : (fun x => ENNReal.ofReal (Phi n |f x / (1:ℝ)|))
      = fun x => ENNReal.ofReal (Phi n |f x|) := by
    funext x; simp
  rw [ENNReal.ofReal_one, harg] at h1
  exact ENNReal.div_le_iff hf.2.1.ne' hf.2.2 |>.mpr h1

/-- **`Cₙ` is the least constant in the endpoint inequality.**  It satisfies the
`λ`-form for every `λ > 0` and every measurable `f`, and any constant that does
dominates it.  This is the formal version of the paper's normalisation step
turning the `λ`-form into the `λ = 1` supremum. -/
theorem endpointConst_least (n : ℕ) :
    (∀ (lam : ℝ) (f : (Fin n → ℝ) → ℝ), 0 < lam → Measurable f →
      volume {x | ENNReal.ofReal lam < strongMax n f x}
        ≤ endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|)) ∧
    (∀ K : ℝ≥0∞, (∀ (lam : ℝ) (f : (Fin n → ℝ) → ℝ), 0 < lam → Measurable f →
      volume {x | ENNReal.ofReal lam < strongMax n f x}
        ≤ K * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|)) → endpointConst n ≤ K) :=
  ⟨fun lam f hlam hmeas => endpointConst_lambda_uncond hlam hmeas,
   fun K hK => le_endpointConst_measurable hK⟩

/-- `∫_R c = c vol(R)` for a constant `c ≥ 0`. -/
theorem lintegral_const_carrier (R : Rect n) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ y in R.carrier, ENNReal.ofReal c = ENNReal.ofReal c * ENNReal.ofReal R.volume := by
  rw [← lintegral_indicator (s := R.carrier)
    (show MeasurableSet R.carrier from measurableSet_Icc)]
  rw [lintegral_indicator_const (s := R.carrier)
    (show MeasurableSet R.carrier from measurableSet_Icc), volume_carrier]

/-- **Sanity check of the definition**: the strong maximal function of a
nonnegative constant is that constant, since every rectangle average equals it. -/
theorem strongMax_const (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (x : Fin n → ℝ) :
    strongMax n (fun _ => c) x = ENNReal.ofReal c := by
  have hvol : ∀ R : Rect n,
      (∫⁻ y in Set.Icc R.lo R.hi, ENNReal.ofReal c)
        = ENNReal.ofReal c * ENNReal.ofReal R.volume := by
    intro R
    exact lintegral_const_carrier R hc
  have hval : ∀ R : Rect n,
      (∫⁻ y in Set.Icc R.lo R.hi, ENNReal.ofReal |(c : ℝ)|) / ENNReal.ofReal R.volume
        = ENNReal.ofReal c := by
    intro R
    have hR0 : ENNReal.ofReal R.volume ≠ 0 := by
      rw [← volume_carrier]; exact ne_of_gt (carrier_pos R)
    have hRtop : ENNReal.ofReal R.volume ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [abs_of_nonneg hc, hvol R, mul_div_assoc, ENNReal.div_self hR0 hRtop, mul_one]
  refine le_antisymm ?_ ?_
  · exact iSup_le fun S => (hval S.1).le
  · refine le_iSup_of_le
      (⟨⟨fun i => x i - 1, fun i => x i + 1, fun i => by linarith⟩,
        ⟨fun i => by linarith, fun i => by linarith⟩⟩ : RectsAt n x) ?_
    exact (hval _).symm.le

end StrongMaximalEndpoint
