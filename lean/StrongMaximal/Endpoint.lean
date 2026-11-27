/-
`Cₙ` is the least constant in the endpoint inequality.

`endpointConst` is defined as the supremum of the `λ = 1` ratios.  Proved here:

* `Mₙ` depends only on the a.e. class of the input, and `Φₙ(|g|) = 0` a.e.
  forces `g = 0` a.e. — this removes the degenerate case `∫Φₙ(|f|) = 0`;
* `endpointConst_spec`: for every admissible `f`, `|{Mₙ f > 1}| ≤ Cₙ ∫Φₙ(|f|)`;
* `levelSet_eq`: homogeneity identifies the level set of the `λ`-form with that
  of the `λ = 1` form applied to `f/λ` (`ennreal_ofReal_lt_iff`);
  `endpointConst_lambda` — passing from that identity to the full `λ`-form for
  every finite-modular input — is **not** yet assembled, see `report.md`;
* `le_endpointConst`: every constant satisfying the `λ`-form dominates `Cₙ`.
-/
import StrongMaximal.Basic

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal NNReal

variable {n : ℕ}

/-- `Mₙ` depends only on the a.e. class of the input. -/
theorem strongMax_congr_ae {f g : (Fin n → ℝ) → ℝ} (h : f =ᵐ[volume] g) (x : Fin n → ℝ) :
    strongMax n f x = strongMax n g x := by
  unfold strongMax
  congr 1
  funext S
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (s := Set.Icc S.1.lo S.1.hi) h] with y hy
  rw [hy]

/-- `Mₙ` of the zero function vanishes. -/
theorem strongMax_zero (x : Fin n → ℝ) : strongMax n (fun _ => (0 : ℝ)) x = 0 := by
  unfold strongMax
  simp

/-- If the `Φₙ`-modular of `|g|` vanishes then `g = 0` a.e. -/
theorem ae_eq_zero_of_lintegral_Phi_eq_zero {g : (Fin n → ℝ) → ℝ} (hg : Measurable g)
    (h : ∫⁻ x, ENNReal.ofReal (Phi n |g x|) = 0) : g =ᵐ[volume] 0 := by
  have habs : Measurable fun x => |g x| := continuous_abs.measurable.comp hg
  have hmeas : Measurable fun x => ENNReal.ofReal (Phi n |g x|) :=
    ((measurable_Phi n).comp habs).ennreal_ofReal
  have h0 : (fun x => ENNReal.ofReal (Phi n |g x|)) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff hmeas).mp h
  filter_upwards [h0] with x hx
  have hz : Phi n |g x| = 0 := by
    by_contra hne
    have hpos : 0 < Phi n |g x| := lt_of_le_of_ne (Phi_nonneg n (abs_nonneg _)) (Ne.symm hne)
    exact absurd hx (ENNReal.ofReal_ne_zero_iff.mpr hpos)
  have hgz : |g x| = 0 := (Phi_eq_zero_iff n (abs_nonneg (g x))).mp hz
  rwa [abs_eq_zero] at hgz

/-- For an admissible input, the ratio is dominated by `Cₙ`. -/
theorem endpointConst_spec {f : (Fin n → ℝ) → ℝ} (hf : Admissible n f) :
    volume {x | 1 < strongMax n f x}
      ≤ endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |f x|) := by
  set a : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Phi n |f x|) with ha
  have hterm : volume {x | 1 < strongMax n f x} / a ≤ endpointConst n := by
    unfold endpointConst
    exact le_iSup₂ (f := fun (g : (Fin n → ℝ) → ℝ) (hg : Admissible n g) =>
      volume {x | 1 < strongMax n g x} / ∫⁻ y, ENNReal.ofReal (Phi n |g y|)) f hf
  have hcancel : volume {x | 1 < strongMax n f x} / a * a = volume {x | 1 < strongMax n f x} :=
    ENNReal.div_mul_cancel hf.2.1.ne' hf.2.2
  calc volume {x | 1 < strongMax n f x}
      = volume {x | 1 < strongMax n f x} / a * a := hcancel.symm
    _ ≤ endpointConst n * a := by gcongr

/-- Pure `ℝ≥0∞` form of the normalization step: `λ < a ↔ 1 < λ⁻¹ · a`. -/
lemma ennreal_ofReal_lt_iff {lam : ℝ} (hlam : 0 < lam) (a : ℝ≥0∞) :
    ENNReal.ofReal lam < a ↔ 1 < ENNReal.ofReal lam⁻¹ * a := by
  have hpos : 0 < lam⁻¹ := inv_pos.mpr hlam
  have h0 : ENNReal.ofReal lam⁻¹ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpos
  have htop : ENNReal.ofReal lam⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hLam : ENNReal.ofReal lam * ENNReal.ofReal lam⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hlam), mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]
  rw [← ENNReal.mul_lt_mul_iff_left h0 htop, hLam, mul_comm a]

/-- Homogeneity identifies the level set of the `λ`-form with that of the `λ = 1`
form applied to `f/λ`. -/
theorem levelSet_eq (f : (Fin n → ℝ) → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    {x | ENNReal.ofReal lam < strongMax n f x}
      = {x | 1 < strongMax n (fun y => lam⁻¹ * f y) x} := by
  have hsm : ∀ x, strongMax n (fun y => lam⁻¹ * f y) x
      = ENNReal.ofReal lam⁻¹ * strongMax n f x := by
    intro x
    exact strongMax_smul n f ⟨lam⁻¹, le_of_lt (inv_pos.mpr hlam)⟩ x
  ext x
  simp only [Set.mem_ofPred_eq, hsm]
  exact ennreal_ofReal_lt_iff hlam _

/-- The `λ`-form of the endpoint inequality with constant `Cₙ`. -/
theorem endpointConst_lambda (f : (Fin n → ℝ) → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hadm : Admissible n (fun y => lam⁻¹ * f y)) :
    volume {x | ENNReal.ofReal lam < strongMax n f x}
      ≤ endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|) := by
  rw [levelSet_eq f hlam]
  have h := endpointConst_spec hadm
  have hone : ∀ x, ENNReal.ofReal (Phi n |lam⁻¹ * f x|)
      = ENNReal.ofReal (Phi n |f x / lam|) := by
    intro x
    rw [div_eq_mul_inv, mul_comm lam⁻¹ (f x)]
  calc volume {x | 1 < strongMax n (fun y => lam⁻¹ * f y) x}
      ≤ endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |(fun y => lam⁻¹ * f y) x|) := h
    _ = endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|) := by
        congr 1
        exact lintegral_congr hone

/-- `Cₙ ≠ 0` as soon as some admissible input has a nonnegligible level set: the
ratio for that input is a positive element of the supremum.  Supplying such an
input (e.g. a constant multiple of the indicator of a cube) is the only missing
ingredient of the `∫Φₙ = ∞` degenerate case; see `report.md`. -/
theorem endpointConst_ne_zero {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Admissible n f)
    (hvol : 0 < volume {x | 1 < strongMax n f x}) : endpointConst n ≠ 0 := by
  have hratio : 0 < volume {x | 1 < strongMax n f x} / ∫⁻ x, ENNReal.ofReal (Phi n |f x|) :=
    ENNReal.div_pos hvol.ne' hf.2.2
  have hle : volume {x | 1 < strongMax n f x} / ∫⁻ x, ENNReal.ofReal (Phi n |f x|)
      ≤ endpointConst n :=
    le_iSup₂ (α := ℝ≥0∞)
      (f := fun (g : (Fin n → ℝ) → ℝ) (hg : Admissible n g) =>
        volume {x | 1 < strongMax n g x} / ∫⁻ y, ENNReal.ofReal (Phi n |g y|)) f hf
  exact ne_of_gt (lt_of_lt_of_le hratio hle)

/-- The `λ`-form in the degenerate case `∫Φₙ(|f/λ|) = ∞`: the right-hand side is
`∞` once `Cₙ ≠ 0`, so the inequality is automatic. -/
theorem endpointConst_lambda_of_infinite {n : ℕ} {f : (Fin n → ℝ) → ℝ} {lam : ℝ}
    (hne : endpointConst n ≠ 0)
    (hinf : ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|) = ⊤) :
    volume {x | ENNReal.ofReal lam < strongMax n f x}
      ≤ endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|) := by
  rw [hinf]
  exact le_top.trans_eq (ENNReal.mul_top hne).symm

/-- The `λ`-form in the degenerate case `∫Φₙ(|f/λ|) = 0`: then `f = 0` a.e., hence
`Mₙ f = 0` everywhere and both sides vanish. -/
theorem endpointConst_lambda_of_zero {n : ℕ} {f : (Fin n → ℝ) → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hmeas : Measurable f)
    (hzero : ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|) = 0) :
    volume {x | ENNReal.ofReal lam < strongMax n f x}
      ≤ endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|) := by
  have hmdiv : Measurable fun x => f x / lam := hmeas.div_const lam
  have hg0 : (fun x : Fin n → ℝ => f x / lam) =ᵐ[volume] 0 :=
    ae_eq_zero_of_lintegral_Phi_eq_zero hmdiv hzero
  have hf0 : f =ᵐ[volume] 0 := by
    filter_upwards [hg0] with x hx
    exact (div_eq_zero_iff.mp hx).resolve_right hlam.ne'
  have hM : ∀ x, strongMax n f x = 0 := by
    intro x
    rw [strongMax_congr_ae (n := n) (f := f) (g := fun _ => (0:ℝ)) hf0 x]
    exact strongMax_zero x
  have hempty : {x | ENNReal.ofReal lam < strongMax n f x} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, hM x, Set.mem_empty_iff_false, iff_false, not_lt]
    exact zero_le
  rw [hempty, hzero, mul_zero]
  simp

/-- **The `λ`-form for every measurable input**, given `Cₙ ≠ 0`: the three cases
`∫Φₙ(|f/λ|) = 0`, `= ∞`, and finite nonzero are
`endpointConst_lambda_of_zero`, `endpointConst_lambda_of_infinite`, and
`endpointConst_lambda`. -/
theorem endpointConst_lambda_all {n : ℕ} {f : (Fin n → ℝ) → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hne : endpointConst n ≠ 0) (hmeas : Measurable f) :
    volume {x | ENNReal.ofReal lam < strongMax n f x}
      ≤ endpointConst n * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|) := by
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|)) 0 with h0 | h0
  · exact endpointConst_lambda_of_zero hlam hmeas h0
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|)) ⊤ with htop | htop
  · exact endpointConst_lambda_of_infinite hne htop
  · have habs : ∀ x : Fin n → ℝ, |lam⁻¹ * f x| = |f x / lam| := by
      intro x
      rw [abs_mul, abs_inv, abs_of_pos hlam, div_eq_mul_inv, abs_mul, abs_inv,
        abs_of_pos hlam, mul_comm]
    have hfun : (fun x => ENNReal.ofReal (Phi n |(fun y => lam⁻¹ * f y) x|))
        = fun x => ENNReal.ofReal (Phi n |f x / lam|) := by
      funext x
      show ENNReal.ofReal (Phi n |lam⁻¹ * f x|) = ENNReal.ofReal (Phi n |f x / lam|)
      rw [habs x]
    have hmod' : (∫⁻ x, ENNReal.ofReal (Phi n |(fun y => lam⁻¹ * f y) x|)) ≠ 0 := by
      rw [hfun]; exact h0
    have hfin' : (∫⁻ x, ENNReal.ofReal (Phi n |(fun y => lam⁻¹ * f y) x|)) ≠ ⊤ := by
      rw [hfun]; exact htop
    refine endpointConst_lambda f hlam ⟨?_, ?_, hfin'⟩
    · exact hmeas.const_mul lam⁻¹
    · exact lt_of_le_of_ne zero_le (Ne.symm hmod')

/-- Conversely, every constant satisfying the `λ`-form dominates `Cₙ`: `Cₙ` is the
least admissible coefficient. -/
theorem le_endpointConst {K : ℝ≥0∞}
    (hK : ∀ (lam : ℝ) (f : (Fin n → ℝ) → ℝ), 0 < lam → Admissible n (fun y => lam⁻¹ * f y) →
      volume {x | ENNReal.ofReal lam < strongMax n f x}
        ≤ K * ∫⁻ x, ENNReal.ofReal (Phi n |f x / lam|)) :
    endpointConst n ≤ K := by
  refine iSup_le fun f => iSup_le fun hf => ?_
  have h1 := hK 1 f one_pos (by simpa using hf)
  have harg : (fun x => ENNReal.ofReal (Phi n |f x / (1:ℝ)|))
      = fun x => ENNReal.ofReal (Phi n |f x|) := by
    funext x; simp
  rw [ENNReal.ofReal_one, harg] at h1
  exact ENNReal.div_le_iff hf.2.1.ne' hf.2.2 |>.mpr h1

end StrongMaximalEndpoint
