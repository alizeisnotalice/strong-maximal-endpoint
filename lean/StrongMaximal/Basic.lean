/-
The objects the v1 manuscript is about, pinned down in Lean.

* `Φₙ t = t (1 + log⁺ t)^{n-1}` with `Φₙ 0 = 0`;
* an axis-parallel rectangle in `ℝⁿ` (a product of bounded intervals, positive
  volume, **not** required to be centred at the point where it is used);
* the uncentered strong maximal function `Mₙ f` as the supremum of the averages
  of `|f|` over such rectangles containing `x`;
* the endpoint constant `Cₙ` as the supremum of `|{Mₙ f > 1}| / ∫ Φₙ(|f|)`.

Only the definitions and their immediate properties are given here: no theorem
of `StrongMaximal.Main` depends on this file, because the two-sided estimate is
carried there as an explicit hypothesis.  The homogeneity
`Mₙ (c · f) = c · Mₙ f` is what identifies the `λ`-form of the endpoint
inequality with the `λ = 1` form used to define `Cₙ`.
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal NNReal

/-- `log⁺ t = max (log t) 0`. -/
noncomputable def logPos (t : ℝ) : ℝ := max (Real.log t) 0

lemma logPos_nonneg (t : ℝ) : 0 ≤ logPos t := le_max_right _ _

/-- `Φₙ t = t (1 + log⁺ t)^{n-1}`, with `Φₙ 0 = 0` (automatic). -/
noncomputable def Phi (n : ℕ) (t : ℝ) : ℝ := t * (1 + logPos t) ^ (n - 1)

theorem Phi_zero (n : ℕ) : Phi n 0 = 0 := by simp [Phi]

theorem Phi_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Phi n t := by
  have h1 : (0:ℝ) ≤ 1 + logPos t := by linarith [logPos_nonneg t]
  exact mul_nonneg ht (pow_nonneg h1 _)

theorem Phi_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < Phi n t := by
  have h1 : (0:ℝ) < 1 + logPos t := by linarith [logPos_nonneg t]
  exact mul_pos ht (pow_pos h1 _)

theorem measurable_Phi (n : ℕ) : Measurable (fun t : ℝ => Phi n t) := by
  have h1 : Measurable fun t : ℝ => Real.log t := Real.measurable_log
  have h2 : Measurable fun t : ℝ => max (Real.log t) 0 := h1.max measurable_const
  have h3 : Measurable fun t : ℝ => (1 + max (Real.log t) 0) ^ (n - 1) :=
    (continuous_pow (n - 1)).measurable.comp (measurable_const.add h2)
  exact measurable_id.mul h3

/-- `Φₙ t = 0` iff `t = 0`, for `t ≥ 0`. -/
theorem Phi_eq_zero_iff (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : Phi n t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have h1 : (0:ℝ) < 1 + logPos t := by linarith [logPos_nonneg t]
    have h2 : 0 < (1 + logPos t) ^ (n - 1) := pow_pos h1 _
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt h2)
  · rintro rfl; exact Phi_zero n

/-- An axis-parallel rectangle in `ℝⁿ`: a product of bounded intervals of
positive length.  It is *not* required to be centred anywhere. -/
structure Rect (n : ℕ) where
  lo : Fin n → ℝ
  hi : Fin n → ℝ
  lt : ∀ i, lo i < hi i

namespace Rect

variable {n : ℕ}

/-- The carrier `∏ᵢ [loᵢ, hiᵢ]`. -/
def carrier (R : Rect n) : Set (Fin n → ℝ) := Set.Icc R.lo R.hi

/-- The Lebesgue volume `∏ᵢ (hiᵢ - loᵢ)`. -/
noncomputable def volume (R : Rect n) : ℝ := ∏ i, (R.hi i - R.lo i)

theorem volume_pos (R : Rect n) : 0 < R.volume :=
  Finset.prod_pos fun i _ => sub_pos.mpr (R.lt i)

end Rect

/-- The rectangles containing `x`. -/
def RectsAt (n : ℕ) (x : Fin n → ℝ) : Type := {R : Rect n // x ∈ Set.Icc R.lo R.hi}

/-- The uncentered strong maximal function: the supremum of `|f|`-averages over
axis-parallel rectangles of positive volume containing `x`. -/
noncomputable def strongMax (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ⨆ S : RectsAt n x,
    (∫⁻ y in Set.Icc S.1.lo S.1.hi, ENNReal.ofReal |f y|) / ENNReal.ofReal S.1.volume

/-- Homogeneity: `Mₙ (c · f) = c · Mₙ f` for `c ≥ 0`.  This is what makes the
`λ`-form of the endpoint inequality equivalent to its `λ = 1` form. -/
theorem strongMax_smul (n : ℕ) (f : (Fin n → ℝ) → ℝ) (c : ℝ≥0) (x : Fin n → ℝ) :
    strongMax n (fun y => (c : ℝ) * f y) x
      = ENNReal.ofReal (c : ℝ) * strongMax n f x := by
  unfold strongMax
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun S => ?_
  have hc : (0:ℝ) ≤ (c:ℝ) := c.2
  have h1 : ∀ y, ENNReal.ofReal |(c:ℝ) * f y| = ENNReal.ofReal (c:ℝ) * ENNReal.ofReal |f y| := by
    intro y
    rw [abs_mul, abs_of_nonneg hc, ENNReal.ofReal_mul hc]
  simp only [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_div_assoc]

/-- An input is admissible for the definition of `Cₙ` when it is measurable and
its `Φₙ`-modular is positive and finite. -/
def Admissible (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  Measurable f ∧
    0 < ∫⁻ x, ENNReal.ofReal (Phi n |f x|) ∧
      ∫⁻ x, ENNReal.ofReal (Phi n |f x|) ≠ ∞

/-- The endpoint constant `Cₙ` as the supremum of the `λ = 1` ratios. -/
noncomputable def endpointConst (n : ℕ) : ℝ≥0∞ :=
  ⨆ (f : (Fin n → ℝ) → ℝ) (_ : Admissible n f),
    volume {x | 1 < strongMax n f x} / ∫⁻ x, ENNReal.ofReal (Phi n |f x|)
/-- `log⁺ t = log t` once `t ≥ 1`. -/
lemma logPos_eq_log {t : ℝ} (ht : 1 ≤ t) : logPos t = Real.log t := by
  simp only [logPos]
  exact max_eq_left (Real.log_nonneg ht)

/-- `log⁺ t = 0` on `[0,1]`. -/
lemma logPos_eq_zero {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : logPos t = 0 := by
  simp only [logPos]
  exact max_eq_right (Real.log_nonpos h0 h1)

/-- `log⁺ (2t) ≤ log 2 + log⁺ t` for `t > 0`. -/
lemma logPos_two_mul {t : ℝ} (ht : 0 < t) :
    logPos (2 * t) ≤ Real.log 2 + logPos t := by
  rcases le_or_gt (2 * t) 1 with h | h
  · rw [logPos_eq_zero (by linarith) h]
    have := Real.log_pos (by norm_num : (1:ℝ) < 2)
    linarith [logPos_nonneg t]
  · rw [logPos_eq_log h.le, Real.log_mul (by norm_num) ht.ne']
    have hle : Real.log t ≤ logPos t := le_max_left _ _
    linarith

/-- **`Φₙ` is strictly increasing on `[0, ∞)`.**  On `[0,1]` it is the identity,
and on `[1,∞)` it is the product of the two strictly increasing positive
functions `t` and `(1 + log t)^{n-1}`. -/
theorem Phi_strictMonoOn (n : ℕ) : StrictMonoOn (Phi n) (Set.Ici 0) := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := hs
  have ht0 : 0 ≤ t := le_of_lt (lt_of_le_of_lt hs0 hst)
  rcases lt_or_ge s 1 with hs1 | hs1
  · have hPs : Phi n s = s := by simp [Phi, logPos_eq_zero hs0 hs1.le]
    rcases le_or_gt t 1 with ht1 | ht1
    · have hPt : Phi n t = t := by simp [Phi, logPos_eq_zero ht0 ht1]
      rw [hPs, hPt]; exact hst
    · have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hge : (1:ℝ) ≤ (1 + Real.log t) ^ (n - 1) := by
        simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1)
          (by linarith : (1:ℝ) ≤ 1 + Real.log t) (n - 1)
      have hPt : Phi n t = t * (1 + Real.log t) ^ (n - 1) := by
        simp [Phi, logPos_eq_log ht1.le]
      rw [hPs, hPt]
      nlinarith
  · have hst1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hs1 hst)
    have hPs : Phi n s = s * (1 + Real.log s) ^ (n - 1) := by
      simp [Phi, logPos_eq_log hs1]
    have hPt : Phi n t = t * (1 + Real.log t) ^ (n - 1) := by
      simp [Phi, logPos_eq_log hst1]
    have hbase : 0 < 1 + Real.log s := by linarith [Real.log_nonneg hs1]
    have hAle : (1 + Real.log s) ^ (n - 1) ≤ (1 + Real.log t) ^ (n - 1) :=
      pow_le_pow_left₀ hbase.le
        (by linarith [Real.log_le_log (by linarith : (0:ℝ) < s) hst.le]) (n - 1)
    have hpos : 0 < s * (1 + Real.log s) ^ (n - 1) :=
      mul_pos (by linarith) (pow_pos hbase _)
    rw [hPs, hPt]
    nlinarith [mul_le_mul_of_nonneg_left hAle ht0]

/-- **Doubling inequality for `Φₙ`**: `Φₙ(2t) ≤ 2(1+log 2)^{n-1} Φₙ(t)`. -/
theorem Phi_doubling (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Phi n (2 * t) ≤ 2 * (1 + Real.log 2) ^ (n - 1) * Phi n t := by
  rcases eq_or_lt_of_le ht with h | htpos
  · subst h; simp [Phi, logPos]
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hstep : 1 + logPos (2 * t) ≤ (1 + Real.log 2) * (1 + logPos t) := by
      have h1 := logPos_two_mul htpos
      have h2 : 0 ≤ logPos t := logPos_nonneg t
      nlinarith
    have hbase : 0 ≤ 1 + logPos t := by linarith [logPos_nonneg t]
    have hpow : (1 + logPos (2 * t)) ^ (n - 1)
        ≤ ((1 + Real.log 2) * (1 + logPos t)) ^ (n - 1) :=
      pow_le_pow_left₀ (by linarith [logPos_nonneg (2 * t)]) hstep (n - 1)
    have hpos : 0 ≤ (1 + Real.log 2) ^ (n - 1) := pow_nonneg (by linarith) _
    have hexp : ((1 + Real.log 2) * (1 + logPos t)) ^ (n - 1)
        = (1 + Real.log 2) ^ (n - 1) * (1 + logPos t) ^ (n - 1) :=
      mul_pow _ _ _
    simp only [Phi]
    rw [hexp] at hpow
    nlinarith [mul_le_mul_of_nonneg_left hpow ht, mul_nonneg ht hpos]


end StrongMaximalEndpoint
