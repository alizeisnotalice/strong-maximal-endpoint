/-
The plateau profile `H_w` of the lower-bound construction (manuscript §3).

  `H_w v = 0` for `v < 0`, `= 1` for `0 ≤ v ≤ w`, `= exp ((v-w)/n)` for `v > w`.

The step converting a strict level-set bound into a strict *average* bound is the
pointwise inequality

  `1_{v ≥ 0} + (v-w)₊/n ≤ H_w v`,

which is `e^y ≥ 1 + y` at `y = (v-w)/n` in the region `v > w`, and immediate
elsewhere.  In the application `w = L/2 + log L ≥ 0`, which is exactly the
hypothesis needed: for `v < 0` the inequality `v - w < 0` (hence `(v-w)₊ = 0`)
requires `w ≥ 0`.

`(v-w)₊` is written as `if 0 ≤ v - w then (v-w)/n else 0` so that every case is a
definitional split rather than a `max` computation.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace StrongMaximalEndpoint

open MeasureTheory
open scoped ENNReal

/-- The plateau profile, at height `1` on `[0,w]` and exponential growth beyond. -/
noncomputable def Hw (n : ℕ) (w v : ℝ) : ℝ :=
  if v < 0 then 0 else if v ≤ w then 1 else Real.exp ((v - w) / n)

theorem Hw_nonneg (n : ℕ) (w v : ℝ) : 0 ≤ Hw n w v := by
  unfold Hw
  split_ifs with h1 h2
  · exact le_rfl
  · exact zero_le_one
  · exact (Real.exp_pos _).le

/-- `H_w` is `1` on the plateau and `exp((v-w)/n)` beyond it. -/
theorem Hw_of_mem {n : ℕ} {w v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ w) : Hw n w v = 1 := by
  unfold Hw
  rw [if_neg (not_lt.mpr h1), if_pos h2]

theorem Hw_of_gt {n : ℕ} {w v : ℝ} (h1 : 0 ≤ v) (h2 : w < v) :
    Hw n w v = Real.exp ((v - w) / n) := by
  unfold Hw
  rw [if_neg (not_lt.mpr h1), if_neg (not_le.mpr h2)]

/-- **The plateau inequality** `1_{v ≥ 0} + (v-w)₊/n ≤ H_w v`, for `w ≥ 0`. -/
theorem Hw_ge_indicator (n : ℕ) (hn : 0 < n) {w : ℝ} (hw0 : 0 ≤ w) (v : ℝ) :
    (if 0 ≤ v then (1 : ℝ) else 0)
      + (if 0 ≤ v - w then (v - w) / (n : ℝ) else 0) ≤ Hw n w v := by
  rcases lt_or_ge v 0 with hv | hv
  · have hv' : ¬ (0 ≤ v) := not_le.mpr hv
    have hvw : ¬ (0 ≤ v - w) := by linarith
    rw [if_neg hv', if_neg hvw]
    unfold Hw
    rw [if_pos hv]
    simp
  · rcases le_or_gt v w with hvw | hvw
    · rw [if_pos hv, Hw_of_mem hv hvw]
      have hz : (if 0 ≤ v - w then (v - w) / (n : ℝ) else 0) ≤ 0 := by
        split_ifs with h
        · have h0 : v - w = 0 := le_antisymm (by linarith) h
          rw [h0]
          simp
        · exact le_rfl
      linarith
    · rw [if_pos hv, Hw_of_gt hv hvw, if_pos (show (0:ℝ) ≤ v - w by linarith)]
      linarith [Real.add_one_le_exp ((v - w) / n)]

/-- **The integrated plateau inequality** of the lower-bound construction:

  `𝔼 H_w(X - s) ≥ 1 - F(s) + (𝔼X - s - w)/n`,  `F(s) = P(X ≤ s)`,

for `w ≥ 0`, `X` integrable, and `H_w(X - s)` integrable (in the application `X` is
`Sₙ = Γ(n,1) + a·Bin(n,ρ)`, which has exponential moments). -/
theorem Hw_integral_ge {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) {w s : ℝ} (hw0 : 0 ≤ w) {X : Ω → ℝ}
    (hXm : Measurable X) (hX : Integrable X μ)
    (hH : Integrable (fun ω => Hw n w (X ω - s)) μ) :
    1 - μ.real {ω | X ω ≤ s} + (∫ ω, X ω ∂μ - s - w) / (n : ℝ)
      ≤ ∫ ω, Hw n w (X ω - s) ∂μ := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hset : MeasurableSet {ω | s ≤ X ω} := measurableSet_le measurable_const hXm
  have hpt : ∀ ω, (if 0 ≤ X ω - s then (1:ℝ) else 0)
      + (if 0 ≤ X ω - s - w then (X ω - s - w) / (n:ℝ) else 0) ≤ Hw n w (X ω - s) :=
    fun ω => Hw_ge_indicator n hn hw0 (X ω - s)
  have hind_eq : (fun ω => if 0 ≤ X ω - s then (1:ℝ) else 0)
      = {ω | s ≤ X ω}.indicator (fun _ => (1:ℝ)) := by
    funext ω
    have hiff : (0 ≤ X ω - s) ↔ (s ≤ X ω) := by constructor <;> intro h <;> linarith
    simp only [Set.indicator, Set.mem_setOf_eq, hiff]
  have hind : ∫ ω, (if 0 ≤ X ω - s then (1:ℝ) else 0) ∂μ = μ.real {ω | s ≤ X ω} := by
    rw [hind_eq]
    exact integral_indicator_one hset
  have hpos_eq : (fun ω => if 0 ≤ X ω - s - w then (X ω - s - w) / (n:ℝ) else 0)
      = fun ω => max (X ω - s - w) 0 / (n:ℝ) := by
    funext ω
    by_cases h : 0 ≤ X ω - s - w
    · rw [if_pos h, max_eq_left h]
    · rw [if_neg h, max_eq_right (by linarith : X ω - s - w ≤ 0)]
      simp
  have hpos : ∫ ω, (if 0 ≤ X ω - s - w then (X ω - s - w) / (n:ℝ) else 0) ∂μ
      = (∫ ω, max (X ω - s - w) 0 ∂μ) / (n:ℝ) := by
    rw [hpos_eq, integral_div]
  have hY : Integrable (fun ω => X ω - s - w) μ :=
    (hX.sub (integrable_const s)).sub (integrable_const w)
  have hInt_ind : Integrable (fun ω => if 0 ≤ X ω - s then (1:ℝ) else 0) μ := by
    rw [hind_eq]; exact (integrable_const (1:ℝ)).indicator hset
  have hInt_pos : Integrable (fun ω => if 0 ≤ X ω - s - w then (X ω - s - w) / (n:ℝ) else 0) μ := by
    rw [hpos_eq]
    exact (hY.pos_part).div_const _
  have hInt_sum : Integrable (fun ω => (if 0 ≤ X ω - s then (1:ℝ) else 0)
      + (if 0 ≤ X ω - s - w then (X ω - s - w) / (n:ℝ) else 0)) μ :=
    hInt_ind.add hInt_pos
  have hmono := integral_mono hInt_sum hH hpt
  have hsplit : ∫ ω, ((if 0 ≤ X ω - s then (1:ℝ) else 0)
      + (if 0 ≤ X ω - s - w then (X ω - s - w) / (n:ℝ) else 0)) ∂μ
      = μ.real {ω | s ≤ X ω} + (∫ ω, max (X ω - s - w) 0 ∂μ) / (n:ℝ) := by
    rw [integral_add hInt_ind hInt_pos, hind, hpos]
  have hYint : ∫ ω, (X ω - s - w) ∂μ = ∫ ω, X ω ∂μ - s - w := by
    have h1 : ∀ ω, X ω - s - w = X ω - (s + w) := fun ω => by ring
    simp only [h1]
    rw [integral_sub hX (integrable_const (s + w)), integral_const]
    have huniv : μ.real (Set.univ : Set Ω) = 1 := by simp
    rw [huniv, one_smul]
    ring
  have hlow : (∫ ω, X ω ∂μ - s - w) / (n:ℝ) ≤ (∫ ω, max (X ω - s - w) 0 ∂μ) / (n:ℝ) := by
    refine div_le_div_of_nonneg_right ?_ hn'.le
    rw [← hYint]
    exact integral_mono hY hY.pos_part (fun ω => le_max_left _ _)
  have hreal : 1 - μ.real {ω | X ω ≤ s} ≤ μ.real {ω | s ≤ X ω} := by
    have hcompl := measureReal_add_measureReal_compl (μ := μ) (s := {ω | X ω ≤ s})
      (measurableSet_le hXm measurable_const)
    have hc : ({ω | X ω ≤ s}ᶜ : Set Ω) = {ω | s < X ω} := by
      ext ω; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hc] at hcompl
    have huniv : μ.real (Set.univ : Set Ω) = 1 := by simp
    rw [huniv] at hcompl
    have hsub : μ.real {ω | s < X ω} ≤ μ.real {ω | s ≤ X ω} := by
      refine measureReal_mono ?_ (by finiteness)
      intro ω h
      simp only [Set.mem_setOf_eq] at h ⊢
      linarith
    linarith
  calc 1 - μ.real {ω | X ω ≤ s} + (∫ ω, X ω ∂μ - s - w) / (n:ℝ)
      ≤ μ.real {ω | s ≤ X ω} + (∫ ω, max (X ω - s - w) 0 ∂μ) / (n:ℝ) := by linarith
    _ = ∫ ω, ((if 0 ≤ X ω - s then (1:ℝ) else 0)
          + (if 0 ≤ X ω - s - w then (X ω - s - w) / (n:ℝ) else 0)) ∂μ := hsplit.symm
    _ ≤ ∫ ω, Hw n w (X ω - s) ∂μ := hmono

end StrongMaximalEndpoint
