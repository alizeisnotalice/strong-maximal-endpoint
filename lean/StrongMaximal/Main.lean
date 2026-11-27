/-
Theorem 1.1 of the v1 manuscript, as a reduction.

The analytic content of the paper enters through the two-sided estimate with
explicit constants. Everything after that is order theory and is proved here
unconditionally:

* the `ε`-form (every `ε > 0`, all large `n`) implies the `liminf`/`limsup`
  form printed in the manuscript;
* the ordering `cLo ≤ liminf ≤ limsup ≤ cHi`;
* the window has width `g = (μ-1)/8`.
-/
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import StrongMaximal.Constants
import StrongMaximal.Gaussian

namespace StrongMaximalEndpoint

open Filter
open scoped Topology

/-- The normalized exponent `Eₙ = (log Cₙ - nμ + dₙ) / log n` of the manuscript. -/
noncomputable def Eexp (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Real.log (C n) - (n : ℝ) * mu + dOf n) / Real.log n

/-- The `ε`-form of the two-sided estimate: every `ε > 0` works for all large `n`. -/
def TwoSidedEventual (C : ℕ → ℝ) : Prop :=
  (∀ ε > 0, ∀ᶠ n in atTop, cLo - ε ≤ Eexp C n) ∧
    (∀ ε > 0, ∀ᶠ n in atTop, Eexp C n ≤ cHi + ε)

lemma boundedUnder_of_eventually_le {u : ℕ → ℝ} {K : ℝ}
    (h : ∀ᶠ n in atTop, u n ≤ K) :
    IsBoundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) atTop u :=
  ⟨K, Filter.eventually_map.mpr h⟩

lemma boundedUnder_of_eventually_ge {u : ℕ → ℝ} {K : ℝ}
    (h : ∀ᶠ n in atTop, K ≤ u n) :
    IsBoundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) atTop u :=
  ⟨K, Filter.eventually_map.mpr h⟩

/-- A sequence that is eventually `≤ K` does not tend to `+∞`. -/
lemma isCoboundedUnder_of_eventually_le {u : ℕ → ℝ} {K : ℝ}
    (h : ∀ᶠ n in atTop, u n ≤ K) :
    IsCoboundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) atTop u := by
  refine ⟨K + 1, fun a ha => ?_⟩
  have h' : ∀ᶠ x in map u atTop, x ≤ K := Filter.eventually_map.mpr h
  obtain ⟨x, hxK, hax⟩ := (h'.and ha).exists
  linarith

/-- A sequence that is eventually `≥ K` does not tend to `-∞`. -/
lemma isCoboundedUnder_of_eventually_ge {u : ℕ → ℝ} {K : ℝ}
    (h : ∀ᶠ n in atTop, K ≤ u n) :
    IsCoboundedUnder (fun x1 x2 : ℝ => x1 ≤ x2) atTop u := by
  refine ⟨K - 1, fun a ha => ?_⟩
  have h' : ∀ᶠ x in map u atTop, K ≤ x := Filter.eventually_map.mpr h
  obtain ⟨x, hKx, hxa⟩ := (h'.and ha).exists
  linarith

/-- `ε`-form ⟹ `cLo ≤ liminf`. -/
theorem cLo_le_liminf {C : ℕ → ℝ} (h : TwoSidedEventual C) :
    cLo ≤ liminf (Eexp C) atTop := by
  rw [le_liminf_iff
    (isCoboundedUnder_of_eventually_le (h.2 1 zero_lt_one))
    (isBoundedUnder_of_eventually_ge (h.1 1 zero_lt_one))]
  intro y hy
  have hε : 0 < cLo - y := by linarith
  filter_upwards [h.1 ((cLo - y) / 2) (by linarith)] with n hn
  linarith

/-- `ε`-form ⟹ `limsup ≤ cHi`. -/
theorem limsup_le_cHi {C : ℕ → ℝ} (h : TwoSidedEventual C) :
    limsup (Eexp C) atTop ≤ cHi := by
  rw [limsup_le_iff
    (isCoboundedUnder_of_eventually_ge (h.1 1 zero_lt_one))
    (isBoundedUnder_of_eventually_le (h.2 1 zero_lt_one))]
  intro y hy
  have hε : 0 < y - cHi := by linarith
  filter_upwards [h.2 ((y - cHi) / 2) (by linarith)] with n hn
  linarith

/-- **Theorem 1.1** (reduction form): the two-sided `ε`-estimate implies the
`liminf`/`limsup` chain printed in the manuscript. -/
theorem main_theorem (C : ℕ → ℝ) (h : TwoSidedEventual C) :
    cLo ≤ liminf (Eexp C) atTop ∧
      liminf (Eexp C) atTop ≤ limsup (Eexp C) atTop ∧
      limsup (Eexp C) atTop ≤ cHi := by
  refine ⟨cLo_le_liminf h, ?_, limsup_le_cHi h⟩
  exact liminf_le_limsup
    (boundedUnder_of_eventually_le (h.2 1 zero_lt_one))
    (boundedUnder_of_eventually_ge (h.1 1 zero_lt_one))

/-- The window has width `g = (μ-1)/8`, the number `0.0348…` of the manuscript. -/
theorem window_width : cHi - cLo = g := by
  rw [← cLo_add_g]; ring

/-- The `O(log n)` sandwich makes the normalized exponent bounded, i.e.
`log Cₙ = nμ - dₙ + O(log n)`.  This is the input of the second-order corollary. -/
theorem abs_Eexp_le_of_sandwich {C : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ᶠ n in atTop, |Real.log (C n) - ((n : ℝ) * mu - dOf n)| ≤ K * Real.log (n : ℝ)) :
    ∀ᶠ n in atTop, |Eexp C n| ≤ K := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos hn1
  filter_upwards [h, hlog] with n hn hpos
  have hrew : Eexp C n = (Real.log (C n) - ((n : ℝ) * mu - dOf n)) / Real.log (n : ℝ) := by
    simp only [Eexp]; ring
  rw [hrew, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |Real.log (C n) - ((n : ℝ) * mu - dOf n)|
      ≤ K * Real.log (n : ℝ) := hn
    _ = K * Real.log (n : ℝ) := rfl

/-- Converse direction: the printed `liminf`/`limsup` chain implies the
`ε`-form.  Boundedness of `Eₙ` is needed for `liminf`/`limsup` to be the genuine
eventual bounds; it is supplied by the `O(log n)` sandwich in applications. -/
theorem twoSided_of_liminf_limsup {C : ℕ → ℝ} {K : ℝ}
    (hsand : ∀ᶠ n in atTop, |Eexp C n| ≤ K)
    (h1 : cLo ≤ liminf (Eexp C) atTop) (h2 : limsup (Eexp C) atTop ≤ cHi) :
    TwoSidedEventual C := by
  have hupper : ∀ᶠ n in atTop, Eexp C n ≤ K := by
    filter_upwards [hsand] with n hn using (abs_le.mp hn).2
  have hlower : ∀ᶠ n in atTop, -K ≤ Eexp C n := by
    filter_upwards [hsand] with n hn using (abs_le.mp hn).1
  constructor
  · intro ε hε
    have h := (le_liminf_iff
      (isCoboundedUnder_of_eventually_le hupper)
      (isBoundedUnder_of_eventually_ge hlower)).mp h1 (cLo - ε) (by linarith)
    filter_upwards [h] with n hn
    linarith
  · intro ε hε
    have h := (limsup_le_iff
      (isCoboundedUnder_of_eventually_ge hlower)
      (isBoundedUnder_of_eventually_le hupper)).mp h2 (cHi + ε) (by linarith)
    filter_upwards [h] with n hn
    linarith

/-- **The two formulations are equivalent** (for bounded `Eₙ`): the `ε`-form used
as the working statement and the `liminf`/`limsup` chain printed in the
manuscript. -/
theorem twoSided_iff_liminf_limsup {C : ℕ → ℝ} {K : ℝ}
    (hsand : ∀ᶠ n in atTop, |Eexp C n| ≤ K) :
    TwoSidedEventual C ↔
      cLo ≤ liminf (Eexp C) atTop ∧ limsup (Eexp C) atTop ≤ cHi := by
  constructor
  · intro h
    exact ⟨cLo_le_liminf h, limsup_le_cHi h⟩
  · rintro ⟨h1, h2⟩
    exact twoSided_of_liminf_limsup hsand h1 h2

/-- **The `O(log n)` form follows from the two-sided estimate.**  Taking
`ε = 1` in `TwoSidedEventual` and multiplying by `log n > 0` gives
`|log Cₙ - (nμ - dₙ)| ≤ 2 log n` for all large `n`.  This is the manuscript's
`log Cₙ = nμ - dₙ + O(log n)`, derived rather than assumed. -/
theorem sandwich_of_twoSided {C : ℕ → ℝ} (h : TwoSidedEventual C) :
    ∀ᶠ n in atTop,
      |Real.log (C n) - ((n : ℝ) * mu - dOf n)| ≤ 2 * Real.log (n : ℝ) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos hn1
  have hexp : ∀ n, Eexp C n
      = (Real.log (C n) - ((n : ℝ) * mu - dOf n)) / Real.log (n : ℝ) := by
    intro n; simp only [Eexp]; ring
  filter_upwards [h.1 1 zero_lt_one, h.2 1 zero_lt_one, hlog] with n h1 h2 hL
  rw [hexp n] at h1 h2
  have h1' : (cLo - 1) * Real.log (n : ℝ)
      ≤ Real.log (C n) - ((n : ℝ) * mu - dOf n) := by
    rw [le_div_iff₀ hL] at h1
    linarith
  have h2' : Real.log (C n) - ((n : ℝ) * mu - dOf n)
      ≤ (cHi + 1) * Real.log (n : ℝ) := by
    rw [div_le_iff₀ hL] at h2
    linarith
  rw [abs_le]
  constructor
  · nlinarith [cLo_pos, hL]
  · nlinarith [cHi_lt_one, hL]

end StrongMaximalEndpoint
