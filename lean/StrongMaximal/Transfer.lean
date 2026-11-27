/-
Transfer of the two-sided estimates across the comparison bridge
`Qₙ ≤ Cₙ ≤ Rₙ` of the manuscript (Lemma 2).

The bridge itself — the part of §2 that builds the fixed-action model `Qₙ`, the
past-dependent model `ℛₙ`, and proves `Qₙ ≤ Cₙ ≤ ℛₙ` — is **not** formalised; it
enters here as the explicit hypothesis `Bridge Q R`.  What is proved is that
this hypothesis does what the paper needs:

* `twoSided_of_sandwich`: if `0 < Qₙ ≤ Cₙ ≤ Rₙ` eventually, the lower estimate
  for `Q` and the upper estimate for `R` transfer to `C`;
* `endpointConst_main`: hence Theorem 1.1 holds for `(endpointConst n).toReal`
  given the bridge and the two one-sided estimates;
* `endpointConst_second_order`: likewise the `√(n log n)` coefficient.
-/
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import StrongMaximal.Main
import StrongMaximal.Endpoint
import StrongMaximal.SecondOrder

namespace StrongMaximalEndpoint

open Filter
open scoped Topology

/-- Pointwise sandwich transfer of the two-sided estimate. -/
theorem twoSided_of_sandwich {Q C R : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, 0 < Q n ∧ Q n ≤ C n ∧ C n ≤ R n)
    (hQ : ∀ ε > 0, ∀ᶠ n in atTop, cLo - ε ≤ Eexp Q n)
    (hR : ∀ ε > 0, ∀ᶠ n in atTop, Eexp R n ≤ cHi + ε) :
    TwoSidedEventual C := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact Real.log_pos hn1
  constructor
  · intro ε hε
    filter_upwards [h, hQ ε hε, hlog] with n hn hq hL
    have hlogQC : Real.log (Q n) ≤ Real.log (C n) := Real.log_le_log hn.1 hn.2.1
    have hnum : Real.log (Q n) - (n : ℝ) * mu + dOf n
        ≤ Real.log (C n) - (n : ℝ) * mu + dOf n := by linarith
    have hdiv := div_le_div_of_nonneg_right hnum hL.le
    simp only [Eexp]
    exact le_trans hq hdiv
  · intro ε hε
    filter_upwards [h, hR ε hε, hlog] with n hn hr hL
    have hlogCR : Real.log (C n) ≤ Real.log (R n) :=
      Real.log_le_log (lt_of_lt_of_le hn.1 hn.2.1) hn.2.2
    have hnum : Real.log (C n) - (n : ℝ) * mu + dOf n
        ≤ Real.log (R n) - (n : ℝ) * mu + dOf n := by linarith
    have hdiv := div_le_div_of_nonneg_right hnum hL.le
    simp only [Eexp]
    exact le_trans hdiv hr

/-- The comparison bridge `Qₙ ≤ Cₙ ≤ Rₙ` of the manuscript, for the endpoint
constant read as a real number. -/
def Bridge (Q R : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, 0 < Q n ∧ Q n ≤ (endpointConst n).toReal ∧ (endpointConst n).toReal ≤ R n

/-- **Theorem 1.1 for the endpoint constant**, conditional on the bridge and on
the two one-sided estimates for the models `Qₙ` and `Rₙ`. -/
theorem endpointConst_main {Q R : ℕ → ℝ} (h : Bridge Q R)
    (hQ : ∀ ε > 0, ∀ᶠ n in atTop, cLo - ε ≤ Eexp Q n)
    (hR : ∀ ε > 0, ∀ᶠ n in atTop, Eexp R n ≤ cHi + ε) :
    cLo ≤ liminf (Eexp fun n => (endpointConst n).toReal) atTop ∧
      liminf (Eexp fun n => (endpointConst n).toReal) atTop
        ≤ limsup (Eexp fun n => (endpointConst n).toReal) atTop ∧
      limsup (Eexp fun n => (endpointConst n).toReal) atTop ≤ cHi :=
  main_theorem _ (twoSided_of_sandwich h hQ hR)

/-- **Second-order coefficient for the endpoint constant**: from the `O(log n)`
sandwich for `log Cₙ` one gets `(μn - log Cₙ)/√(n log n) → √μ`. -/
theorem endpointConst_second_order {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ᶠ n in atTop,
      |Real.log ((endpointConst n).toReal) - ((n : ℝ) * mu - dOf n)| ≤ K * Real.log (n : ℝ)) :
    Tendsto (fun n : ℕ => ((n : ℝ) * mu - Real.log ((endpointConst n).toReal))
      / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 (Real.sqrt mu)) :=
  second_order_coefficient _ hK h

/-- **The second-order coefficient for `Cₙ`, derived from Theorem 1.1**: given
the bridge and the two one-sided estimates, the exponent of `Cₙ` has second term
`-√μ √(n log n)`.  This is the manuscript's second goal, and it now follows from
`endpointConst_main`'s two-sided estimate rather than being assumed. -/
theorem endpointConst_second_order_of_bridge {Q R : ℕ → ℝ} (h : Bridge Q R)
    (hQ : ∀ ε > 0, ∀ᶠ n in atTop, cLo - ε ≤ Eexp Q n)
    (hR : ∀ ε > 0, ∀ᶠ n in atTop, Eexp R n ≤ cHi + ε) :
    Tendsto (fun n : ℕ => ((n : ℝ) * mu - Real.log ((endpointConst n).toReal))
      / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 (Real.sqrt mu)) :=
  second_order_of_twoSided (twoSided_of_sandwich h hQ hR)

end StrongMaximalEndpoint
