/-
Formalisation accompanying

  "High-dimensional bounds for the optimal endpoint constant of the uncentered
   strong maximal operator" (v1.0.0, tag `v1.0.0`).

Module map (see `report.md` for the statement-by-statement comparison table):

* `StrongMaximal.Constants`  -- `μ`, `g`, `cLo`, `cHi`, the identity `cLo + g = cHi`
* `StrongMaximal.ExpModel`   -- `∫₀^∞ x e^{-x} = 1`, mean of `expMeasure 1`
* `StrongMaximal.Gaussian`   -- `φ`, `Φ̄`, `zₙ`, `dₙ`
* `StrongMaximal.Basic`      -- `Φₙ`, axis-parallel rectangles, `Mₙ`, `Cₙ`
* `StrongMaximal.Cumulants`  -- one-step cumulants at `a = μ`
* `StrongMaximal.StepModel`  -- the increment law `Exp 1 + a·Ber(ρ a)` and its mean
* `StrongMaximal.NStepModel` -- `Sₙ = ∑_{i<n} Z_a` and `∫ Sₙ = n·m(a)`
* `StrongMaximal.Variance`   -- `E[Z_a²]`, `Var(Z_a) = vStep a`
* `StrongMaximal.ExpMoment`  -- exponential moments of `Z_a` and `Sₙ`
* `StrongMaximal.HwModel`    -- the plateau inequality instantiated on `Sₙ`
* `StrongMaximal.Threshold`  -- plateau width, monotonicity, CDF threshold criterion
* `StrongMaximal.Mills`      -- two-sided Mills bounds for `Φ̄`
* `StrongMaximal.Zeta`       -- `zₙ → ∞` and `zₙ²/log n → 1`
* `StrongMaximal.Endpoint`   -- `Cₙ` as the least admissible coefficient
* `StrongMaximal.Plateau`    -- the plateau profile `H_w` and its inequality
* `StrongMaximal.Transfer`   -- the bridge `Qₙ ≤ Cₙ ≤ Rₙ` and Theorem 1.1 for `Cₙ`
* `StrongMaximal.TestInput`  -- an explicit admissible input; `Cₙ ≠ 0`; `Cₙ` is least
* `StrongMaximal.Main`       -- Theorem 1.1 as a reduction
* `StrongMaximal.SecondOrder`-- the `√(n log n)` coefficient
* `StrongMaximal.RankRat`    -- the rational rank-CDF inversion archived with v1.0.0
* `StrongMaximal.Audit`      -- `#print axioms` for every top-level declaration
-/
import StrongMaximal.Constants
import StrongMaximal.ExpModel
import StrongMaximal.Gaussian
import StrongMaximal.Basic
import StrongMaximal.Cumulants
import StrongMaximal.StepModel
import StrongMaximal.NStepModel
import StrongMaximal.Variance
import StrongMaximal.ExpMoment
import StrongMaximal.HwModel
import StrongMaximal.Threshold
import StrongMaximal.Mills
import StrongMaximal.Zeta
import StrongMaximal.Main
import StrongMaximal.SecondOrder
import StrongMaximal.Endpoint
import StrongMaximal.Transfer
import StrongMaximal.TestInput
import StrongMaximal.Plateau
import StrongMaximal.RankRat

/-!
The two top-level goals of the task are `StrongMaximalEndpoint.main_theorem`
(Theorem 1.1, reduction form) and
`StrongMaximalEndpoint.second_order_coefficient`.  Both are proved from explicit
hypotheses; `report.md` records which of those hypotheses are formalised
elsewhere in this development and which remain open.
-/
