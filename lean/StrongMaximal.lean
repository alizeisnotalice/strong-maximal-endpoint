import Std

namespace StrongMaximalEndpoint

/-- The two affine constraints in the inversion of the rank CDF. -/
theorem cdf_threshold (v r a : Rat) :
    a ≤ v + min v r ↔ max (a / 2) (a - r) ≤ v := by
  grind

/-- The rank CDF formula in the manuscript, before restricting the argument to [0,1]. -/
def rankCDF (r v : Rat) : Rat := (v + min v r) / (1 + r)

/-- The rank quantile formula in the manuscript. -/
def rankQuantile (r t : Rat) : Rat := max ((1 + r) * t / 2) ((1 + r) * t - r)

/-- Inversion of the rank CDF over the rationals with a positive denominator. -/
theorem rank_cdf_threshold (r t v : Rat) (hr : 0 < 1 + r) :
    t ≤ rankCDF r v ↔ rankQuantile r t ≤ v := by
  have hden : 1 + r ≠ 0 := by grind
  have hcancel := Rat.div_mul_cancel (a := v + min v r) hden
  constructor
  · intro h
    have hmul := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hr)
    rw [rankCDF, hcancel] at hmul
    exact (cdf_threshold v r ((1 + r) * t)).mp (by grind)
  · intro h
    have hmul := (cdf_threshold v r ((1 + r) * t)).mpr h
    apply Rat.le_of_mul_le_mul_right (c := 1 + r) _ hr
    rw [rankCDF, hcancel]
    grind

end StrongMaximalEndpoint

#print axioms StrongMaximalEndpoint.cdf_threshold
#print axioms StrongMaximalEndpoint.rank_cdf_threshold
