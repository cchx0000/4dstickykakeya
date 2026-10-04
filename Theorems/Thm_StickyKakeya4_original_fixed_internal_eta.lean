import Theorems.Thm_StickyKakeya4_planar_frostman_ball_conversion
import Theorems.Thm_StickyKakeya4_original_pair_strip_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

noncomputable section
namespace OriginalFixedInternalEta
open Classical OriginalPairStripGeometry PlanarFrostmanBallConversion

/-- Every admissible external input profile weakens to the one fixed
internal exponent on the SAME original point source. -/
theorem original_frostman_to_fixed_internal_eta
    (Pts : Finset Point) (delta t eta etaI : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (hetaI : 0≤etaI) (heta : eta≤etaI/2)
    (hsource : ∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-eta)*R^t*Pts.card) :
    ∀ q∈Pts, ∀ R : ℝ, delta≤R → R≤1 →
      ((Pts.filter (fun v => euclideanDistance q v≤R)).card : ℝ)≤delta^(-etaI)*R^t*Pts.card := by
  have he : eta≤etaI := by linarith only [heta,hetaI]
  have hpow : delta^(-eta)≤delta^(-etaI) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg he)
  intro q hq R hR hR1
  exact (hsource q hq R hR hR1).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (hd.le.trans hR) t))
      (Nat.cast_nonneg Pts.card))

/-- One fixed internal discarded-pair exponent dominates every allowed
external exponent, with no eta-dependent scale cutoff. -/
theorem fixed_internal_error_power_le_external
    (delta eta etaI : ℝ) (hd : 0<delta) (hd1 : delta≤1) (heta : eta≤etaI/2) :
    delta^(etaI/2)≤delta^eta :=
  Real.rpow_le_rpow_of_exponent_ge hd hd1 heta

/-- Quantitative discarded mass is compared on the same original P². -/
theorem original_pair_error_to_external_eta
    (Pts : Finset Point) (Bad : Finset Pair) (delta eta etaI : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta : eta≤etaI/2)
    (hbad : (Bad.card : ℝ)≤delta^(etaI/2)*(Pts.card : ℝ)^2) :
    (Bad.card : ℝ)≤delta^eta*(Pts.card : ℝ)^2 :=
  hbad.trans (mul_le_mul_of_nonneg_right
    (fixed_internal_error_power_le_external delta eta etaI hd hd1 heta) (sq_nonneg _))

/-- A fixed-internal-eta good original graph has the requested external
retention fraction, again without changing the source cardinality. -/
theorem original_pair_retention_to_external_eta
    (Pts : Finset Point) (Good : Finset Pair) (delta eta etaI : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta : eta≤etaI/2)
    (hgood : (1-delta^(etaI/2))*(Pts.card : ℝ)^2≤(Good.card : ℝ)) :
    (1-delta^eta)*(Pts.card : ℝ)^2≤(Good.card : ℝ) := by
  have hh := fixed_internal_error_power_le_external delta eta etaI hd hd1 heta
  exact (mul_le_mul_of_nonneg_right (by linarith only [hh]) (sq_nonneg (Pts.card : ℝ))).trans hgood

end OriginalFixedInternalEta
