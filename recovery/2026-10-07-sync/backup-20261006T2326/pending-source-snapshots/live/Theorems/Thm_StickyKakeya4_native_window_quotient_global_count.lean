import Theorems.Thm_StickyKakeya4_native_window_quotient_transport

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeWindowQuotientGlobalCount
open Classical Finset NativeWindowXYLabels NativeWindowXFibers NativeTwoMapRetainedSliceLabels
open NativeWindowQuotientTransport NativeQuotientLatticeTransport NativeQuotientLatticeCounts
open NativeEncodedQuotientAD NativeQuotientGridCenters NativeSliceClassBalls GridQuotientAD
open FiniteVoronoiRealADCoarsening

lemma global_coefficient_le {k l : ℕ} {lam K t : ℝ} (hlam : 0 < lam) (hK : 0 < K)
    (hkt : (k:ℝ) ≤ t) : (5:ℝ)^(k+l)*K/lam ≤ quotientConstant k l lam K t := by
  have hh : (1:ℝ) ≤ (2:ℝ)^(t-k) := Real.one_le_rpow (by norm_num) (sub_nonneg.mpr hkt)
  unfold quotientConstant NativeHalfScaleInterpolation.constant
  have hg : 0 ≤ max ((3:ℝ)^k*(2:ℝ)^(k+l)*K/lam) ((5:ℝ)^(k+l)*K/lam) := by positivity
  exact (le_max_right _ _).trans ((le_mul_of_one_le_left hg hh).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

/-- The whole quotient count uses the finite support cover and genuine
X-fiber population; it does not assert that one unit ball contains the set. -/
theorem global_count_of_encoded_AD {k l : ℕ} (hd : k+l=3)
    (S : Finset (XY k l)) (height : ℤ) (N : ℕ) (hN : 1 ≤ N)
    {mesh lam K t : ℝ} (hmesh : 0 < mesh) (hlam : 0 < lam) (hK : 0 < K)
    (hscale : mesh*(N:ℝ)=1/2) (hkt : (k:ℝ) ≤ t)
    (hx : ∀p∈productSlice S height,∀i,|p.1 i| ≤ (N:ℤ))
    (hy : ∀p∈productSlice S height,∀i,|p.2 i| ≤ ((2*N:ℕ):ℤ))
    (hdense : ∀y∈(productSlice S height).image Prod.snd,
      lam*(N:ℝ)^k ≤ ((fiber (productSlice S height) y).card:ℝ))
    (H : ADBounds (realizedSlice (S.image (encode hd)) mesh height) mesh K t) :
    (((productSlice S height).image Prod.snd).card:ℝ) ≤
      quotientConstant k l lam K t*(N:ℝ)^(t-k) := by
  have hlocal (p) (hp : p∈productSlice S height) :
      ((ambientBox (productSlice S height) p N).card:ℝ) ≤ K*(N:ℝ)^t :=
    (ambient_bounds_of_AD hd S height hmesh H p hp N hN (by rw [hscale]; norm_num)).2
  have htotal := global_card_le (productSlice S height) N hN (K*(N:ℝ)^t) (by positivity)
    (fun p hp j => (hx p hp j).trans (by omega)) hy hlocal
  have htotal' : ((productSlice S height).card:ℝ) ≤ ((5:ℝ)^(k+l)*K)*(N:ℝ)^t := by
    simpa only [mul_assoc] using htotal
  have hh := global_quotient_card_le (productSlice S height) N hN lam ((5:ℝ)^(k+l)*K) t hlam htotal' hdense
  exact hh.trans (mul_le_mul_of_nonneg_right (global_coefficient_le hlam hK hkt) (by positivity))

/-- The same global bound at every genuine coarse height window follows
from the original fine fibers, with the SAME quotient AD constant. -/
theorem window_global_count {k l : ℕ} (hd : k+l=3)
    (S : Finset (XY k l)) (H R Nfine Ncoarse : ℕ) (hR : 0 < R) (hN : Nfine=Ncoarse*R)
    (hNc : 1 ≤ Ncoarse) {mesh lam K t : ℝ}
    (hmesh : 0 < mesh) (hlam : 0 < lam) (hK : 0 < K)
    (hscale : mesh*(Nfine:ℝ)=1/2) (hkt : (k:ℝ) ≤ t)
    (hx : ∀z∈S,∀i,|z.2.1 i| ≤ (Nfine:ℤ))
    (hy : ∀z∈S,∀i,|z.2.2 i| ≤ ((2*Nfine:ℕ):ℤ))
    (HX : ∀z∈S,lam*(Nfine:ℝ)^k ≤ ((fiber (productSlice S z.1) z.2.2).card:ℝ))
    (HXY : ∀height : ℤ,ADBounds
      (realizedSlice ((S.image (window H R)).image (encode hd)) (mesh*(R:ℝ)) height)
      (mesh*(R:ℝ)) K t) :
    ∀height : ℤ,(((productSlice (S.image (window H R)) height).image Prod.snd).card:ℝ) ≤
      quotientConstant k l lam K t*(Ncoarse:ℝ)^(t-k) := by
  have hscaled : (mesh*(R:ℝ))*(Ncoarse:ℝ)=1/2 := by
    rw [hN,Nat.cast_mul] at hscale
    nlinarith only [hscale]
  have hden := window_fiber_density S H R Nfine Ncoarse hR hN lam HX
  intro height
  have hsup := window_support S H R Nfine Ncoarse hR hN hx hy height
  exact global_count_of_encoded_AD hd (S.image (window H R)) height Ncoarse hNc
    (by positivity) hlam hK hscaled hkt hsup.1 hsup.2 (hden height) (HXY height)

end NativeWindowQuotientGlobalCount
