import Theorems.Thm_StickyKakeya4_native_window_X_fibers
import Theorems.Thm_StickyKakeya4_native_encoded_quotient_ad
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_support

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
namespace NativeWindowQuotientTransport
open Classical Finset NativeWindowXYLabels NativeWindowXFibers NativeTwoMapRetainedSliceLabels
open NativeQuotientLatticeTransport NativeEncodedQuotientAD NativeQuotientGridCenters
open NativeReferenceXYGridPoints NativeReferenceXYGridSupport NativeSquaredGrainQueries
open NativeSliceClassBalls GridQuotientAD FiniteVoronoiRealADCoarsening

/-- Horizontal coarsening from the genuine finest XY mesh. -/
def factor (m f : ℕ) : ℕ := 2^(phaseDepth m-f)

/-- The integer half-width at a prepared physical window radius. -/
def windowHalfWidth (m f : ℕ) : ℕ := 2^(f-m+5)

lemma width_factorization (m f : ℕ) (hm : 6 ≤ m) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m) :
    halfWidth m=windowHalfWidth m f*factor m f := by
  unfold halfWidth windowHalfWidth factor
  rw [←pow_add]
  congr 1
  unfold phaseDepth at hfb ⊢
  omega

lemma window_mesh_halfWidth (m f : ℕ) (hm : 6 ≤ m) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m) :
    (mu m*(factor m f:ℝ))*(windowHalfWidth m f:ℝ)=1/2 := by
  have hh := mu_halfWidth m (by omega)
  rw [width_factorization m f hm hmf hfb,Nat.cast_mul] at hh
  nlinarith only [hh]

lemma abs_ediv_bound {x : ℤ} {N R : ℕ} (hR : 0 < R) (hx : |x| ≤ ((N*R:ℕ):ℤ)) :
    |x/(R:ℤ)| ≤ (N:ℤ) := by
  have hp : (0:ℤ)<R := by exact_mod_cast hR
  rw [Nat.cast_mul] at hx
  apply abs_le.mpr
  exact ⟨Int.le_ediv_of_mul_le hp (by nlinarith only [(abs_le.mp hx).1]),
    Int.ediv_le_of_le_mul hp (abs_le.mp hx).2⟩

/-- Actual ambient support survives integer coarsening without a rounding
loss, because the old half-width is an exact multiple of the new one. -/
lemma window_support {k l : ℕ} (S : Finset (XY k l)) (H R Nfine Ncoarse : ℕ)
    (hR : 0 < R) (hN : Nfine=Ncoarse*R)
    (hx : ∀z∈S,∀i,|z.2.1 i| ≤ (Nfine:ℤ))
    (hy : ∀z∈S,∀i,|z.2.2 i| ≤ ((2*Nfine:ℕ):ℤ)) (height : ℤ) :
    (∀p∈productSlice (S.image (window H R)) height,∀i,|p.1 i| ≤ (Ncoarse:ℤ)) ∧
    (∀p∈productSlice (S.image (window H R)) height,∀i,|p.2 i| ≤ ((2*Ncoarse:ℕ):ℤ)) := by
  constructor
  · intro p hp i
    simp only [productSlice,mem_image,mem_filter] at hp
    obtain ⟨w,⟨⟨z,hz,rfl⟩,_hh⟩,rfl⟩ := hp
    apply abs_ediv_bound hR
    simpa only [hN] using hx z hz i
  · intro p hp i
    simp only [productSlice,mem_image,mem_filter] at hp
    obtain ⟨w,⟨⟨z,hz,rfl⟩,_hh⟩,rfl⟩ := hp
    apply abs_ediv_bound hR
    simpa only [hN,Nat.mul_assoc] using hy z hz i

/-- Quotient AD for the literal coarse Y union. Its tangent population is
computed from whole fine X fibers, and the radius through twice the half-width
is justified by the exact rescaled mesh identity. -/
theorem window_quotient_AD {k l : ℕ} (hd : k+l=3)
    (S : Finset (XY k l)) (H R Nfine Ncoarse : ℕ) (hR : 0 < R) (hN : Nfine=Ncoarse*R)
    (hNc : 1 ≤ Ncoarse) {mesh lambda K t : ℝ}
    (hmesh : 0 < mesh) (hlambda : 0 < lambda) (hK : 0 < K)
    (hscale : mesh*(Nfine:ℝ)=1/2) (hkt : (k:ℝ) ≤ t) (ht : t ≤ ((k+l:ℕ):ℝ))
    (hx : ∀z∈S,∀i,|z.2.1 i| ≤ (Nfine:ℤ))
    (hy : ∀z∈S,∀i,|z.2.2 i| ≤ ((2*Nfine:ℕ):ℤ))
    (HX : ∀z∈S,lambda*(Nfine:ℝ)^k ≤ ((fiber (productSlice S z.1) z.2.2).card:ℝ))
    (HXY : ∀height : ℤ,ADBounds
      (realizedSlice ((S.image (window H R)).image (encode hd)) (mesh*(R:ℝ)) height)
      (mesh*(R:ℝ)) K t) :
    ∀height : ℤ,ADBounds
      (((productSlice (S.image (window H R)) height).image Prod.snd).image (center (mesh*(R:ℝ))))
      (mesh*(R:ℝ)) (quotientConstant k l lambda K t) (t-k) := by
  have hscaled : (mesh*(R:ℝ))*(Ncoarse:ℝ)=1/2 := by
    rw [hN,Nat.cast_mul] at hscale
    nlinarith only [hscale]
  have hden := window_fiber_density S H R Nfine Ncoarse hR hN lambda HX
  intro height
  have hsup := window_support S H R Nfine Ncoarse hR hN hx hy height
  exact (quotient_AD_of_encoded_AD hd (S.image (window H R)) height Ncoarse hNc
    (by positivity) hlambda hK hscaled hkt ht hsup.1 hsup.2 (hden height) (HXY height)).2

end NativeWindowQuotientTransport
