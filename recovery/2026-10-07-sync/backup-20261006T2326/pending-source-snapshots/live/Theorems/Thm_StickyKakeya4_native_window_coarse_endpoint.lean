import Theorems.Thm_StickyKakeya4_native_window_real_interpolation
import Theorems.Thm_StickyKakeya4_native_coarse_height_endpoint
import Theorems.Thm_StickyKakeya4_native_grid_center_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeWindowCoarseEndpoint
open Classical Finset NativeWindowXYLabels NativeWindowNesting
open NativeWindowRealInterpolation NativeCoarseHeightEndpoint
open FiniteVoronoiRealADCoarsening

/-- The actual global endpoint count is weakened algebraically to the
normalization required by grid recoding. No unit-ball support is assumed. -/
lemma global_card_from_half_width {X : Type*} (P : Finset X) (N : ℕ) {mu K s : ℝ}
    (hmu : 0 < mu) (hK : 0 ≤ K) (hs : 0 ≤ s) (hscale : mu*(N:ℝ)=1/2)
    (H : (P.card:ℝ) ≤ K*(N:ℝ)^s) : (P.card:ℝ) ≤ K*mu^(-s) := by
  have hN : (N:ℝ)=1/(2*mu) := by
    apply (eq_div_iff (by positivity : 2*mu ≠ 0)).mpr
    nlinarith only [hscale]
  rw [hN] at H
  exact NativeFiniteSliceUnionAD.global_bound_of_half_mesh P hmu hK hs H

/-- Beyond the coarsest prepared window, the proved source-height bound
makes temporal membership identical. Spatial labels still undergo their
literal integer coarsening. -/
theorem large_coarsen_eq {k l : ℕ} (S : Finset (XY k l))
    (R D : ℕ) (hR : 0 < R) (hD : 0 < D)
    (hheight : ∀w∈S, |w.1| ≤ 4*(R:ℤ)) (z : XY k l) (hz : z∈S) :
    (atPoint S R z).image (gridDiv D) = atPoint S (R*D) z := by
  apply Finset.Subset.antisymm (coarsen_subset S R D z)
  intro y hy
  rw [atPoint_eq_image] at hy
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hy
  obtain ⟨hwS,hwindow⟩ := mem_filter.mp hw
  have hRD : R ≤ R*D := by simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_left R hD
  have hw := height_label_stable R (R*D) hR hRD w.1 (hheight w hwS)
  have hz' := height_label_stable R (R*D) hR hRD z.1 (hheight z hz)
  rw [hw,hz'] at hwindow
  apply mem_image.mpr
  refine ⟨gridDiv R w.2.2,?_,gridDiv_comp R D w.2.2⟩
  rw [atPoint_eq_image]
  exact mem_image.mpr ⟨w,mem_filter.mpr ⟨hwS,hwindow⟩,rfl⟩

/-- Full-radius AD at an arbitrarily coarser actual dyadic height window.
The original coarsest profile and original global count are the inputs;
the target AD bound is derived through the exact original-point image. -/
theorem AD_from_coarsest_profile {k l : ℕ} (S : Finset (XY k l))
    (R D : ℕ) (hR : 0 < R) (hD : 0 < D)
    (hheight : ∀w∈S, |w.1| ≤ 4*(R:ℤ)) (z : XY k l) (hz : z∈S)
    {mu K s : ℝ} (hmu : 0 < mu) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (H : ADBounds (points S R mu z) mu K s)
    (Hglobal : ((atPoint S R z).card:ℝ) ≤ K*mu^(-s)) :
    ADBounds (points S (R*D) (mu*(D:ℝ)) z) (mu*(D:ℝ))
      ((((9:ℕ)^l:ℕ):ℝ)*K^2*(12:ℝ)^s) s := by
  have hh := NativeGridCenterCoarsening.coarsened_ADBounds (atPoint S R z) D hD hmu hK hs H Hglobal
  have he := large_coarsen_eq S R D hR hD hheight z hz
  change ADBounds (((atPoint S R z).image (gridDiv D)).image
    (NativeQuotientGridCenters.center (mu*(D:ℝ)))) (mu*(D:ℝ))
      ((((9:ℕ)^l:ℕ):ℝ)*K^2*(12:ℝ)^s) s at hh
  rw [he] at hh
  exact hh

end NativeWindowCoarseEndpoint
