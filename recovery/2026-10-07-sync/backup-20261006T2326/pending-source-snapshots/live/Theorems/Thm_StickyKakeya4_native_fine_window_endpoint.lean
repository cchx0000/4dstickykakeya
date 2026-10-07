import Theorems.Thm_StickyKakeya4_native_finite_slice_union_ad
import Theorems.Thm_StickyKakeya4_native_ad_fixed_mesh_refinement

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeFineWindowEndpoint
open NativeFiniteSliceUnionAD NativeADFixedMeshRefinement FiniteVoronoiRealADCoarsening

/-- The genuine translated-height mesh is mu/8. A positive window H<=8
is a union of at most eight fine Y slices, at its actual physical scale
rho=mu*H/8. No density retention inside that short window is assumed. -/
theorem short_window_ADBounds {Ω X : Type*} [PseudoMetricSpace X]
    (A : Finset Ω) (height : Ω → ℤ) (value : Ω → X)
    (H : ℕ) (hH : 0 < H) (hH8 : H ≤ 8) (q : ℤ)
    {mu K s : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (Hfine : ∀z∈OriginalHeightRescaling.timeFiber H q, ADBounds (heightSlice A height value z) mu K s)
    (Hglobal : ∀z∈OriginalHeightRescaling.timeFiber H q,
      ((heightSlice A height value z).card:ℝ) ≤ K*mu^(-s)) :
    ADBounds (heightWindow A height value H q) (mu*(H:ℝ)/8) (8*(16:ℝ)^s*K) s := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hh := heightWindow_eight_ADBounds A height value H hH hH8 q hmu hK0 hs Hfine Hglobal
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hH1 : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hH8r : (H:ℝ) ≤ 8 := by exact_mod_cast hH8
  have hrho : 0 < mu*(H:ℝ)/8 := by positivity
  have hrhomu : mu*(H:ℝ)/8 ≤ mu := by nlinarith only [mul_le_mul_of_nonneg_left hH8r hmu.le]
  have hscale : mu ≤ 8*(mu*(H:ℝ)/8) := by
    have hp := mul_le_mul_of_nonneg_left hH1 hmu.le
    nlinarith only [hp]
  have htwo : (1:ℝ) ≤ (2:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have hcoef : (1:ℝ) ≤ 8*(2:ℝ)^s*K := by
    have hh' := one_le_mul_of_one_le_of_one_le htwo hK
    nlinarith only [hh']
  have Href := refine_mesh (heightWindow A height value H q) hrho hrhomu hmu1 hscale
    (by norm_num : (1:ℝ) ≤ 8) hcoef hs hh
  have heq : (8:ℝ)^s*(8*(2:ℝ)^s*K)=8*(16:ℝ)^s*K := by
    rw [show (16:ℝ)=8*2 by norm_num,Real.mul_rpow (by norm_num) (by norm_num)]
    ring
  simpa only [heq] using Href

end NativeFineWindowEndpoint
