/- RECONSTRUCTED 2026-10-06. UNVERIFIED.
This includes the post-terminal deprecation repair, which was not rechecked. -/
import Theorems.Thm_StickyKakeya4_native_fixed_offset_coherence
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
noncomputable section
namespace NativeAffineQuotientReadback
open StickyKakeya4 NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates NativeHeightSlopeCoordinates
open NativeGrainQuotientInjection
open scoped Matrix.Norms.Elementwise

lemma quotient_apply (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (x : E4) :
    NativeReferenceXYGridLinear.quotientMap P hP ell hell hell4 hd M x=
      NativeIncidentAffineAnchorGeometry.normalCoordinates P hP ell hell hell4 hd x-
        matrixVector M (tangentCoordinates P ell hd x) := by
  simp only [NativeReferenceXYGridLinear.quotientMap,LinearMap.sub_apply,LinearMap.comp_apply,
    Matrix.toEuclideanLin,Matrix.toLpLin_apply]
  rfl

lemma residual (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (x : E4)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (error : ℝ)
    (H : ‖NativeIncidentAffineAnchorGeometry.normalCoordinates P hP ell hell hell4 hd x-xi-
      matrixVector M (tangentCoordinates P ell hd x)‖ ≤ error) :
    ‖NativeReferenceXYGridLinear.quotientMap P hP ell hell hell4 hd M x-xi‖ ≤ error := by
  rw [quotient_apply]
  have heq (u v w : EuclideanSpace ℝ (Fin (4-ell))) : u-v-w=u-w-v := by abel
  rw [heq]
  exact H

end NativeAffineQuotientReadback
