import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_menus
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeReferenceXYGridAngularCap
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridMaps NativeReferenceXYGridMenus
open NativeGrainQuotientInjection NativeGrainQuotientBins NativeHorizontalGrainSlice NativeOriginalParentSelection
open NativeLocalParentGeometry NativeOriginalCellChartGeometry NativeSpatialAngularGeometry
open NativeIncidentAffineAnchorGeometry (localHorizontalSlope localHorizontalSlope_norm localHorizontalSlope_mem_heightKernel)
open scoped BigOperators Matrix.Norms.Elementwise

/-- The actual STANDARD three-coordinate angular grid, not a tangent projection. -/
def angle (r : ℝ) (v : E4) : Fin 3 → ℤ := fun j => ⌊v j.castSucc/r⌋

lemma angle_mem_box {r : ℝ} (hr : 0 < r) (v w : E4) (hdist : ‖v-w‖ ≤ 8*r) :
    angle r v∈vectorBox (angle r w) 8 := by
  apply Fintype.mem_piFinset.mpr
  intro j
  apply floor_neighbor hr 8
  have hh : |v j.castSucc-w j.castSucc| ≤ ‖v-w‖ := by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (v-w) j.castSucc
  exact hh.trans hdist

/-- A tangent grid fiber has bounded FULL angular diameter because the
actual affine quotient residual is small. No tangent injectivity is assumed. -/
lemma same_tangent_bin_diameter (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) {r : ℝ} (hr : 0 < r) (v w : E4)
    (hv : v∈heightKernel) (hw : w∈heightKernel)
    (hvr : ‖quotientMap P hP ell hell hell4 hd M v-xi‖ ≤ r)
    (hwr : ‖quotientMap P hP ell hell hell4 hd M w-xi‖ ≤ r)
    (he : label r (tangentCoordinates P ell hd v)=label r (tangentCoordinates P ell hd w)) :
    ‖v-w‖ ≤ 8*r := by
  have ht := same_label_norm_bound hr (tangentCoordinates P ell hd v) (tangentCoordinates P ell hd w) he
  rw [←map_sub] at ht
  have hq : ‖quotientMap P hP ell hell hell4 hd M (v-w)‖ ≤ 2*r := by
    rw [map_sub]
    have hh := norm_sub_le_norm_sub_add_norm_sub
      (quotientMap P hP ell hell hell4 hd M v) xi (quotientMap P hP ell hell hell4 hd M w)
    rw [norm_sub_rev xi] at hh
    linarith
  have hi := horizontal_inverse P hP ell hell hell4 hd M hM (heightKernel.sub_mem hv hw)
  have hdim : ((ell-1:ℕ):ℝ) ≤ 3 := by exact_mod_cast (show ell-1 ≤ 3 by omega)
  have hmul := mul_le_mul_of_nonneg_right hdim hr.le
  linarith

/-- The actual standard angular grid is covered by the tangent-grid fibers.
Every fiber meets≤17^3 standard angular cells; the final50^3 constant leaves
room for other fixed coordinate conventions without hiding any r factor. -/
theorem affine_angle_cap {A : Type*} (S : Finset A) (w : A → E4)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) {r : ℝ} (hr : 0 < r)
    (hhorizontal : ∀i∈S,w i∈heightKernel) (hnorm : ∀i∈S,‖w i‖ ≤ 2)
    (hresidual : ∀i∈S,‖quotientMap P hP ell hell hell4 hd M (w i)-xi‖ ≤ r) :
    ((S.image (fun i => angle r (w i))).card:ℝ) ≤ (50:ℝ)^3*(4/r+2)^(ell-1) := by
  let f := fun i => label r (tangentCoordinates P ell hd (w i))
  have hfiber : ∀b∈S.image f,(((S.filter (fun i => f i=b)).image (fun i => angle r (w i))).card:ℝ) ≤ (17:ℝ)^3 := by
    intro b hb
    obtain ⟨j,hj,hjb⟩ := mem_image.mp hb
    have hsub : (S.filter (fun i => f i=b)).image (fun i => angle r (w i))⊆vectorBox (angle r (w j)) 8 := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      obtain ⟨hi,hib⟩ := mem_filter.mp hi
      exact angle_mem_box hr (w i) (w j)
        (same_tangent_bin_diameter P hP ell hell hell4 hd M hM xi hr (w i) (w j)
          (hhorizontal i hi) (hhorizontal j hj) (hresidual i hi) (hresidual j hj) (hib.trans hjb.symm))
    have hc := card_le_card hsub
    rw [vectorBox_card] at hc
    exact_mod_cast hc
  have hcover := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images S
    (fun i => angle r (w i)) f ((17:ℝ)^3) hfiber
  have ht : ((S.image f).card:ℝ) ≤ (4/r+2)^(ell-1) := by
    have hh := occupied_card S (fun i => tangentCoordinates P ell hd (w i)) hr (by norm_num : (0:ℝ) ≤ 2)
      (0:EuclideanSpace ℝ (Fin (ell-1))) (fun i hi => by
        rw [sub_zero]
        exact (tangent_norm_le P ell hd (w i)).trans (hnorm i hi))
    simpa only [show (2:ℝ)*2=4 by norm_num] using hh
  calc
    _ ≤ (17:ℝ)^3*((S.image f).card:ℝ) := hcover
    _ ≤ (50:ℝ)^3*((S.image f).card:ℝ) := mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)

/-- Literal standard angular cells of the actual parent-normalized original slopes. -/
def localAngle {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent) (r : ℝ) (i : Fin n) : Fin 3 → ℤ :=
  angle r (localHorizontalSlope D N p i)

/-- Source-specific angle cap, with actual parent membership supplying the
norm bound. The fixed affine residual is the one provided by source anchors. -/
theorem source_local_angle_cap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (S : Finset (Fin n)) (hparent : ∀i∈S,parentLabel D a N i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) {r : ℝ} (hr : 0 < r)
    (hresidual : ∀i∈S,‖quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D N p i)-xi‖ ≤ r) :
    ((S.image (localAngle D N p r)).card:ℝ) ≤ (50:ℝ)^3*(4/r+2)^(ell-1) :=
  affine_angle_cap S (localHorizontalSlope D N p) P hP ell hell hell4 hd M hM xi hr
    (fun i _ => localHorizontalSlope_mem_heightKernel D N p i)
    (fun i hi => localHorizontalSlope_norm D a N p i (hparent i hi)) hresidual

/-- At reciprocal integer resolution this is exactly the original angular
label translated by the fixed parent label, not a projected angle alphabet. -/
lemma localAngle_inverse {n : ℕ} (D : FiniteScaleSource n) (N R : ℕ) (p : Parent) (i : Fin n) :
    localAngle D N p (1/(R:ℝ)) i=(fun j => angularLabel D (N*R) i j-(R:ℤ)*p.1 j) := by
  ext j
  simp only [localAngle,angle,localHorizontalSlope,ActualSlopeSource.heightPoint_castSucc,localSlope,div_eq_mul_inv,one_mul,inv_inv]
  rw [mul_comm,NativeUnitParentDyadic.floor_sub_integer_mul]
  congr 1
  change ⌊(R:ℝ)*((N:ℝ)*slope (D.line i) j)⌋=⌊((N*R:ℕ):ℝ)*slope (D.line i) j⌋
  congr 1
  push_cast
  ring

lemma localAngle_image_card {n : ℕ} (D : FiniteScaleSource n) (N R : ℕ) (p : Parent) (S : Finset (Fin n)) :
    (S.image (localAngle D N p (1/(R:ℝ)))).card=(S.image (angularLabel D (N*R))).card := by
  have he : S.image (localAngle D N p (1/(R:ℝ)))=
      (S.image (angularLabel D (N*R))).image (fun v j => v j-(R:ℤ)*p.1 j) := by
    rw [image_image]
    exact image_congr (fun i _ => localAngle_inverse D N R p i)
  rw [he]
  apply card_image_of_injective
  intro u v huv
  ext j
  have hh := congrFun huv j
  dsimp only at hh
  omega

/-- Exact ORIGINAL angular-label count on one retained parent. This is the
native grid needed by the source angular lower bounds. -/
theorem original_angular_cap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N R : ℕ) (hR : 0 < R) (p : Parent)
    (S : Finset (Fin n)) (hparent : ∀i∈S,parentLabel D a N i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell)))
    (hresidual : ∀i∈S,‖quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D N p i)-xi‖ ≤ 1/(R:ℝ)) :
    ((S.image (angularLabel D (N*R))).card:ℝ) ≤ (50:ℝ)^3*(4*(R:ℝ)+2)^(ell-1) := by
  have hh := source_local_angle_cap D a N p S hparent P hP ell hell hell4 hd M hM xi
    (by positivity : (0:ℝ)<1/(R:ℝ)) hresidual
  rw [localAngle_image_card] at hh
  simpa only [div_eq_mul_inv,one_mul,inv_inv] using hh

end NativeReferenceXYGridAngularCap
