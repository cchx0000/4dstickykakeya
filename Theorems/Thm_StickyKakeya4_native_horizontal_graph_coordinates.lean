import Theorems.Thm_StickyKakeya4_native_selected_horizontal_graph_chart
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeHorizontalGraphCoordinates
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice NativeProjectorCellChart
open NativeProjectorGraphMap NativeSelectedHorizontalGraphChart
open scoped BigOperators Matrix.Norms.Elementwise

/-- The true horizontal normal space; the vertical coordinate is removed. -/
def normalSpace (P : Submodule ℝ E4) : Submodule ℝ E4 := Pᗮ⊓heightKernel

lemma horizontal_finrank : Module.finrank ℝ heightKernel=3 := by
  apply heightKernel_finrank (v:=EuclideanSpace.single (3:Fin 4) (1:ℝ))
  simp

lemma normalSpace_finrank (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) : Module.finrank ℝ (normalSpace P)=4-ell := by
  have hh := Submodule.finrank_add_inf_finrank_orthogonal hP
  rw [hd,horizontal_finrank] at hh
  change (ell-1)+Module.finrank ℝ (normalSpace P)=3 at hh
  omega

/-- Fixed orthonormal coordinates chosen once from the actual reference plane. -/
def domainBasis (P : Submodule ℝ E4) (ell : ℕ) (hd : Module.finrank ℝ P=ell-1) :
    OrthonormalBasis (Fin (ell-1)) ℝ P :=
  (stdOrthonormalBasis ℝ P).reindex (finCongr hd)

def normalBasis (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) :
    OrthonormalBasis (Fin (4-ell)) ℝ (normalSpace P) :=
  (stdOrthonormalBasis ℝ (normalSpace P)).reindex (finCongr (normalSpace_finrank P hP ell hell hell4 hd))

/-- Restriction uses proved horizontal membership of the actual graph outputs. -/
def horizontalGraph (P : Submodule ℝ E4) (G : P →ₗ[ℝ] Pᗮ)
    (hG : ∀p,(G p:E4)∈heightKernel) : P →ₗ[ℝ] normalSpace P :=
  (Pᗮ.subtype.comp G).codRestrict (normalSpace P) (fun p => ⟨(G p).property,hG p⟩)

lemma horizontalGraph_val (P : Submodule ℝ E4) (G : P →ₗ[ℝ] Pᗮ)
    (hG : ∀p,(G p:E4)∈heightKernel) (p : P) :
    (horizontalGraph P G hG p:E4)=(G p:E4) := rfl

/-- The two isometries preserve all graph norms and all variation constants. -/
def slopeMap (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel) :
    EuclideanSpace ℝ (Fin (ell-1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (4-ell)) :=
  ((normalBasis P hP ell hell hell4 hd).repr.toLinearMap.comp (horizontalGraph P G hG)).comp
    (domainBasis P ell hd).repr.symm.toLinearMap

lemma slopeMap_norm (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel)
    (B : ℝ) (hbound : ∀p,‖G p‖ ≤ B*‖p‖) (x : EuclideanSpace ℝ (Fin (ell-1))) :
    ‖slopeMap P hP ell hell hell4 hd G hG x‖ ≤ B*‖x‖ := by
  change ‖(normalBasis P hP ell hell hell4 hd).repr
    (horizontalGraph P G hG ((domainBasis P ell hd).repr.symm x))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  change ‖G ((domainBasis P ell hd).repr.symm x)‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using hbound ((domainBasis P ell hd).repr.symm x)

lemma slopeMap_variation (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G F : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel) (hF : ∀p,(F p:E4)∈heightKernel)
    (B : ℝ) (hbound : ∀p,‖G p-F p‖ ≤ B*‖p‖) (x : EuclideanSpace ℝ (Fin (ell-1))) :
    ‖slopeMap P hP ell hell hell4 hd G hG x-slopeMap P hP ell hell hell4 hd F hF x‖ ≤ B*‖x‖ := by
  change ‖(normalBasis P hP ell hell hell4 hd).repr (horizontalGraph P G hG ((domainBasis P ell hd).repr.symm x))-
    (normalBasis P hP ell hell hell4 hd).repr (horizontalGraph P F hF ((domainBasis P ell hd).repr.symm x))‖ ≤ _
  rw [←map_sub,LinearIsometryEquiv.norm_map]
  change ‖G ((domainBasis P ell hd).repr.symm x)-F ((domainBasis P ell hd).repr.symm x)‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using hbound ((domainBasis P ell hd).repr.symm x)

/-- The actual coordinate matrix; rows have dimension4-ell and columnsell-1. -/
def slopeMatrix (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel) : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (ell-1)) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin (4-ell)) ℝ).toBasis (slopeMap P hP ell hell hell4 hd G hG)

lemma slopeMatrix_entry (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel) (i : Fin (4-ell)) (j : Fin (ell-1)) :
    slopeMatrix P hP ell hell hell4 hd G hG i j=
      slopeMap P hP ell hell hell4 hd G hG (EuclideanSpace.basisFun (Fin (ell-1)) ℝ j) i := by
  simp only [slopeMatrix,LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr,OrthonormalBasis.coe_toBasis]

lemma slopeMatrix_action (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel) (x : EuclideanSpace ℝ (Fin (ell-1))) :
    (slopeMatrix P hP ell hell hell4 hd G hG).mulVec (fun j => x j)=
      (fun i => slopeMap P hP ell hell hell4 hd G hG x i) := by
  have hh := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin (ell-1)) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin (4-ell)) ℝ).toBasis (slopeMap P hP ell hell hell4 hd G hG) x
  have hsrc : ((EuclideanSpace.basisFun (Fin (ell-1)) ℝ).toBasis.repr x : Fin (ell-1) → ℝ)=fun j => x j := by
    funext j
    simp only [OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr]
  have htgt : ((EuclideanSpace.basisFun (Fin (4-ell)) ℝ).toBasis.repr
      (slopeMap P hP ell hell hell4 hd G hG x) : Fin (4-ell) → ℝ)=fun i => slopeMap P hP ell hell hell4 hd G hG x i := by
    funext i
    simp only [OrthonormalBasis.coe_toBasis_repr_apply,EuclideanSpace.basisFun_repr]
  rw [hsrc,htgt] at hh
  exact hh

lemma slopeMatrix_norm (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀p,‖G p‖ ≤ B*‖p‖) :
    ‖slopeMatrix P hP ell hell hell4 hd G hG‖ ≤ B := by
  apply (Matrix.norm_le_iff hB).mpr
  intro i j
  rw [slopeMatrix_entry]
  have hh := slopeMap_norm P hP ell hell hell4 hd G hG B hbound
    (EuclideanSpace.basisFun (Fin (ell-1)) ℝ j)
  have hnorm := (EuclideanSpace.basisFun (Fin (ell-1)) ℝ).orthonormal.norm_eq_one j
  exact (PiLp.norm_apply_le _ i).trans (by simpa only [hnorm,mul_one] using hh)

lemma slopeMatrix_variation (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G F : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel) (hF : ∀p,(F p:E4)∈heightKernel)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀p,‖G p-F p‖ ≤ B*‖p‖) :
    ‖slopeMatrix P hP ell hell hell4 hd G hG-slopeMatrix P hP ell hell hell4 hd F hF‖ ≤ B := by
  apply (Matrix.norm_le_iff hB).mpr
  intro i j
  change ‖slopeMatrix P hP ell hell hell4 hd G hG i j-slopeMatrix P hP ell hell hell4 hd F hF i j‖ ≤ B
  rw [slopeMatrix_entry,slopeMatrix_entry]
  have hh := slopeMap_variation P hP ell hell hell4 hd G F hG hF B hbound
    (EuclideanSpace.basisFun (Fin (ell-1)) ℝ j)
  have hnorm := (EuclideanSpace.basisFun (Fin (ell-1)) ℝ).orthonormal.norm_eq_one j
  have hc := PiLp.norm_apply_le
    (slopeMap P hP ell hell hell4 hd G hG (EuclideanSpace.basisFun (Fin (ell-1)) ℝ j)-
      slopeMap P hP ell hell hell4 hd F hF (EuclideanSpace.basisFun (Fin (ell-1)) ℝ j)) i
  exact hc.trans (by simpa only [hnorm,mul_one] using hh)

/-- Exact linear-plane graph readback in fixed orthonormal coordinates.
This says nothing about replacing thick raw grain points by exact graph points. -/
lemma coordinate_graph_readback (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (G : P →ₗ[ℝ] Pᗮ) (hG : ∀p,(G p:E4)∈heightKernel)
    (x : EuclideanSpace ℝ (Fin (ell-1))) :
    (((normalBasis P hP ell hell hell4 hd).repr.symm (slopeMap P hP ell hell hell4 hd G hG x):normalSpace P):E4)=
      (G ((domainBasis P ell hd).repr.symm x):E4) := by
  change (((normalBasis P hP ell hell hell4 hd).repr.symm
    ((normalBasis P hP ell hell hell4 hd).repr (horizontalGraph P G hG ((domainBasis P ell hd).repr.symm x))):normalSpace P):E4)=_
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

end NativeHorizontalGraphCoordinates
