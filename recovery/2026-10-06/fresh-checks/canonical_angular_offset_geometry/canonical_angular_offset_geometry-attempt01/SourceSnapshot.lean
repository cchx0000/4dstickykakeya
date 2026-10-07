import Theorems.Thm_StickyKakeya4_canonical_configured_E4_bridge
import Theorems.Thm_StickyKakeya4_native_local_offset_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace CanonicalAngularOffsetGeometry
open Classical Finset StickyKakeya4 CanonicalConfiguredE4Bridge
open scoped BigOperators

/-- The actual coordinate grid of the displayed E4 direction. -/
def angularKey (M : ℝ) (theta : E4) : Fin 4 → ℤ := fun j => ⌊M*theta j⌋

theorem angularKey_eq_grid (M : ℝ) (theta : E4) :
    angularKey M theta=wzDyadicCellIndex (1/M) theta := by
  funext j
  simp only [angularKey,wzDyadicCellIndex,div_div,div_one,mul_comm]

/-- A four-coordinate grid cell has Euclidean diameter at most2/M. -/
theorem angularKey_distance (M : ℝ) (hM : 0 < M) (theta theta' : E4)
    (H : angularKey M theta=angularKey M theta') :
    dist theta theta'≤2/M := by
  rw [angularKey_eq_grid,angularKey_eq_grid] at H
  have hh := NativeRotatedCellSelection.same_grid_dist_le (one_div_pos.mpr hM) H
  simpa only [mul_one_div] using hh

def tangentIndex : (s : Split) → Fin (tangentDim s) → Fin 4
  | .oneTwo,j => ⟨j.val,by have h : j.val<1 := j.isLt; omega⟩
  | .twoOne,j => ⟨j.val,by have h : j.val<2 := j.isLt; omega⟩

def normalIndex : (s : Split) → Fin (normalDim s) → Fin 4
  | .oneTwo,j => ⟨j.val+1,by have h : j.val<2 := j.isLt; omega⟩
  | .twoOne,j => ⟨j.val+2,by have h : j.val<1 := j.isLt; omega⟩

theorem tangent_readback (s : Split) (z : E4) (j : Fin (tangentDim s)) :
    tangent s z j=z (tangentIndex s j) := by
  cases s <;> fin_cases j <;> rfl

theorem normal_readback (s : Split) (z : E4) (i : Fin (normalDim s)) :
    normal s z i=z (normalIndex s i) := by
  cases s <;> fin_cases i <;> rfl

lemma rotated_coordinate_distance (O : E4 ≃ₗᵢ[ℝ] E4) (theta theta' : E4) (j : Fin 4) :
    |O theta j-O theta' j|≤dist theta theta' := by
  have hh := PiLp.dist_apply_le (O theta) (O theta') j
  simpa only [Real.dist_eq,LinearIsometryEquiv.dist_map] using hh

/-- Same literal angle key implies the required tangent AND normal
coordinate differences in the unchanged fixed orthonormal chart. -/
theorem chart_coordinates_close (s : Split) (O : E4 ≃ₗᵢ[ℝ] E4)
    (M : ℝ) (hM : 0 < M) (theta theta' : E4)
    (H : angularKey M theta=angularKey M theta') :
    (∀j,|tangent s (O theta) j-tangent s (O theta') j|≤2/M) ∧
    (∀i,|normal s (O theta) i-normal s (O theta') i|≤2/M) := by
  have hd := angularKey_distance M hM theta theta' H
  constructor
  · intro j
    rw [tangent_readback,tangent_readback]
    exact (rotated_coordinate_distance O theta theta' (tangentIndex s j)).trans hd
  · intro i
    rw [normal_readback,normal_readback]
    exact (rotated_coordinate_distance O theta theta' (normalIndex s i)).trans hd

lemma rotated_coordinate_bound (O : E4 ≃ₗᵢ[ℝ] E4) (theta : E4)
    (H : ‖theta‖≤4) (j : Fin 4) : |O theta j|≤4 := by
  have hh := PiLp.norm_apply_le (O theta) j
  have hh' : |O theta j|≤‖theta‖ := by
    simpa only [Real.norm_eq_abs,LinearIsometryEquiv.norm_map] using hh
  exact hh'.trans H

theorem chart_coordinates_bound (s : Split) (O : E4 ≃ₗᵢ[ℝ] E4)
    (theta : E4) (H : ‖theta‖≤4) :
    (∀j,|tangent s (O theta) j|≤4) ∧ (∀i,|normal s (O theta) i|≤4) := by
  constructor
  · intro j
    rw [tangent_readback]
    exact rotated_coordinate_bound O theta H (tangentIndex s j)
  · intro i
    rw [normal_readback]
    exact rotated_coordinate_bound O theta H (normalIndex s i)

/-- Literal Euclidean residual in the normal coordinates of the fixed
chart. It can be read directly from an actual affine incidence estimate. -/
def affineResidual (s : Split) (O : E4 ≃ₗᵢ[ℝ] E4) (theta : E4)
    (F : Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (xi : Fin (normalDim s) → ℝ) : EuclideanSpace ℝ (Fin (normalDim s)) :=
  WithLp.toLp 2 (fun i => normal s (O theta) i-
    (∑j,F i j*tangent s (O theta) j)-xi i)

/-- Coordinate differences A=2 and tangent bound B=4 are derived from the
actual angular grid and direction norm. Only the displayed local matrix
oscillation and the genuine affine residual remain geometric inputs. -/
theorem shared_actual_angle_offsets {P T : Type*}
    (s : Split) (S : Finset (P × T)) (theta : T → E4) (O : E4 ≃ₗᵢ[ℝ] E4)
    (field : P → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (xi : P → Fin (normalDim s) → ℝ) (E M v : ℝ) (hM : 0 < M) (hv : 0≤v)
    (hTheta : ∀z∈S,‖theta z.2‖≤4)
    (hField : ∀p∈S.image Prod.fst,∀i j,|field p i j|≤1/4)
    (hVar : ∀p∈S.image Prod.fst,∀q∈S.image Prod.fst,∀i j,|field p i j-field q i j|≤v)
    (hRes : ∀z∈S,‖affineResidual s O (theta z.2) (field z.1) (xi z.1)‖≤E)
    {z w : P × T} (hz : z∈S) (hw : w∈S)
    (ha : angularKey M (theta z.2)=angularKey M (theta w.2)) :
    ∀i,|xi z.1 i-xi w.1 i|≤2*E+4/M+8*v := by
  have hTang : ∀a∈S,∀j,|tangent s (O (theta a.2)) j|≤4 := by
    intro a ha j
    exact (chart_coordinates_bound s O (theta a.2) (hTheta a ha)).1 j
  have hAngle : ∀a∈S,∀b∈S,angularKey M (theta a.2)=angularKey M (theta b.2) →
      (∀j,|tangent s (O (theta a.2)) j-tangent s (O (theta b.2)) j|≤2/M) ∧
      (∀i,|normal s (O (theta a.2)) i-normal s (O (theta b.2)) i|≤2/M) := by
    intro a _ha b _hb hab
    exact chart_coordinates_close s O M hM (theta a.2) (theta b.2) hab
  have hResCoord : ∀a∈S,∀i,|normal s (O (theta a.2)) i-
      (∑j,field a.1 i j*tangent s (O (theta a.2)) j)-xi a.1 i|≤E := by
    intro a ha i
    have hh := (PiLp.norm_apply_le (affineResidual s O (theta a.2) (field a.1) (xi a.1)) i).trans
      (hRes a ha)
    change |(affineResidual s O (theta a.2) (field a.1) (xi a.1)) i|≤E
    simpa only [Real.norm_eq_abs] using hh
  have hk : tangentDim s≤2 := by cases s <;> decide
  have hh := NativeLocalOffsetGeometry.shared_angle_offsets S (fun t => angularKey M (theta t))
    (fun t => tangent s (O (theta t))) (fun t => normal s (O (theta t))) field xi
    E M v 2 4 hk hM hv (by norm_num) (by norm_num) hTang hField hVar hAngle hResCoord hz hw ha
  simpa only [show (2:ℝ)*2=4 by norm_num,show (2:ℝ)*4=8 by norm_num] using hh

end CanonicalAngularOffsetGeometry
