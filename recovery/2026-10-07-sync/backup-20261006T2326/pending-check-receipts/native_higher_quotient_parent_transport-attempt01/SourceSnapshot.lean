import Theorems.Thm_StickyKakeya4_native_local_parent_physical_map

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeHigherQuotientParentTransport
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentPhysicalMap NativeContractedUnitParent

/-- The actual time origin used by physicalMap, before its factor512. -/
def timeOrigin {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) : ℝ := (shift D a:ℝ)*mesh D

def horizontalScale (N : ℕ) : ℝ := (N:ℝ)/512

lemma horizontalScale_nonneg (N : ℕ) : 0≤horizontalScale N := by
  unfold horizontalScale
  positivity

lemma horizontalScale_pos {N : ℕ} (hN : 0<N) : 0<horizontalScale N := by
  unfold horizontalScale
  positivity

/-- Literal higher tangent coordinates in the fixed chart. -/
def higherX (x : E4) : Fin 2 → ℝ := fun j => x j.castSucc.castSucc

/-- Literal scalar quotient of the higher horizontal two-plane. -/
def higherY (C F : ℝ) (x : E4) : ℝ := x 2-C*x 0-F*x 1

def tangentShift (p : Parent) (s z : ℝ) : Fin 2 → ℝ :=
  fun j => ((p.1 j.castSucc:ℝ)*(z-s)+4*(p.2 j.castSucc:ℝ))/512

def quotientShift (p : Parent) (s z C F : ℝ) : ℝ :=
  ((C*(p.1 0:ℝ)+F*(p.1 1:ℝ)-(p.1 2:ℝ))*(z-s)+
    4*(C*(p.2 0:ℝ)+F*(p.2 1:ℝ)-(p.2 2:ℝ)))/512

/-- Exact raw physical time. The factor128 in the separate oldTime chart
does not occur in this identity. -/
theorem physical_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (x : E4) :
    NativeLocalParentPhysicalMap.physicalMap D a N p x 3=(x 3-timeOrigin D a)/512 := by
  simp only [NativeLocalParentPhysicalMap.physicalMap,baseMap,contractPoint,
    PiLp.smul_apply,smul_eq_mul,show (3:Fin 4)=Fin.last 3 from rfl,
    ActualSlopeSource.heightPoint_last,timeOrigin]
  ring

theorem physical_coordinate {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (x : E4) (j : Fin 3) :
    NativeLocalParentPhysicalMap.physicalMap D a N p x j.castSucc=
      ((N:ℝ)*x j.castSucc-(p.1 j:ℝ)*(x 3-timeOrigin D a)-4*(p.2 j:ℝ))/512 := by
  simp only [NativeLocalParentPhysicalMap.physicalMap,baseMap,contractPoint,
    PiLp.smul_apply,smul_eq_mul,ActualSlopeSource.heightPoint_castSucc,timeOrigin]
  ring

theorem old_height_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (x : E4) :
    timeOrigin D a+512*(NativeLocalParentPhysicalMap.physicalMap D a N p x 3)=x 3 := by
  rw [physical_height]
  ring

/-- A field is pulled back by the literal inverse physical time map. -/
def carriedField (s : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (s+512*t)

theorem carriedField_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (f : ℝ → ℝ) (x : E4) :
    carriedField (timeOrigin D a) f (NativeLocalParentPhysicalMap.physicalMap D a N p x 3)=f (x 3) := by
  simp only [carriedField,old_height_readback]

/-- The same actual tube-parent map acts affinely on higher X. -/
theorem higherX_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (x : E4) :
    higherX (NativeLocalParentPhysicalMap.physicalMap D a N p x)=
      horizontalScale N • higherX x-tangentShift p (timeOrigin D a) (x 3) := by
  funext j
  simp only [higherX,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [physical_coordinate]
  dsimp only [horizontalScale,tangentShift]
  ring

/-- At the same original height the higher Y map is a genuine affine
similarity, with its actual parent translation fully displayed. -/
theorem higherY_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (C F : ℝ) (x : E4) :
    higherY C F (NativeLocalParentPhysicalMap.physicalMap D a N p x)=
      horizontalScale N*higherY C F x+quotientShift p (timeOrigin D a) (x 3) C F := by
  dsimp only [higherY]
  have h0 := physical_coordinate D a N p x (0:Fin 3)
  have h1 := physical_coordinate D a N p x (1:Fin 3)
  have h2 := physical_coordinate D a N p x (2:Fin 3)
  simp only [show (0:Fin 3).castSucc=(0:Fin 4) by decide] at h0
  simp only [show (1:Fin 3).castSucc=(1:Fin 4) by decide] at h1
  simp only [show (2:Fin 3).castSucc=(2:Fin 4) by decide] at h2
  rw [h0,h1,h2]
  dsimp only [horizontalScale,quotientShift]
  ring

theorem carried_quotient_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (C F : ℝ → ℝ) (x : E4) :
    higherY (carriedField (timeOrigin D a) C (NativeLocalParentPhysicalMap.physicalMap D a N p x 3))
      (carriedField (timeOrigin D a) F (NativeLocalParentPhysicalMap.physicalMap D a N p x 3))
      (NativeLocalParentPhysicalMap.physicalMap D a N p x)=
      horizontalScale N*higherY (C (x 3)) (F (x 3)) x+
        quotientShift p (timeOrigin D a) (x 3) (C (x 3)) (F (x 3)) := by
  rw [carriedField_readback,carriedField_readback]
  exact higherY_readback D a N p _ _ x

/-- This is the same point's actual higher graph representation after the
parent map. No higher-plane existence or density assertion is an input. -/
theorem graph_representation {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (C F y : ℝ) (x : E4) (h : x 2=y+C*x 0+F*x 1) :
    NativeLocalParentPhysicalMap.physicalMap D a N p x 2=
      (horizontalScale N*y+quotientShift p (timeOrigin D a) (x 3) C F)+
        C*NativeLocalParentPhysicalMap.physicalMap D a N p x 0+
        F*NativeLocalParentPhysicalMap.physicalMap D a N p x 1 := by
  have hh := higherY_readback D a N p C F x
  dsimp only [higherY] at hh
  rw [h] at hh
  linarith only [hh]

theorem higherX_difference_same_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (x y : E4) (hheight : x 3=y 3) :
    higherX (NativeLocalParentPhysicalMap.physicalMap D a N p x)-
      higherX (NativeLocalParentPhysicalMap.physicalMap D a N p y)=
        horizontalScale N • (higherX x-higherX y) := by
  rw [higherX_readback,higherX_readback,hheight]
  module

theorem higherX_distance_same_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (x y : E4) (hheight : x 3=y 3) :
    dist (higherX (NativeLocalParentPhysicalMap.physicalMap D a N p x))
      (higherX (NativeLocalParentPhysicalMap.physicalMap D a N p y))=
        horizontalScale N*dist (higherX x) (higherX y) := by
  rw [dist_eq_norm,higherX_difference_same_height D a N p x y hheight,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (horizontalScale_nonneg N),dist_eq_norm]

theorem higherY_difference_same_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (C F : ℝ) (x y : E4) (hheight : x 3=y 3) :
    higherY C F (NativeLocalParentPhysicalMap.physicalMap D a N p x)-
      higherY C F (NativeLocalParentPhysicalMap.physicalMap D a N p y)=
        horizontalScale N*(higherY C F x-higherY C F y) := by
  rw [higherY_readback,higherY_readback,hheight]
  ring

theorem higherY_distance_same_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (C F : ℝ) (x y : E4) (hheight : x 3=y 3) :
    dist (higherY C F (NativeLocalParentPhysicalMap.physicalMap D a N p x))
      (higherY C F (NativeLocalParentPhysicalMap.physicalMap D a N p y))=
        horizontalScale N*dist (higherY C F x) (higherY C F y) := by
  rw [Real.dist_eq,higherY_difference_same_height D a N p C F x y hheight,
    abs_mul,abs_of_nonneg (horizontalScale_nonneg N),Real.dist_eq]

/-- Exact finite image on the original labels, at one unchanged old height. -/
theorem higherY_image {A : Type*} {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (I : Finset A) (point : A → E4) (z C F : ℝ)
    (hheight : ∀i∈I,point i 3=z) :
    I.image (fun i => higherY C F (NativeLocalParentPhysicalMap.physicalMap D a N p (point i)))=
      (I.image (fun i => higherY C F (point i))).image
        (fun y => horizontalScale N*y+quotientShift p (timeOrigin D a) z C F) := by
  rw [image_image]
  apply image_congr
  intro i hi
  simpa only [Function.comp_apply,hheight i hi] using higherY_readback D a N p C F (point i)

theorem higherX_image {A : Type*} {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (I : Finset A) (point : A → E4) (z : ℝ)
    (hheight : ∀i∈I,point i 3=z) :
    I.image (fun i => higherX (NativeLocalParentPhysicalMap.physicalMap D a N p (point i)))=
      (I.image (fun i => higherX (point i))).image
        (fun x => horizontalScale N • x-tangentShift p (timeOrigin D a) z) := by
  rw [image_image]
  apply image_congr
  intro i hi
  simpa only [Function.comp_apply,hheight i hi] using higherX_readback D a N p (point i)

/-- The same-height higher-Y alphabet keeps its actual cardinality under
the nondegenerate parent map, even when original metadata repeats a point. -/
theorem higherY_image_card {A : Type*} {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (hN : 0<N) (p : Parent) (I : Finset A) (point : A → E4) (z C F : ℝ)
    (hheight : ∀i∈I,point i 3=z) :
    (I.image (fun i => higherY C F (NativeLocalParentPhysicalMap.physicalMap D a N p (point i)))).card=
      (I.image (fun i => higherY C F (point i))).card := by
  rw [higherY_image D a N p I point z C F hheight]
  apply card_image_of_injective
  intro u v huv
  exact (mul_left_cancel₀ (horizontalScale_pos hN).ne' (add_right_cancel huv))

/-- Apply this to the literal old higher-Y fiber to transport its selected
distinct X population exactly. It does not assert retention of that fiber. -/
theorem higherX_image_card {A : Type*} {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (hN : 0<N) (p : Parent) (I : Finset A) (point : A → E4) (z : ℝ)
    (hheight : ∀i∈I,point i 3=z) :
    (I.image (fun i => higherX (NativeLocalParentPhysicalMap.physicalMap D a N p (point i)))).card=
      (I.image (fun i => higherX (point i))).card := by
  rw [higherX_image D a N p I point z hheight]
  apply card_image_of_injective
  intro u v huv
  funext j
  have hj := congrFun huv j
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hj
  apply mul_left_cancel₀ (horizontalScale_pos hN).ne'
  linarith only [hj]

/-- Exact equality of the original index fibers before and after transport.
Both the original height and its own higher quotient witness are retained. -/
theorem higherY_fiber_indices {A : Type*} {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (hN : 0<N) (p : Parent) (I : Finset A) (point : A → E4) (z C F y : ℝ) :
    I.filter (fun i => point i 3=z ∧
      higherY C F (NativeLocalParentPhysicalMap.physicalMap D a N p (point i))=
        horizontalScale N*y+quotientShift p (timeOrigin D a) z C F)=
      I.filter (fun i => point i 3=z ∧ higherY C F (point i)=y) := by
  ext i
  simp only [mem_filter]
  constructor
  · rintro ⟨hi,hz,hy⟩
    rw [higherY_readback,hz] at hy
    exact ⟨hi,hz,mul_left_cancel₀ (horizontalScale_pos hN).ne' (add_right_cancel hy)⟩
  · rintro ⟨hi,hz,hy⟩
    refine ⟨hi,hz,?_⟩
    rw [higherY_readback,hz,hy]

/-- A later actual point motion contributes its explicit bounded linear
quotient error. Coefficients are evaluated at the retained old height; no
continuity across merged heights is silently used. -/
theorem quotient_error_of_point_motion {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (C F error : ℝ) (x xnew : E4)
    (hmove : dist xnew (NativeLocalParentPhysicalMap.physicalMap D a N p x)≤error) :
    |higherY C F xnew-(horizontalScale N*higherY C F x+
      quotientShift p (timeOrigin D a) (x 3) C F)|≤(1+|C|+|F|)*error := by
  rw [←higherY_readback]
  let old := NativeLocalParentPhysicalMap.physicalMap D a N p x
  have hc (j : Fin 4) : |xnew j-old j|≤error := by
    have hh : |xnew j-old j|≤dist xnew old := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le xnew old j
    exact hh.trans hmove
  have he : higherY C F xnew-higherY C F old=
      (xnew 2-old 2)-C*(xnew 0-old 0)-F*(xnew 1-old 1) := by
    dsimp only [higherY]
    ring
  rw [he]
  calc
    _ ≤ |xnew 2-old 2| + |C| * |xnew 0-old 0| + |F| * |xnew 1-old 1| := by
      calc
        _ ≤ |(xnew 2-old 2)-C*(xnew 0-old 0)|+|F*(xnew 1-old 1)| := abs_sub _ _
        _ ≤ (|xnew 2-old 2|+|C*(xnew 0-old 0)|)+|F*(xnew 1-old 1)| :=
          add_le_add (abs_sub _ _) le_rfl
        _ = _ := by rw [abs_mul,abs_mul]
    _ ≤ error + |C| * error + |F| * error := by
      exact add_le_add (add_le_add (hc 2) (mul_le_mul_of_nonneg_left (hc 0) (abs_nonneg C)))
        (mul_le_mul_of_nonneg_left (hc 1) (abs_nonneg F))
    _ = _ := by ring

end NativeHigherQuotientParentTransport
