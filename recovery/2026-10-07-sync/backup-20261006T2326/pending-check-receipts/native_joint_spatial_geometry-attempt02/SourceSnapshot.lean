import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_caps
import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_menu
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeJointSpatialGeometry
open NativeHorizontalGrainSlice
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeReferenceXYGridMetric NativeReferenceXYGridCaps NativeAnisotropicShortRowGeometry
open NativeNormalizedCellRelativeMenu NativeTranslatedGrainHeightOverlap NativeGrainQuotientInjection
open scoped Matrix.Norms.Elementwise

/-- The existing full metric inverse includes the actual mu/8 discrepancy
of equal translated-height bins. At the genuine joint scales this gives a
fixed eight-cell diameter, with no equality of old real times assumed. -/
theorem coarse_xy_old_dist {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6  ≤  m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1  ≤  ell) (hell4 : ell  ≤  4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖  ≤  (1/4:ℝ))
    (R : ℕ) (hR : 512  ≤  R) (k l : Index)
    (he : coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)=
      coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F l)) :
    dist (oldPoint D a m p k) (oldPoint D a m p l)  ≤  8*((R:ℝ)*mu m) := by
  have hRp : 0 < R := by omega
  have ht : translatedHeight D a m k=translatedHeight D a m l := congrArg Prod.fst he
  have hX (j : Fin (ell-1)) := congrArg (fun z : XY ell => z.2.1 j) he
  have hY (j : Fin (4-ell)) := congrArg (fun z : XY ell => z.2.2 j) he
  simp only [coarseXY_x] at hX
  simp only [coarseXY_y] at hY
  have hwidth : 0 < (R:ℝ)*mu m := mul_pos (by exact_mod_cast hRp) (mu_pos m)
  have hb := old_dist_of_coordinate_bounds h m ell hm p i hi P hP hell hell4 hd F hF k l ht
    ((R:ℝ)*mu m) hwidth.le
    (fun j => same_floor_abs hwidth (hX j)) (fun j => same_floor_abs hwidth (hY j))
  have hRr : (512:ℝ)  ≤  R := by exact_mod_cast hR
  have hscale := mul_le_mul_of_nonneg_right hRr (mu_pos m).le
  have hmu := mu_pos m
  nlinarith only [hb,hscale,hmu]

/-- Literal original physical cells lie in a bounded halo of an actual
source witness. This concerns occupied cell labels, not old edge counts. -/
theorem physical_neighbor {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6  ≤  m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1  ≤  ell) (hell4 : ell  ≤  4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖  ≤  (1/4:ℝ))
    (R depth : ℕ) (hR : 512  ≤  R) (hscale : (R:ℝ)*mu m=64/((2^depth:ℕ):ℝ))
    (k l : Index)
    (he : coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)=
      coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F l)) :
    physicalCell D a (2^m) (2^depth) p k ∈
      columnHalo 8 8 (physicalCell D a (2^m) (2^depth) p l) := by
  have hb := coarse_xy_old_dist h m ell hm p i hi P hP hell hell4 hd F hF R hR k l he
  rw [hscale] at hb
  apply Fintype.mem_piFinset.mpr
  intro j
  simp only [ite_self]
  change ⌊oldPoint D a m p k j/(64/((2^depth:ℕ):ℝ))⌋ ∈
    Icc (⌊oldPoint D a m p l j/(64/((2^depth:ℕ):ℝ))⌋-(8:ℤ))
      (⌊oldPoint D a m p l j/(64/((2^depth:ℕ):ℝ))⌋+8)
  apply floor_neighbor (by positivity) 8
  have hc : |oldPoint D a m p k j-oldPoint D a m p l j|  ≤ 
      dist (oldPoint D a m p k) (oldPoint D a m p l) := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le (oldPoint D a m p k) (oldPoint D a m p l) j
  exact hc.trans hb

/-- One actual coarse XY fiber meets at most17^4 original physical cells. -/
theorem physical_fiber_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6  ≤  m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1  ≤  ell) (hell4 : ell  ≤  4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖  ≤  (1/4:ℝ))
    (R depth : ℕ) (hR : 512  ≤  R) (hscale : (R:ℝ)*mu m=64/((2^depth:ℕ):ℝ))
    (S : Finset Index) (z : XY ell) :
    (((S.filter (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)=z)).image
      (physicalCell D a (2^m) (2^depth) p)).card)  ≤  17^4 := by
  let U := S.filter (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)=z)
  by_cases hU : U.Nonempty
  · obtain ⟨l,hl⟩ := hU
    have hsub : U.image (physicalCell D a (2^m) (2^depth) p) ⊆
        columnHalo 8 8 (physicalCell D a (2^m) (2^depth) p l) := by
      intro q hq
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hq
      exact physical_neighbor h m ell hm p i hi P hP hell hell4 hd F hF R depth hR hscale k l
        ((mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm)
    exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)
  · rw [not_nonempty_iff_eq_empty] at hU
    change (U.image _).card  ≤  _
    simp only [hU,image_empty,card_empty,Nat.zero_le]

/-- Projection to literal original physical cells is controlled by occupied
coarse XY keys on the same incidences; all repeated edges are discarded by
actual finite images on both sides. -/
theorem physical_image_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6  ≤  m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hell : 1  ≤  ell) (hell4 : ell  ≤  4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖  ≤  (1/4:ℝ))
    (R depth : ℕ) (hR : 512  ≤  R) (hscale : (R:ℝ)*mu m=64/((2^depth:ℕ):ℝ))
    (S : Finset (Fin n × Index)) :
    ((S.image (fun z => physicalCell D a (2^m) (2^depth) p z.2)).card:ℝ)  ≤ 
      ((17^4:ℕ):ℝ)*((S.image (fun z => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F z.2))).card:ℝ) := by
  apply NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
  intro z _hz
  have hh := lift_incidence_capacity S Prod.snd
    (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k))
    (physicalCell D a (2^m) (2^depth) p) (17^4)
    (physical_fiber_card h m ell hm p i hi P hP hell hell4 hd F hF R depth hR hscale) z
  exact_mod_cast hh

end NativeJointSpatialGeometry
