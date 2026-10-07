import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_points

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeReferenceXYGridMaps
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridPoints
open NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates NativeGrainQuotientInjection
open NativeGrainQuotientBins NativeTranslatedGrainHeightOverlap NativeHeightSlopeCoordinates
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeSelectedHorizontalGraphChart
open scoped BigOperators Matrix.Norms.Elementwise

abbrev XY (ell : ℕ) := ℤ × ((Fin (ell-1) → ℤ) × (Fin (4-ell) → ℤ))

/-- ONE total fixed XY map on every reference incidence point. Its field
matrix depends only on the actual translated height, including off-core. -/
def pxy {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (k : Index) : XY ell :=
  (translatedHeight D a m k,
    (label (mu m) (tangentCoordinates P ell hd (rawPoint D a m p k)),
      label (mu m) (quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k))))

/-- Coarsening keeps the actual reference height exactly. -/
def coarseXY (ell R : ℕ) (z : XY ell) : XY ell :=
  (z.1,(fun j => z.2.1 j/(R:ℤ),fun j => z.2.2 j/(R:ℤ)))

lemma pxy_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (k : Index) :
    (pxy D a m ell p P hP hell hell4 hd F k).1=pref D a m p k (3:Fin 4) := (pref_height D a m p k).symm

lemma coarseXY_x {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (R : ℕ) (k : Index) (j : Fin (ell-1)) :
    (coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)).2.1 j=
      ⌊tangentCoordinates P ell hd (rawPoint D a m p k) j/((R:ℝ)*mu m)⌋ := by
  exact floor_div_scale _ _ R

lemma coarseXY_y {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (R : ℕ) (k : Index) (j : Fin (4-ell)) :
    (coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)).2.2 j=
      ⌊quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k) j/((R:ℝ)*mu m)⌋ := by
  exact floor_div_scale _ _ R

lemma same_floor_abs {r x y : ℝ} (hr : 0 < r) (he : ⌊x/r⌋=⌊y/r⌋) : |x-y| ≤ r := by
  have hxl := (le_div_iff₀ hr).mp (Int.floor_le (x/r))
  have hxu := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (x/r))
  have hyl := (le_div_iff₀ hr).mp (Int.floor_le (y/r))
  have hyu := (div_lt_iff₀ hr).mp (Int.lt_floor_add_one (y/r))
  rw [he] at hxl hxu
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

lemma floor_neighbor {r x y : ℝ} (hr : 0 < r) (K : ℕ) (hxy : |x-y| ≤ (K:ℝ)*r) :
    ⌊x/r⌋∈Icc (⌊y/r⌋-(K:ℤ)) (⌊y/r⌋+K) := by
  have hh : |x/r-y/r| ≤ K := by
    rw [←sub_div,abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr hxy
  obtain ⟨hlo,hhi⟩ := abs_le.mp hh
  apply mem_Icc.mpr
  constructor
  · simpa only [Int.floor_sub_natCast] using
      (Int.floor_mono (show y/r-(K:ℝ) ≤ x/r by linarith))
  · simpa only [Int.floor_add_natCast] using
      (Int.floor_mono (show x/r ≤ y/r+(K:ℝ) by linarith))

lemma euclidean_coord_bound {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (B : ℝ)
    (h : ∀j,|x j| ≤ B) : ‖x‖ ≤ (d:ℝ)*B := by
  calc
    _ ≤ ∑j : Fin d,|x j| := euclidean_norm_le_sum x
    _ ≤ ∑_j : Fin d,B := sum_le_sum (fun j _ => h j)
    _ = _ := by simp

/-- Exact readback of the new matrix-based quotient to the old graph-map
quotient whenever the chosen matrix is the actual selected node matrix. -/
lemma quotient_nodeSlope (P Q : Submodule ℝ E4) (hP : P≤heightKernel) (hQ : Q≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (x : E4) :
    quotientMap P hP ell hell hell4 hd (nodeSlope P hP ell hell hell4 hd Q hQ) x=
      NativeGrainQuotientGeometry.coordinates P Q hP ell hell hell4 hd x := by
  let G := totalGraph P Q
  let hg := totalGraph_horizontal P Q hP hQ
  have hp := Submodule.orthogonalProjectionOnto_starProjection_of_le
    (show normalSpace P≤Pᗮ from inf_le_left) x
  have hG : (G (P.orthogonalProjectionOnto x):E4)∈normalSpace P :=
    ⟨(G (P.orthogonalProjectionOnto x)).property,hg _⟩
  have hGp : (normalSpace P).orthogonalProjectionOnto (G (P.orthogonalProjectionOnto x):E4)=
      horizontalGraph P G hg (P.orthogonalProjectionOnto x) := by
    apply Subtype.ext
    exact (normalSpace P).starProjection_eq_self_iff.mpr hG
  have hm : (nodeSlope P hP ell hell hell4 hd Q hQ).toEuclideanLin (tangentCoordinates P ell hd x)=
      slopeMap P hP ell hell hell4 hd G hg (tangentCoordinates P ell hd x) :=
    nodeSlope_action P hP ell hell hell4 hd Q hQ (tangentCoordinates P ell hd x)
  change normalCoordinates P hP ell hell hell4 hd x-
      (nodeSlope P hP ell hell hell4 hd Q hQ).toEuclideanLin (tangentCoordinates P ell hd x)=_
  rw [hm]
  change (normalBasis P hP ell hell hell4 hd).repr ((normalSpace P).orthogonalProjectionOnto x)-
      (normalBasis P hP ell hell hell4 hd).repr
        (horizontalGraph P G hg ((domainBasis P ell hd).repr.symm
          ((domainBasis P ell hd).repr (P.orthogonalProjectionOnto x))))=
    (normalBasis P hP ell hell hell4 hd).repr ((normalSpace P).orthogonalProjectionOnto
      (Pᗮ.starProjection x-(G (P.orthogonalProjectionOnto x):E4)))
  rw [LinearIsometryEquiv.symm_apply_apply,map_sub,hp,hGp,map_sub]

end NativeReferenceXYGridMaps
