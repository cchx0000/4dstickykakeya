import Theorems.Thm_StickyKakeya4_native_reference_slice_all_radii
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeRealizedSliceGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeMiddleWindowBalance NativeAnisotropicShortRowGeometry NativeSliceCountComparison
open NativeReferenceSliceAllRadii NativeSquaredGrainQueries NativeSliceClassBalls
open NativeParentSliceHeightGeometry NativeLocalParentPhysicalMap

lemma horizontalMesh_le_eighth (m : ℕ) (hm6 : 6 ≤ m) : horizontalMesh m ≤ 1/8 := by
  have hpow : (64:ℝ) ≤ ((2^m:ℕ):ℝ) := by
    have hh : (2^6:ℕ) ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm6
    exact_mod_cast hh
  unfold horizontalMesh
  have hh : (64:ℝ)/((2^m:ℕ):ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hpow
  linarith only [hh]

lemma floor_center_error {mu : ℝ} (hmu : 0 < mu) (x : ℝ) :
    |mu*((⌊x/mu⌋:ℝ)+1/2)-x| ≤ mu/2 := by
  have hlo := (le_div_iff₀ hmu).mp (Int.floor_le (x/mu))
  have hhi := (div_lt_iff₀ hmu).mp (Int.lt_floor_add_one (x/mu))
  exact abs_le.mpr ⟨by linarith only [hlo,hhi],by linarith only [hlo,hhi]⟩

lemma realized_column_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (hm6 : 6 ≤ m) (p : Parent) (k : Index) (i : Fin 3) :
    |realized (horizontalMesh m)
        (columnLabel D a (2^m) p (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) k) i-
      physicalMap D a (2^m) p (cellCenter (mesh D) k) i.castSucc| ≤ horizontalMesh m/2 := by
  have hi3 : (i.castSucc:Fin 4)≠3 := Fin.castSucc_ne_last i
  simp only [realized,columnLabel,chartWidth,hi3,if_false,←horizontalMesh_readback m hm6]
  exact floor_center_error (horizontalMesh_pos m) _

/-- Every literal occupied finest-column center remains in the parent box,
with exactly the additional half-cell rounding error. -/
theorem realized_point_coordinate_bound {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (m : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (p : Parent)
    (u : Index) (hu : u∈points D a m (phaseDepth m) E p) (v : Fin 3) :
    |realized (horizontalMesh m) u v| ≤ 3/16 := by
  simp only [points,mem_image] at hu
  obtain ⟨⟨i,k⟩,hik,rfl⟩ := hu
  have hparent := (mem_filter.mp hik).2
  have hikE := (mem_filter.mp hik).1
  have hk : k∈original i := (mem_incidences original i k).mp
    ((hE.trans (filter_subset _ _)) hikE)
  have hmb : m ≤ phaseDepth m := by unfold phaseDepth; omega
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale HB.2.1 (hmb.trans hbL)]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hphysical := physical_parent_spatial_bound h original HB.1 HB.2.2.1
    (2^m) hscale p i hparent k hk v
  have herror := realized_column_error D a m hm6 p k v
  have hmesh := horizontalMesh_le_eighth m hm6
  have htri := abs_sub_le
    (realized (horizontalMesh m) (columnLabel D a (2^m) p
      (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) k) v)
    (physicalMap D a (2^m) p (cellCenter (mesh D) k) v.castSucc) 0
  simp only [sub_zero] at htri
  linarith only [htri,herror,hphysical,hmesh]

theorem realized_slice_geometry {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (m : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (p : Parent) (height : ℤ) :
    let P := realizedSlice (points D a m (phaseDepth m) E p) (horizontalMesh m) height
    (∀x∈P,∀v : Fin 3,|x v| ≤ 3/16) ∧ (∀x∈P,∀y∈P,dist x y ≤ 3/8) := by
  dsimp only
  have Hcoord : ∀x∈realizedSlice (points D a m (phaseDepth m) E p) (horizontalMesh m) height,
      ∀v : Fin 3,|x v| ≤ 3/16 := by
    intro x hx v
    simp only [realizedSlice,mem_image,heightSlice,mem_filter] at hx
    obtain ⟨u,⟨hu,_hh⟩,rfl⟩ := hx
    exact realized_point_coordinate_bound h original R level HB m hm6 hbL E hE p u hu v
  refine ⟨Hcoord,?_⟩
  intro x hx y hy
  rw [dist_pi_le_iff (by norm_num : (0:ℝ)≤3/8)]
  intro v
  rw [Real.dist_eq]
  exact (abs_sub _ _).trans (by linarith only [Hcoord x hx v,Hcoord y hy v])

/-- The literal horizontal cell centers are separated by their true mesh. -/
theorem realized_slice_separated (P : Finset Index) (mu : ℝ) (hmu : 0 < mu) (height : ℤ) :
    FiniteVoronoiPopulation.Separated (realizedSlice P mu height) mu := by
  intro x hx y hy hne
  by_contra hn
  have hdist : dist x y < mu := lt_of_not_ge hn
  simp only [realizedSlice,mem_image] at hx hy
  obtain ⟨u,_hu,rfl⟩ := hx
  obtain ⟨v,_hv,rfl⟩ := hy
  apply hne
  funext i
  have hi := (dist_pi_lt_iff hmu).mp hdist i
  rw [Real.dist_eq] at hi
  have he : realized mu u i-realized mu v i=mu*((u i.castSucc:ℝ)-(v i.castSucc:ℝ)) := by
    unfold realized
    ring
  rw [he,abs_mul,abs_of_pos hmu] at hi
  have hsmall : |(u i.castSucc:ℝ)-(v i.castSucc:ℝ)| < 1 := by nlinarith only [hi,hmu]
  have hint : |u i.castSucc-v i.castSucc| < (1:ℤ) := by exact_mod_cast hsmall
  have heq : u i.castSucc=v i.castSucc := by
    obtain ⟨hl,hh⟩ := abs_lt.mp hint
    omega
  simp only [realized,heq]

end NativeRealizedSliceGeometry
