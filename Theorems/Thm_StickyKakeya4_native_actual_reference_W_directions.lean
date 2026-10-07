import Theorems.Thm_StickyKakeya4_native_actual_reference_W_geometry
import Theorems.Thm_StickyKakeya4_native_coarse_direction_thinning
import Theorems.Thm_StickyKakeya4_original_macro_printed_w

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeActualReferenceWDirections
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeCoarseDirectionThinning NativeDyadicParentCells
open NativeLocalParentGeometry NativeActualReferenceWGeometry NativeAnisotropicGlobalSourceBridge
open OriginalMacroDirectionCells OriginalMacroPrintedW OriginalWWitnessCounts OriginalWCoarseEscapeMenus

def slope {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (m f : ℕ) (p t : Parent) : Fin 3 → ℝ :=
  localSlope D (2^m) p (representative h R a (2^f) t)

/-- Active fine phases use the SAME global R representative, and it belongs
to the actual fixed outer parent. There is no new representative selection. -/
theorem representative_parent {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (m f : ℕ) (hmf : m ≤ f)
    (p : Parent) (H : Finset (Fin n × Index))
    (hR : ∀z∈H,z.1∈R) (hp : ∀z∈H,parentLabel D a (2^m) z.1=p)
    (t : Parent) (ht : t∈TwoTubePathCollisionCount.tubes (incidences D a m f p H)) :
    representative h R a (2^f) t∈R ∧ parentLabel D a (2^f) (representative h R a (2^f) t)=t ∧
      parentLabel D a (2^m) (representative h R a (2^f) t)=p := by
  obtain ⟨e,he,het⟩ := mem_image.mp ht
  obtain ⟨z,hz,hze⟩ := mem_image.mp he
  have hzFine : parentLabel D a (2^f) z.1=t := by
    exact (congrArg Prod.snd hze).trans het
  have htR : t∈R.image (parentLabel D a (2^f)) := by
    rw [←hzFine]
    exact mem_image_of_mem _ (hR z hz)
  obtain ⟨hrepR,hrepFine⟩ := representative_spec h R a (2^f) htR
  refine ⟨hrepR,hrepFine,?_⟩
  rw [←parent_ancestor_eq D a hmf _,hrepFine,←hzFine,parent_ancestor_eq D a hmf z.1]
  exact hp z hz

/-- The normalized actual parent slopes give a literal full angular-grid
menu. The honest ambient exponent is three; no kappa bound is inferred. -/
theorem full_direction_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (m f : ℕ) (hmf : m ≤ f)
    (p : Parent) (H : Finset (Fin n × Index))
    (hR : ∀z∈H,z.1∈R) (hp : ∀z∈H,parentLabel D a (2^m) z.1=p)
    (q : ℝ) (hq : 0 < q) :
    let I := incidences D a m f p H
    let u := fun t => slope h R a m f p t (0:Fin 3)
    let v := fun t => (slope h R a m f p t (1:Fin 3),slope h R a m f p t (2:Fin 3))
    (((TwoTubePathCollisionCount.tubes I).image (directionCell (q/8) u v)).card:ℝ) ≤ (16/q+2)^3 := by
  intro I u v
  have hBound : ∀t∈TwoTubePathCollisionCount.tubes I,∀j,|slope h R a m f p t j| ≤ 1 := by
    intro t ht j
    exact localSlope_bound D a (2^m) p _ (representative_parent h R m f hmf p H hR hp t ht).2.2 j
  have hh := direction_cells_box_bound (TwoTubePathCollisionCount.tubes I) u v 0 (0,0)
    (by positivity : 0<q/8) (show 0≤8/q by positivity)
    (fun t ht => by
      rw [sub_zero,show (8/q)*(q/8)=(1:ℝ) by field_simp]
      exact hBound t ht 0)
    (fun t ht => by
      rw [show (8/q)*(q/8)=(1:ℝ) by field_simp]
      simpa [v,Prod.norm_def] using max_le (hBound t ht 1) (hBound t ht 2))
  have he : 2*(8/q)+2=16/q+2 := by ring
  simpa only [directionCells,he] using hh

/-- Every collided path pair retains its four geometric incidence legs,
its literal shared heights, and full Euclidean terminal-direction closeness. -/
theorem witness_full_direction_conditions {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (m f : ℕ)
    (p : Parent) (H : Finset (Fin n × Index)) (q : ℝ) (hq : 0 < q)
    (w : TwoTubePathCollisionCount.Path Index Parent × TwoTubePathCollisionCount.Path Index Parent)
    (hw : w∈witnesses (incidences D a m f p H) (fun k => k (3:Fin 4))
      (directionCell (q/8) (fun t => slope h R a m f p t (0:Fin 3))
        (fun t => (slope h R a m f p t (1:Fin 3),slope h R a m f p t (2:Fin 3))))) :
    w.1∈TwoTubePathCollisionCount.paths (incidences D a m f p H) ∧
    w.2∈TwoTubePathCollisionCount.paths (incidences D a m f p H) ∧
    w.2.point₀=w.1.point₀ ∧ w.2.point₁ (3:Fin 4)=w.1.point₁ (3:Fin 4) ∧
    w.2.point₂ (3:Fin 4)=w.1.point₂ (3:Fin 4) ∧
    dist (EuclideanAlignmentPatches.euclidean (slope h R a m f p w.2.tube₂))
      (EuclideanAlignmentPatches.euclidean (slope h R a m f p w.1.tube₂)) ≤ q := by
  have hh := original_full_witness_conditions (incidences D a m f p H) (fun k => k (3:Fin 4))
    (fun t => slope h R a m f p t (0:Fin 3))
    (fun t => (slope h R a m f p t (1:Fin 3),slope h R a m f p t (2:Fin 3))) hq hw
  have he (t : Parent) : directionVector (fun t => slope h R a m f p t (0:Fin 3))
      (fun t => (slope h R a m f p t (1:Fin 3),slope h R a m f p t (2:Fin 3))) t=
      slope h R a m f p t := by
    funext j
    fin_cases j <;> rfl
  simpa only [he] using hh

end NativeActualReferenceWDirections
