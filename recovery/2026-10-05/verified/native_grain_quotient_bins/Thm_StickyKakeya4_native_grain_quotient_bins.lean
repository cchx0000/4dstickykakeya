import Theorems.Thm_StickyKakeya4_native_grain_quotient_geometry
import Theorems.Thm_StickyKakeya4_original_height_interval_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeGrainQuotientBins
open Classical Finset StickyKakeya4 NativeGrainQuotientGeometry
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeSquaredGrainQueries
open NativeActualProjectedGrainCount NativeOriginalPacketReference NativeParentGrainIncidenceCleanup
open NativeSpatialAngularGeometry NativeOriginalCellChartGeometry NativeHorizontalGrainSlice
open NativeProjectorCellChart
open scoped BigOperators

/-- Literal terminal-resolution quotient labels, without replacing points. -/
def label {d : ℕ} (mu : ℝ) (x : EuclideanSpace ℝ (Fin d)) : Fin d → ℤ :=
  fun j => ⌊x j/mu⌋

def box {d : ℕ} (mu H : ℝ) (c : EuclideanSpace ℝ (Fin d)) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun j => Icc ⌊(c j-H)/mu⌋ ⌊(c j+H)/mu⌋)

lemma label_mem_box {d : ℕ} {mu H : ℝ} (hmu : 0 < mu)
    (x c : EuclideanSpace ℝ (Fin d)) (hclose : ‖x-c‖ ≤ H) :
    label mu x∈box mu H c := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hh : |x j-c j| ≤ H := by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using (PiLp.norm_apply_le (x-c) j).trans hclose
  obtain ⟨hlo,hhi⟩ := abs_le.mp hh
  exact mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hmu.le),
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hmu.le)⟩

lemma box_card {d : ℕ} {mu H : ℝ} (hmu : 0 < mu) (hH : 0 ≤ H)
    (c : EuclideanSpace ℝ (Fin d)) : ((box mu H c).card:ℝ) ≤ (2*H/mu+2)^d := by
  have hcoord (j : Fin d) := OriginalHeightIntervalCap.floor_interval_card
    mu (c j-H) (2*H) hmu (by positivity)
  have he (j : Fin d) : c j-H+2*H=c j+H := by ring
  simp_rw [he] at hcoord
  rw [box,Fintype.card_piFinset,Nat.cast_prod]
  calc
    _ ≤ ∏_j : Fin d,(2*H/mu+2) := prod_le_prod
      (fun _ _ => Nat.cast_nonneg _) (fun j _ => hcoord j)
    _ = _ := by simp

/-- Occupied bins are counted geometrically, irrespective of raw multiplicity. -/
theorem occupied_card {A : Type*} {d : ℕ} (S : Finset A)
    (f : A → EuclideanSpace ℝ (Fin d)) {mu H : ℝ}
    (hmu : 0 < mu) (hH : 0 ≤ H) (c : EuclideanSpace ℝ (Fin d))
    (hclose : ∀x∈S,‖f x-c‖ ≤ H) :
    ((S.image (fun x => label mu (f x))).card:ℝ) ≤ (2*H/mu+2)^d := by
  apply (Nat.cast_le.mpr (card_le_card (show
    S.image (fun x => label mu (f x))⊆box mu H c from ?_))).trans (box_card hmu hH c)
  intro b hb
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
  exact label_mem_box hmu (f x) c (hclose x hx)

/-- Pigeonhole on the literal original elements, with the paid image count. -/
theorem exists_dense_fiber {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (hS : S.Nonempty) (f : A → B) (C : ℝ)
    (hC : ((S.image f).card:ℝ) ≤ C) :
    ∃x∈S,(S.filter (fun y => f y=f x)).Nonempty ∧
      (S.card:ℝ) ≤ C*(S.filter (fun y => f y=f x)).card := by
  obtain ⟨b,hb,hmax⟩ := exists_max_image (S.image f)
    (fun b => (S.filter (fun x => f x=b)).card) (hS.image f)
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
  refine ⟨x,hx,⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩,?_⟩
  have hsum : S.card ≤ (S.image f).card*(S.filter (fun y => f y=f x)).card := by
    calc
      _ = ∑b∈S.image f,(S.filter (fun y => f y=b)).card := card_eq_sum_card_image f S
      _ ≤ ∑_b∈S.image f,(S.filter (fun y => f y=f x)).card := sum_le_sum (fun b hb => hmax b hb)
      _ = _ := by simp
  exact (show (S.card:ℝ) ≤ ((S.image f).card:ℝ)*(S.filter (fun y => f y=f x)).card by
    exact_mod_cast hsum).trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))

/-- A thick finite grain has a dense actual fiber at the requested resolution. -/
theorem exists_dense_quotient_fiber {A : Type*} [DecidableEq A] {d : ℕ}
    (S : Finset A) (hS : S.Nonempty) (f : A → EuclideanSpace ℝ (Fin d))
    {mu H : ℝ} (hmu : 0 < mu) (hH : 0 ≤ H)
    (hdiam : ∀x∈S,∀y∈S,‖f x-f y‖ ≤ H) :
    ∃x∈S,(S.filter (fun y => label mu (f y)=label mu (f x))).Nonempty ∧
      (S.card:ℝ) ≤ (2*H/mu+2)^d*(S.filter (fun y => label mu (f y)=label mu (f x))).card := by
  obtain ⟨x0,hx0⟩ := hS
  apply exists_dense_fiber S ⟨x0,hx0⟩ (fun x => label mu (f x))
  exact occupied_card S f hmu hH (f x0) (fun x hx => hdiam x hx x0 hx0)

/-- Raw phase-scale vertices inside a mixed fiber, at one exact raw height. -/
def heightFiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (t : ℤ) : Finset Index :=
  (mixedVertices D a m (phaseDepth m) plane ell E c).filter (fun k => k (3:Fin 4)=t)

/-- Coordinates of the unchanged raw vertex under the genuine parent map. -/
def rawCoordinates {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (parent : Parent) (P Q : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (k : Index) : EuclideanSpace ℝ (Fin (4-ell)) :=
  coordinates P Q hP ell hell hell4 hd
    (NativeLocalParentPhysicalMap.physicalMap D a (2^m) parent
      (cellCenter (64/((2^(phaseDepth m):ℕ):ℝ)) k))

/-- The exact diameter retained after horizontal slicing and parent normalization. -/
def diameter (m ell : ℕ) : ℝ := (15/2:ℝ)*(((2^m:ℕ):ℝ)/512)*grainWidth m ell

lemma diameter_pos (m ell : ℕ) : 0 < diameter m ell := by
  unfold diameter
  exact mul_pos (mul_pos (by norm_num) (by positivity)) (grainWidth_pos m ell)

lemma height_fiber_diameter {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (t : ℤ) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (hPQ : Module.finrank ℝ P=Module.finrank ℝ (sliceSpace (plane c.2.1)))
    (hc : cell P=cell (sliceSpace (plane c.2.1)))
    (v : E4) (hvR : v∈plane c.2.1) (hv : v (3:Fin 4)=1) (hvn : ‖v‖ ≤ 2)
    (k l : Index) (hk : k∈heightFiber D a m ell plane E c t)
    (hl : l∈heightFiber D a m ell plane E c t) :
    ‖rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd k-
      rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd l‖ ≤ diameter m ell := by
  obtain ⟨hkV,hkt⟩ := mem_filter.mp hk
  obtain ⟨hlV,hlt⟩ := mem_filter.mp hl
  have hheight : cellCenter (64/((2^(phaseDepth m):ℕ):ℝ)) k (3:Fin 4)=
      cellCenter (64/((2^(phaseDepth m):ℕ):ℝ)) l (3:Fin 4) := by
    simp only [cellCenter,hkt,hlt]
  have hh := parent_coordinates_difference D a (2^m) c.1 P (plane c.2.1) hP ell hell hell4 hd
    hPQ hc hvR hv hvn hheight (mixed_vertices_near D a m ell plane E c k l hkV hlV)
  change _ ≤ (15/4:ℝ)*(((2^m:ℕ):ℝ)/512)*(2*grainWidth m ell) at hh
  calc
    _ ≤ (15/4:ℝ)*(((2^m:ℕ):ℝ)/512)*(2*grainWidth m ell) := hh
    _ = diameter m ell := by unfold diameter; ring

/-- Actual occupied quotient bins of the raw height slice are bounded by
its thickness, with every scale factor displayed. -/
theorem mixed_occupied_quotient_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (t : ℤ) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (hPQ : Module.finrank ℝ P=Module.finrank ℝ (sliceSpace (plane c.2.1)))
    (hc : cell P=cell (sliceSpace (plane c.2.1)))
    (v : E4) (hvR : v∈plane c.2.1) (hv : v (3:Fin 4)=1) (hvn : ‖v‖ ≤ 2)
    (mu : ℝ) (hmu : 0 < mu) :
    let f := rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd
    (((heightFiber D a m ell plane E c t).image (fun k => label mu (f k))).card:ℝ) ≤
      (2*diameter m ell/mu+2)^(4-ell) := by
  intro f
  by_cases hS : (heightFiber D a m ell plane E c t).Nonempty
  · obtain ⟨k,hk⟩ := hS
    exact occupied_card _ f hmu (diameter_pos m ell).le (f k)
      (fun l hl => height_fiber_diameter D a m ell plane E c t P hP hell hell4 hd hPQ hc v hvR hv hvn l k hl hk)
  · rw [not_nonempty_iff_eq_empty] at hS
    simp only [hS,image_empty,card_empty,Nat.cast_zero]
    exact pow_nonneg (by have hp := diameter_pos m ell; positivity) _

end NativeGrainQuotientBins
