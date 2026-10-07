import Theorems.Thm_StickyKakeya4_native_grain_quotient_injection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeGrainQuotientImage
open Classical Finset StickyKakeya4 NativeGrainQuotientGeometry NativeGrainQuotientBins
open NativeGrainQuotientFibers NativeGrainQuotientInjection NativeHorizontalGrainSlice
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup NativeProjectorCellChart

/-- Tangent coordinates of every unchanged raw physical vertex. -/
def rawTangent {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (parent : Parent) (P : Submodule ℝ E4) (hd : Module.finrank ℝ P=ell-1)
    (k : Index) : EuclideanSpace ℝ (Fin (ell-1)) :=
  tangentCoordinates P ell hd
    (NativeLocalParentPhysicalMap.physicalMap D a (2^m) parent
      (cellCenter (64/((2^(phaseDepth m):ℕ):ℝ)) k))

/-- On a fixed time/quotient fiber, tangent bins at the true physical mesh/8
are injective on raw vertices. Distinct physical points are never collapsed. -/
theorem tangent_label_injOn {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (t : ℤ) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (b : Fin (4-ell) → ℤ) :
    let f := rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd
    Set.InjOn (fun k => label mu (rawTangent D a m ell c.1 P hd k))
      (↑(fiber D a m ell plane E c t mu f b) : Set Index) := by
  intro f k hk l hl heq
  by_contra hne
  have hkF := mem_filter.mp hk
  have hlF := mem_filter.mp hl
  have hkt := (mem_filter.mp hkF.1).2
  have hlt := (mem_filter.mp hlF.1).2
  have ht : k (3:Fin 4)=l (3:Fin 4) := hkt.trans hlt.symm
  have hY := hkF.2.trans hlF.2.symm
  have hhorizontal := physical_difference_horizontal D a m (phaseDepth m) c.1 k l ht
  have hnorm := same_coordinate_bins_norm hmu P (sliceSpace (plane c.2.1)) hP
    (show sliceSpace (plane c.2.1)≤heightKernel from inf_le_right)
    ell hell hell4 hd _ _ hhorizontal heq hY
  have hsep := physical_vertex_separated D a m (phaseDepth m) c.1 k l ht hne
  have hpos := physicalMesh_pos m (phaseDepth m)
  linarith

/-- Actual tangent-bin X coordinates of an actual raw time/quotient fiber. -/
def X {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (t : ℤ) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (b : Fin (4-ell) → ℤ) : Finset (Fin (ell-1) → ℤ) :=
  (fiber D a m ell plane E c t mu
    (rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd) b).image
      (fun k => label mu (rawTangent D a m ell c.1 P hd k))

lemma X_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (t : ℤ) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (b : Fin (4-ell) → ℤ) :
    (X D a m ell plane E c t P hP hell hell4 hd mu b).card=
      (fiber D a m ell plane E c t mu
        (rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd) b).card :=
  card_image_of_injOn (tangent_label_injOn D a m ell plane E c t P hP hell hell4 hd mu hmu hmesh b)

/-- A dense X fiber consists of actual occupied tangent bins, each witnessed
by one distinct original raw vertex. No new AD property is assumed. -/
theorem exists_dense_X {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (hV : (mixedVertices D a m (phaseDepth m) plane ell E c).Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (hPQ : Module.finrank ℝ P=Module.finrank ℝ (sliceSpace (plane c.2.1)))
    (hc : cell P=cell (sliceSpace (plane c.2.1)))
    (v : E4) (hvR : v∈plane c.2.1) (hv : v (3:Fin 4)=1) (hvn : ‖v‖ ≤ 2)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8) :
    ∃t : ℤ,∃b : Fin (4-ell) → ℤ,
      (X D a m ell plane E c t P hP hell hell4 hd mu b).Nonempty ∧
      (mixedVertices D a m (phaseDepth m) plane ell E c).card ≤
        (((2^(phaseDepth m-m):ℕ):ℝ)*(2*diameter m ell/mu+2)^(4-ell))*
          (X D a m ell plane E c t P hP hell hell4 hd mu b).card := by
  obtain ⟨t,b,hS,hcard⟩ := exists_mixed_dense_fiber D a m ell hm plane E c hV P hP
    hell hell4 hd hPQ hc v hvR hv hvn mu hmu
  refine ⟨t,b,hS.image _,?_⟩
  rwa [X_card D a m ell plane E c t P hP hell hell4 hd mu hmu hmesh b]

/-- The witness X fiber lower-bounds the image of ALL mixed-grain points;
no original occurrence or incidence is discarded by this conclusion. -/
theorem full_tangent_image_lower {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (hV : (mixedVertices D a m (phaseDepth m) plane ell E c).Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (hPQ : Module.finrank ℝ P=Module.finrank ℝ (sliceSpace (plane c.2.1)))
    (hc : cell P=cell (sliceSpace (plane c.2.1)))
    (v : E4) (hvR : v∈plane c.2.1) (hv : v (3:Fin 4)=1) (hvn : ‖v‖ ≤ 2)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8) :
    (mixedVertices D a m (phaseDepth m) plane ell E c).card ≤
      (((2^(phaseDepth m-m):ℕ):ℝ)*(2*diameter m ell/mu+2)^(4-ell))*
        ((mixedVertices D a m (phaseDepth m) plane ell E c).image
          (fun k => label mu (rawTangent D a m ell c.1 P hd k))).card := by
  obtain ⟨t,b,_hX,hcard⟩ := exists_dense_X D a m ell hm plane E c hV P hP hell hell4 hd
    hPQ hc v hvR hv hvn mu hmu hmesh
  have hsub : X D a m ell plane E c t P hP hell hell4 hd mu b ⊆
      (mixedVertices D a m (phaseDepth m) plane ell E c).image
        (fun k => label mu (rawTangent D a m ell c.1 P hd k)) := by
    apply image_subset_image
    exact (filter_subset _ _).trans (filter_subset _ _)
  exact hcard.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub))
    (by have hp := diameter_pos m ell; positivity))

/-- At phase mesh/8 the quotient loss is a fixed dimension-dependent
constant. The separately displayed height factor is not called subpower. -/
lemma phase_quotient_loss (m ell : ℕ) :
    (2*diameter m ell/(physicalMesh m (phaseDepth m)/8)+2)^(4-ell)=
      (120*(4:ℝ)^ell*258+2)^(4-ell) := by
  congr 1
  have he := phase_diameter_div_physicalMesh m ell
  calc
    _ = 16*(diameter m ell/physicalMesh m (phaseDepth m))+2 := by ring
    _ = _ := by rw [he]; ring

end NativeGrainQuotientImage
