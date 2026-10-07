import Theorems.Thm_StickyKakeya4_native_grain_height_projection_source

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeGrainHeightProjectionFibers
open Classical Finset StickyKakeya4 NativeGrainQuotientGeometry NativeGrainQuotientBins
open NativeGrainQuotientFibers NativeGrainQuotientImage NativeGrainHeightProjectionSource
open NativeHorizontalGrainSlice NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup

/-- ALL raw heights in one actual quotient bin at the common coarse node.
The input vertices and their physical quotient coordinates are unchanged. -/
def wholeFiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (b : Fin (4-ell) → ℤ) : Finset Index :=
  (mixedVertices D a m (phaseDepth m) plane ell E c).filter
    (fun k => label mu (rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd k)=b)

/-- Actual occupied X bins in the whole coarse-height quotient class. -/
def wholeX {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (b : Fin (4-ell) → ℤ) : Finset (Fin (ell-1) → ℤ) :=
  (wholeFiber D a m ell plane E c P hP hell hell4 hd mu b).image
    (fun k => label mu (rawTangent D a m ell c.1 P hd k))

/-- Exact-height injection is used ONLY to count an X-bin's preimages.
Every raw height remains in the actual quotient class. -/
theorem wholeFiber_card_le_X {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (b : Fin (4-ell) → ℤ) :
    (wholeFiber D a m ell plane E c P hP hell hell4 hd mu b).card ≤
      (((2^(phaseDepth m-m):ℕ):ℝ))*(wholeX D a m ell plane E c P hP hell hell4 hd mu b).card := by
  let V := mixedVertices D a m (phaseDepth m) plane ell E c
  let S := wholeFiber D a m ell plane E c P hP hell hell4 hd mu b
  let g := fun k => label mu (rawTangent D a m ell c.1 P hd k)
  have hcap : ∀j∈S.image g,(((S.filter (fun k => g k=j)).image id).card:ℝ) ≤
      (((2^(phaseDepth m-m):ℕ):ℝ)) := by
    intro j _hj
    let T := S.filter (fun k => g k=j)
    have hTV : T⊆V := (filter_subset _ _).trans (filter_subset _ _)
    have hinj : Set.InjOn (fun k : Index => k (3:Fin 4)) (↑T : Set Index) := by
      intro k hk l hl ht
      have hkT := mem_filter.mp hk
      have hlT := mem_filter.mp hl
      have hkS := mem_filter.mp hkT.1
      have hlS := mem_filter.mp hlT.1
      have hkold : k∈fiber D a m ell plane E c (k (3:Fin 4)) mu
          (rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd) b :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨hkS.1,rfl⟩,hkS.2⟩
      have hlold : l∈fiber D a m ell plane E c (k (3:Fin 4)) mu
          (rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd) b :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨hlS.1,ht.symm⟩,hlS.2⟩
      exact tangent_label_injOn D a m ell plane E c (k (3:Fin 4)) P hP hell hell4 hd mu hmu hmesh b
        hkold hlold (hkT.2.trans hlT.2.symm)
    have hc : T.card ≤ 2^(phaseDepth m-m) := by
      calc
        _ = (T.image (fun k => k (3:Fin 4))).card := (card_image_of_injOn hinj).symm
        _ ≤ (V.image (fun k => k (3:Fin 4))).card := card_le_card (image_subset_image hTV)
        _ ≤ _ := mixed_height_count D a m ell hm plane E c
    simpa only [image_id] using (show (T.card:ℝ) ≤ ((2^(phaseDepth m-m):ℕ):ℝ) by exact_mod_cast hc)
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
    S id g (((2^(phaseDepth m-m):ℕ):ℝ)) hcap
  simpa only [S,g,wholeX,image_id] using hh

/-- A single actual all-height quotient fiber supplies dense occupied X
coordinates, paying the computed quotient count and raw-height multiplicity. -/
theorem exists_dense_wholeX {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (hV : (mixedVertices D a m (phaseDepth m) plane ell E c).Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8) :
    let f := fun k => label mu (rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd k)
    ∃b∈(mixedVertices D a m (phaseDepth m) plane ell E c).image f,
      (wholeFiber D a m ell plane E c P hP hell hell4 hd mu b).Nonempty ∧
      (wholeX D a m ell plane E c P hP hell hell4 hd mu b).Nonempty ∧
      (mixedVertices D a m (phaseDepth m) plane ell E c).card ≤
        (((mixedVertices D a m (phaseDepth m) plane ell E c).image f).card:ℝ)*
          (((2^(phaseDepth m-m):ℕ):ℝ))*(wholeX D a m ell plane E c P hP hell hell4 hd mu b).card := by
  intro f
  let V := mixedVertices D a m (phaseDepth m) plane ell E c
  obtain ⟨k,hk,hF,hcard⟩ := exists_dense_fiber V hV f ((V.image f).card:ℝ) le_rfl
  refine ⟨f k,mem_image_of_mem f hk,hF,hF.image _,?_⟩
  have hX := wholeFiber_card_le_X D a m ell hm plane E c P hP hell hell4 hd mu hmu hmesh (f k)
  calc
    _ ≤ ((V.image f).card:ℝ)*(wholeFiber D a m ell plane E c P hP hell hell4 hd mu (f k)).card := hcard
    _ ≤ ((V.image f).card:ℝ)*
        ((((2^(phaseDepth m-m):ℕ):ℝ))*(wholeX D a m ell plane E c P hP hell hell4 hd mu (f k)).card) :=
      mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg _)
    _ = _ := by ring

end NativeGrainHeightProjectionFibers
