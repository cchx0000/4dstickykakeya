import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_fibers
import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeWeightedGrainQuotientHereditary
open Classical Finset StickyKakeya4 NativeWeightedGrainQuotientGeometry NativeWeightedGrainQuotientFibers
open NativeGrainQuotientBins NativeGrainQuotientFibers NativeGrainQuotientImage
open NativeGrainHeightProjectionFibers NativeHorizontalGrainSlice NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup
open NativeSpatialAngularGeometry RichDirectionalLayers NativeSourceParentGrainCleanup

/-- The X-bin preimage bound is hereditary in raw points. No later subset
is incorrectly identified with a saturated original quotient class. -/
theorem subset_wholeFiber_card_le_X {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (b : Fin (4-ell) → ℤ) (W : Finset Index)
    (hW : W⊆wholeFiber D a m ell plane E c P hP hell hell4 hd mu b) :
    (W.card:ℝ) ≤ (((2^(phaseDepth m-m):ℕ):ℝ))*
      (W.image (fun k => label mu (rawTangent D a m ell c.1 P hd k))).card := by
  let V := mixedVertices D a m (phaseDepth m) plane ell E c
  let g := fun k => label mu (rawTangent D a m ell c.1 P hd k)
  have hcap : ∀j∈W.image g,(((W.filter (fun k => g k=j)).image id).card:ℝ) ≤
      (((2^(phaseDepth m-m):ℕ):ℝ)) := by
    intro j _hj
    let T := W.filter (fun k => g k=j)
    have hTV : T⊆V := (filter_subset _ _).trans (hW.trans (filter_subset _ _))
    have hinj : Set.InjOn (fun k : Index => k (3:Fin 4)) (↑T : Set Index) := by
      intro k hk l hl ht
      have hkT := mem_filter.mp hk
      have hlT := mem_filter.mp hl
      have hkS := mem_filter.mp (hW hkT.1)
      have hlS := mem_filter.mp (hW hlT.1)
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
    W id g (((2^(phaseDepth m-m):ℕ):ℝ)) hcap
  simpa only [g,image_id] using hh

lemma edgeX_image_vertices {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (c : Parent × (Index × Index)) :
    (mixedFiber D a m plane ell H c).image (edgeX D a m ell P hd mu)=
      (mixedVertices D a m (phaseDepth m) plane ell H c).image
        (fun k => label mu (rawTangent D a m ell c.1 P hd k)) := by
  rw [mixedVertices,image_image]
  apply image_congr
  intro z hz
  rw [←grain_mixed_eq D a m ell plane H c] at hz
  have hp : parentLabel D a (2^m) z.1=c.1 := congrArg Prod.fst (mem_filter.mp hz).2
  simp only [edgeX,hp,Function.comp_apply]

/-- The exact geometric multiplicity cap on the SAME later H3 incidences,
using only H3 subset of the original incidence-weighted quotient selection. -/
theorem hereditary_vertices_le_X {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4) (H H3 : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (h3S : H3⊆retained D a m ell plane H P hP hell hell4 hd mu)
    (c : Parent × (Index × Index)) :
    (mixedVertices D a m (phaseDepth m) plane ell H3 c).card ≤
      (((2^(phaseDepth m-m):ℕ):ℝ))*((mixedFiber D a m plane ell H3 c).image (edgeX D a m ell P hd mu)).card := by
  have hsub : mixedVertices D a m (phaseDepth m) plane ell H3 c⊆
      wholeFiber D a m ell plane H c P hP hell hell4 hd mu (pick D a m ell plane H P hP hell hell4 hd mu c) := by
    rw [←retained_mixed_vertices]
    apply image_subset_image
    intro z hz
    simp only [mixedFiber,classFiber,mem_filter] at hz ⊢
    exact ⟨h3S hz.1,hz.2⟩
  have hh := subset_wholeFiber_card_le_X D a m ell hm plane H c P hP hell hell4 hd mu hmu hmesh _ _ hsub
  rw [edgeX_image_vertices]
  exact hh

/-- Hereditary incidence-to-X cross bound. HC is exactly the existing
source_parent_vertex_cap interface on E0; no uniformity of H3 is required. -/
theorem hereditary_X_cross {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E0 H H3 : Finset (Fin n × Index)) (hHE0 : H⊆E0)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (h3S : H3⊆retained D a m ell plane H P hP hell hell4 hd mu)
    (c : Parent × (Index × Index)) (A C : ℝ) (hC : 0 ≤ C)
    (HC : ∀T⊆E0,∀v : Index,(∀z∈T,parentLabel D a (2^m) z.1=c.1) →
      (∀z∈T,spatialLabel D (2^(phaseDepth m)) z.2=v) → A*(T.card:ℝ) ≤ C) :
    A*(mixedFiber D a m plane ell H3 c).card ≤ C*(((2^(phaseDepth m-m):ℕ):ℝ))*
      ((mixedFiber D a m plane ell H3 c).image (edgeX D a m ell P hd mu)).card := by
  have h3E0 := (h3S.trans (retained_subset D a m ell plane H P hP hell hell4 hd mu)).trans hHE0
  have hcross := mixed_vertex_cross D a m (phaseDepth m) plane ell E0 H3 h3E0 c A C HC
  have hvertices := hereditary_vertices_le_X D a m ell hm plane H H3 P hP hell hell4 hd mu hmu hmesh h3S c
  have hh := hcross.trans (mul_le_mul_of_nonneg_left hvertices hC)
  simpa only [mul_assoc] using hh

/-- The same later H3 mixed-grain X image is contained in its actual final
coarse-height/quotient fiber. No original saturated image replaces H3. -/
theorem hereditary_mixed_X_subset_fullX {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H H3 : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (h3S : H3⊆retained D a m ell plane H P hP hell hell4 hd mu)
    (x : Fin n × Index) (hx : x∈H3) :
    (mixedFiber D a m plane ell H3 (mixedLabel D a m plane ell x)).image (edgeX D a m ell P hd mu) ⊆
      fullX D a m ell plane H3 P hP hell hell4 hd mu (key D a m ell plane P hP hell hell4 hd mu x) := by
  apply image_subset_image
  intro y hy
  have hy3 := hy
  simp only [mixedFiber,classFiber,mem_filter] at hy3
  have hxS : x∈mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu)
      (mixedLabel D a m plane ell x) := by
    simp only [mixedFiber,classFiber,mem_filter]
    exact ⟨h3S hx,True.intro⟩
  have hyS : y∈mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu)
      (mixedLabel D a m plane ell x) := by
    simp only [mixedFiber,classFiber,mem_filter]
    exact ⟨h3S hy3.1,hy3.2⟩
  exact mem_filter.mpr ⟨hy3.1,mixed_key_eq D a m ell plane H P hP hell hell4 hd mu _ y x hyS hxS⟩

end NativeWeightedGrainQuotientHereditary
