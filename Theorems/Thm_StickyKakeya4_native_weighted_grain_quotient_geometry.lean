import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeWeightedGrainQuotientGeometry
open Classical Finset StickyKakeya4 NativeWeightedGrainQuotientSelection
open NativeGrainQuotientBins NativeGrainQuotientFibers NativeGrainQuotientImage
open NativeGrainHeightProjectionFibers NativeHorizontalGrainSlice NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeSpatialAngularGeometry NativeSquaredGrainQueries
open NativeParentGrainIncidenceCleanup RichDirectionalLayers

lemma grain_mixed_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) :
    grain H (mixedLabel D a m plane ell) c=mixedFiber D a m plane ell H c := by
  ext z
  simp only [grain,mixedFiber,classFiber,mem_filter]

/-- Each original incidence receives its actual parent/node quotient label.
Its raw point and time are unchanged. -/
def quotientLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (z : Fin n × Index) : Fin (4-ell) → ℤ :=
  label mu (rawCoordinates D a m ell (parentLabel D a (2^m) z.1) P
    (sliceSpace (plane (spatialLabel D (2^m) z.2))) hP hell hell4 hd
      (spatialLabel D (2^(phaseDepth m)) z.2))

/-- The winning quotient label is chosen by ORIGINAL INCIDENCE mass. -/
def pick {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (c : Parent × (Index × Index)) : Fin (4-ell) → ℤ :=
  chosen (fun _ => 1) H (mixedLabel D a m plane ell)
    (quotientLabel D a m ell plane P hP hell hell4 hd mu) c

def retained {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ) : Finset (Fin n × Index) :=
  selected (fun _ => 1) H (mixedLabel D a m plane ell)
    (quotientLabel D a m ell plane P hP hell hell4 hd mu)

lemma retained_subset {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ) :
    retained D a m ell plane H P hP hell hell4 hd mu⊆H := selected_subset _ _ _ _

lemma quotientLabel_on_mixed {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (c : Parent × (Index × Index)) (z : Fin n × Index) (hz : z∈mixedFiber D a m plane ell H c) :
    quotientLabel D a m ell plane P hP hell hell4 hd mu z=
      label mu (rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd
        (spatialLabel D (2^(phaseDepth m)) z.2)) := by
  simp only [mixedFiber,classFiber,mem_filter] at hz
  have hp := congrArg Prod.fst hz.2
  have hn := congrArg (fun c : Parent × (Index × Index) => c.2.1) hz.2
  change parentLabel D a (2^m) z.1=c.1 at hp
  change spatialLabel D (2^m) z.2=c.2.1 at hn
  simp only [quotientLabel,hp,hn]

lemma quotient_image_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (c : Parent × (Index × Index)) :
    (mixedFiber D a m plane ell H c).image (quotientLabel D a m ell plane P hP hell hell4 hd mu)=
      (mixedVertices D a m (phaseDepth m) plane ell H c).image
        (fun k => label mu (rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd k)) := by
  rw [mixedVertices,image_image]
  exact image_congr (fun z hz => quotientLabel_on_mixed D a m ell plane H P hP hell hell4 hd mu c z hz)

/-- Exact edge saturation: no occurrence or height in the winning class is
removed, and no unselected quotient class is included. -/
lemma retained_mixed_fiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (c : Parent × (Index × Index)) :
    mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c=
      (mixedFiber D a m plane ell H c).filter
        (fun z => quotientLabel D a m ell plane P hP hell hell4 hd mu z=pick D a m ell plane H P hP hell hell4 hd mu c) := by
  rw [←grain_mixed_eq D a m ell plane (retained D a m ell plane H P hP hell hell4 hd mu) c,
    ←grain_mixed_eq D a m ell plane H c]
  exact selected_grain (fun _ => 1) H (mixedLabel D a m plane ell)
    (quotientLabel D a m ell plane P hP hell hell4 hd mu) c

/-- The retained raw vertices are EXACTLY the whole original quotient
fiber, including every original raw height represented there. -/
lemma retained_mixed_vertices {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (c : Parent × (Index × Index)) :
    mixedVertices D a m (phaseDepth m) plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c=
      wholeFiber D a m ell plane H c P hP hell hell4 hd mu (pick D a m ell plane H P hP hell hell4 hd mu c) := by
  rw [mixedVertices,retained_mixed_fiber]
  ext k
  simp only [wholeFiber,mem_image,mem_filter,mixedVertices]
  constructor
  · rintro ⟨z,⟨hz,hq⟩,rfl⟩
    exact ⟨⟨z,hz,rfl⟩,by rwa [quotientLabel_on_mixed D a m ell plane H P hP hell hell4 hd mu c z hz] at hq⟩
  · rintro ⟨⟨z,hz,rfl⟩,hq⟩
    refine ⟨z,⟨hz,?_⟩,rfl⟩
    rwa [quotientLabel_on_mixed D a m ell plane H P hP hell hell4 hd mu c z hz]

/-- The raw-height preimage cost applies to the incidence-weighted winning
class; the selection criterion does not affect this geometric upper bound. -/
theorem retained_vertices_le_X {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (mu : ℝ) (hmu : 0 < mu) (hmesh : mu ≤ physicalMesh m (phaseDepth m)/8)
    (c : Parent × (Index × Index)) :
    (mixedVertices D a m (phaseDepth m) plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c).card ≤
      (((2^(phaseDepth m-m):ℕ):ℝ))*
        (wholeX D a m ell plane H c P hP hell hell4 hd mu (pick D a m ell plane H P hP hell hell4 hd mu c)).card := by
  rw [retained_mixed_vertices]
  exact wholeFiber_card_le_X D a m ell hm plane H c P hP hell hell4 hd mu hmu hmesh _

end NativeWeightedGrainQuotientGeometry
