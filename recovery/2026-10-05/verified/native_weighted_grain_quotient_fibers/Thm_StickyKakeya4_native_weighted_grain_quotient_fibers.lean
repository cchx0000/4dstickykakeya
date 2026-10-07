import Theorems.Thm_StickyKakeya4_native_weighted_grain_quotient_source

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeWeightedGrainQuotientFibers
open Classical Finset StickyKakeya4 NativeWeightedGrainQuotientGeometry
open NativeGrainQuotientBins NativeGrainQuotientImage NativeGrainHeightProjectionFibers
open NativeHorizontalGrainSlice NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeSquaredGrainQueries NativeParentGrainIncidenceCleanup NativeSpatialAngularGeometry RichDirectionalLayers

/-- Global actual coarse-height/quotient key of an unchanged original edge. -/
def key {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (z : Fin n × Index) : ℤ × (Fin (4-ell) → ℤ) :=
  (spatialLabel D (2^m) z.2 (3:Fin 4),quotientLabel D a m ell plane P hP hell hell4 hd mu z)

/-- Actual tangent bin of the original physical raw vertex, in the fixed chart. -/
def edgeX {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (P : Submodule ℝ E4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (z : Fin n × Index) : Fin (ell-1) → ℤ :=
  label mu (rawTangent D a m ell (parentLabel D a (2^m) z.1) P hd
    (spatialLabel D (2^(phaseDepth m)) z.2))

/-- All actual X bins of a retained global coarse-height/quotient fiber. -/
def fullX {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (S : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (b : ℤ × (Fin (4-ell) → ℤ)) : Finset (Fin (ell-1) → ℤ) :=
  (S.filter (fun z => key D a m ell plane P hP hell hell4 hd mu z=b)).image (edgeX D a m ell P hd mu)

lemma mixed_edgeX_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (c : Parent × (Index × Index)) :
    (mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c).image
      (edgeX D a m ell P hd mu)=
      wholeX D a m ell plane H c P hP hell hell4 hd mu (pick D a m ell plane H P hP hell hell4 hd mu c) := by
  let S := retained D a m ell plane H P hP hell hell4 hd mu
  have he : (mixedFiber D a m plane ell S c).image (edgeX D a m ell P hd mu)=
      (mixedVertices D a m (phaseDepth m) plane ell S c).image
        (fun k => label mu (rawTangent D a m ell c.1 P hd k)) := by
    rw [mixedVertices,image_image]
    apply image_congr
    intro z hz
    rw [←grain_mixed_eq D a m ell plane S c] at hz
    have hp : parentLabel D a (2^m) z.1=c.1 := congrArg Prod.fst (mem_filter.mp hz).2
    simp only [edgeX,hp,Function.comp_apply]
  change _=_ at he
  rw [he,retained_mixed_vertices]
  rfl

/-- A whole retained mixed grain lies in one actual global key. -/
lemma mixed_key_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (c : Parent × (Index × Index)) (x y : Fin n × Index)
    (hx : x∈mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c)
    (hy : y∈mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu) c) :
    key D a m ell plane P hP hell hell4 hd mu x=key D a m ell plane P hP hell hell4 hd mu y := by
  rw [retained_mixed_fiber] at hx hy
  obtain ⟨hx,hqx⟩ := mem_filter.mp hx
  obtain ⟨hy,hqy⟩ := mem_filter.mp hy
  simp only [mixedFiber,classFiber,mem_filter] at hx hy
  have hn := congrArg (fun c : Parent × (Index × Index) => c.2.1 (3:Fin 4)) (hx.2.trans hy.2.symm)
  exact Prod.ext hn (hqx.trans hqy.symm)

/-- Density in each incidence-weighted mixed grain also holds in its full
retained coarse-height/quotient fiber, which may combine several grains. -/
theorem wholeX_subset_fullX {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (H : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1) (mu : ℝ)
    (x : Fin n × Index) (hx : x∈retained D a m ell plane H P hP hell hell4 hd mu) :
    wholeX D a m ell plane H (mixedLabel D a m plane ell x) P hP hell hell4 hd mu
      (pick D a m ell plane H P hP hell hell4 hd mu (mixedLabel D a m plane ell x)) ⊆
      fullX D a m ell plane (retained D a m ell plane H P hP hell hell4 hd mu) P hP hell hell4 hd mu
        (key D a m ell plane P hP hell hell4 hd mu x) := by
  rw [←mixed_edgeX_image]
  apply image_subset_image
  intro y hy
  have hxF : x∈mixedFiber D a m plane ell (retained D a m ell plane H P hP hell hell4 hd mu)
      (mixedLabel D a m plane ell x) := by simp only [mixedFiber,classFiber,mem_filter]; exact ⟨hx,True.intro⟩
  have hyS := hy
  simp only [mixedFiber,classFiber,mem_filter] at hyS
  exact mem_filter.mpr ⟨hyS.1,mixed_key_eq D a m ell plane H P hP hell hell4 hd mu _ y x hy hxF⟩

end NativeWeightedGrainQuotientFibers
