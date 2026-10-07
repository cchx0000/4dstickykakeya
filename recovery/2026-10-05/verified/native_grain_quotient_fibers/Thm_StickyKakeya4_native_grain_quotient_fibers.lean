import Theorems.Thm_StickyKakeya4_native_grain_quotient_bins
import Theorems.Thm_StickyKakeya4_native_compatible_angular_candidates

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeGrainQuotientFibers
open Classical Finset StickyKakeya4 NativeGrainQuotientGeometry NativeGrainQuotientBins
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeSquaredGrainQueries
open NativeActualProjectedGrainCount NativeOriginalPacketReference NativeParentGrainIncidenceCleanup
open NativeSpatialAngularGeometry NativeOriginalCellChartGeometry NativeHorizontalGrainSlice
open NativeProjectorCellChart NativeCompatibleAngularCandidates RichDirectionalLayers
open scoped BigOperators

/-- The exact occupied-height bound is obtained from raw dyadic ancestors. -/
theorem mixed_height_count {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index)) :
    ((mixedVertices D a m (phaseDepth m) plane ell E c).image (fun k => k (3:Fin 4))).card ≤
      2^(phaseDepth m-m) := by
  let N : ℕ := 2^(phaseDepth m-m)
  let u : ℤ := c.2.1 (3:Fin 4)
  have hN : (0:ℤ)<N := by dsimp [N]; positivity
  have hsub : (mixedVertices D a m (phaseDepth m) plane ell E c).image (fun k => k (3:Fin 4))⊆
      Ico (u*(N:ℤ)) (u*(N:ℤ)+N) := by
    intro t ht
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ht
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    have hzc := hz
    simp only [mixedFiber,classFiber,mem_filter] at hzc
    have hnode : spatialLabel D (2^m) z.2=c.2.1 :=
      congrArg (fun z : Parent × (Index × Index) => z.2.1) hzc.2
    have hh := congrFun (spatialAncestor_label D hm z.2) (3:Fin 4)
    rw [hnode] at hh
    change spatialLabel D (2^(phaseDepth m)) z.2 (3:Fin 4)/(N:ℤ)=u at hh
    exact mem_Ico.mpr ((Int.ediv_eq_iff_of_pos hN).mp hh)
  calc
    _ ≤ (Ico (u*(N:ℤ)) (u*(N:ℤ)+N)).card := card_le_card hsub
    _ = N := by simp [Int.card_Ico]

/-- The actual fiber keeps original, distinct raw vertices. -/
def fiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (plane : Index → Submodule ℝ E4) (E : Finset (Fin n × Index))
    (c : Parent × (Index × Index)) (t : ℤ) (mu : ℝ)
    (f : Index → EuclideanSpace ℝ (Fin (4-ell))) (b : Fin (4-ell) → ℤ) : Finset Index :=
  (heightFiber D a m ell plane E c t).filter (fun k => label mu (f k)=b)

/-- Select one genuine time and quotient fiber, paying BOTH the exact raw
height count and the geometric quotient-bin count. -/
theorem exists_mixed_dense_fiber {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : m ≤ phaseDepth m) (plane : Index → Submodule ℝ E4)
    (E : Finset (Fin n × Index)) (c : Parent × (Index × Index))
    (hV : (mixedVertices D a m (phaseDepth m) plane ell E c).Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (hPQ : Module.finrank ℝ P=Module.finrank ℝ (sliceSpace (plane c.2.1)))
    (hc : cell P=cell (sliceSpace (plane c.2.1)))
    (v : E4) (hvR : v∈plane c.2.1) (hv : v (3:Fin 4)=1) (hvn : ‖v‖ ≤ 2)
    (mu : ℝ) (hmu : 0 < mu) :
    let f := rawCoordinates D a m ell c.1 P (sliceSpace (plane c.2.1)) hP hell hell4 hd
    ∃t : ℤ,∃b : Fin (4-ell) → ℤ,
      (fiber D a m ell plane E c t mu f b).Nonempty ∧
      (mixedVertices D a m (phaseDepth m) plane ell E c).card ≤
        (((2^(phaseDepth m-m):ℕ):ℝ)*(2*diameter m ell/mu+2)^(4-ell))*
          (fiber D a m ell plane E c t mu f b).card := by
  intro f
  let V := mixedVertices D a m (phaseDepth m) plane ell E c
  let T : ℝ := (2^(phaseDepth m-m):ℕ)
  let B : ℝ := (2*diameter m ell/mu+2)^(4-ell)
  obtain ⟨k,_hk,hSn,hret⟩ := exists_dense_fiber V hV (fun k => k (3:Fin 4)) T
    (by dsimp only [V,T]; exact_mod_cast mixed_height_count D a m ell hm plane E c)
  change (heightFiber D a m ell plane E c (k (3:Fin 4))).Nonempty at hSn
  change (V.card:ℝ) ≤ T*(heightFiber D a m ell plane E c (k (3:Fin 4))).card at hret
  obtain ⟨l,_hl,hFn,hdense⟩ := exists_dense_fiber
    (heightFiber D a m ell plane E c (k (3:Fin 4))) hSn (fun j => label mu (f j)) B
    (mixed_occupied_quotient_card D a m ell plane E c (k (3:Fin 4)) P hP hell hell4 hd hPQ hc v hvR hv hvn mu hmu)
  refine ⟨k (3:Fin 4),label mu (f l),hFn,?_⟩
  calc
    _ ≤ T*(heightFiber D a m ell plane E c (k (3:Fin 4))).card := hret
    _ ≤ T*(B*(fiber D a m ell plane E c (k (3:Fin 4)) mu f (label mu (f l))).card) :=
      mul_le_mul_of_nonneg_left hdense (by dsimp [T]; positivity)
    _ = _ := by ring

/-- Explicit physical lattice spacing after the actual horizontal parent map. -/
def physicalMesh (m f : ℕ) : ℝ := (((2^m:ℕ):ℝ)/512)*(64/((2^f:ℕ):ℝ))

lemma physicalMesh_pos (m f : ℕ) : 0 < physicalMesh m f := by unfold physicalMesh; positivity

/-- Exact thickness-to-resolution ratio; the physical parent factor cancels
but the terminal-to-grain mesh ratio remains. -/
lemma diameter_div_physicalMesh (m ell f : ℕ) :
    diameter m ell/physicalMesh m f=
      (15/2:ℝ)*(4:ℝ)^ell*258*(((2^f:ℕ):ℝ)/((2^(phaseDepth m):ℕ):ℝ)) := by
  have hm : (((2^m:ℕ):ℝ))≠0 := by positivity
  have hf : (((2^f:ℕ):ℝ))≠0 := by positivity
  have hg : (((2^(phaseDepth m):ℕ):ℝ))≠0 := by positivity
  unfold diameter physicalMesh grainWidth NativeApproximateFiberIteration.radius
  field_simp

/-- The terminal phase mesh incurs a constant quotient loss, while using
another terminal depth keeps its precise scale ratio. -/
lemma phase_diameter_div_physicalMesh (m ell : ℕ) :
    diameter m ell/physicalMesh m (phaseDepth m)=(15/2:ℝ)*(4:ℝ)^ell*258 := by
  rw [diameter_div_physicalMesh,div_self (by positivity : (((2^(phaseDepth m):ℕ):ℝ))≠0),mul_one]

/-- A source density estimate is preserved with its q-dependent factor
unchanged; only the explicitly paid height and quotient losses are added. -/
lemma density_transfer {L C H B V X : ℝ} (hC : 0 ≤ C)
    (hsource : L < C*V) (hretain : V ≤ H*B*X) : L < C*H*B*X := by
  calc
    _ < C*V := hsource
    _ ≤ C*(H*B*X) := mul_le_mul_of_nonneg_left hretain hC
    _ = _ := by ring

end NativeGrainQuotientFibers
