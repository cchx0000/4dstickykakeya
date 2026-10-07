/- UNVERIFIED geometric halo for literal remembered-source occurrences. -/
import Theorems.Thm_StickyKakeya4_native_remembered_source_maps
import Theorems.Thm_StickyKakeya4_native_matched_shadow_configured_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedCellHalo
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeLocalParentSource NativeLocalParentCells
open NativeLocalParentPhysicalMap NativeLocalCellCoherence NativeRelativeCoarseReadback
open NativeMatchedShadowConfiguredGeometry NativeRememberedSourceMaps
open NativeReferenceXYGridPoints NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge

/-- The actual parent map has its explicit N/64 Lipschitz bound. -/
theorem physical_map_dist {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (a : ℝ) (N : ℕ) (hN : 0 < N)
    (p : Parent) (i : Fin n) (hi : parentLabel C a N i=p) (x y : E4) :
    dist (physicalMap C a N p x) (physicalMap C a N p y) ≤ (N:ℝ)*dist x y/64 := by
  have hh := baseMap_dist_le N hN ((shift C a:ℝ)*mesh C) p
    (parent_slope_bound hC N hN p i hi) x y
  unfold physicalMap
  rw [NativeContractedUnitParent.contract_dist]
  have hdiv := div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 32)
  convert hdiv using 1 <;> ring

/-- Literal local-cell rounding costs at most2sigma in E4. It is derived
from the original native shading membership and the actual front map. -/
theorem local_center_near_map {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (ha : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (i : Fin n) (k : Index) (hk : k∈cells i) :
    dist (cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)))
      (physicalMap C 0 N p (cellCenter (mesh C) k)) ≤ 2*((N:ℝ)*C.thickness/64) := by
  have he : 0 < (N:ℝ)*C.thickness/128 := by have hd := hC.1.2.1; positivity
  apply (distance_of_coordinates _ _ ((N:ℝ)*C.thickness/64) (by positivity) ?_)
  intro j
  have hr := cell_center_coordinate_error he (frontPoint C 0 N p i k) j
  have hf := frontPoint_near_physicalCell hC cells hcells ha N p i k hk j
  have htri := abs_sub_le
    (cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) j)
    (frontPoint C 0 N p i k j) (physicalMap C 0 N p (cellCenter (mesh C) k) j)
  change |frontPoint C 0 N p i k j-
    cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) j| ≤ _ at hr
  rw [abs_sub_comm] at hr
  linarith only [hr,hf,htri]

/-- A genuine original occurrence supplies the2d intermediate shadow error.
The final local cell is consequently within4sigma of the common physical
image of its own original configured point. No halo certificate is assumed. -/
theorem occurrence_center_near {n : ℕ} {D : FiniteScaleSource n} {eta etaC a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Q.card → Finset Index)
    (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (A : Finset (Fin n × Index)) (hA : A⊆NativeCubicalIncidenceCounts.incidences original)
    (hparent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ))
    (c : ℕ) (pA : Parent)
    (z : (Fin Q.card × Index) × (Fin n × Index))
    (hz : z∈occurrences h backbone a m b p hp Q cells A)
    (hcurrent : parentLabel C 0 (2^c) z.1.1=pA) :
    let O := NativePackedFrameIsometry.frame s P hP hd
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2.2
    dist (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128)
        (localCellLabel C 0 (2^c) pA z.1))
      (physicalMap C 0 (2^c) pA (O.symm cfg)) ≤ 4*(((2^c:ℕ):ℝ)*C.thickness/64) := by
  intro O cfg
  obtain ⟨hzCells,hzA,_hphase,hshadow⟩ := (mem_occurrences h backbone a m b p hp Q cells A z).mp hz
  have horig : z.2.2∈original z.2.1 :=
    (NativeCubicalIncidenceCounts.mem_incidences original _ _).mp (hA hzA)
  have hi := (mem_parentLabels D backbone a (2^m) p _).mp (hparent z.2 hzA)
  let rep := originalRepresentative h backbone a m p hp (2^b)
    (NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^b) z.2.1)
  have hr := originalRepresentative_label h backbone a m p hp (2^b) z.2.1 (hparent z.2 hzA)
  have hnear := point_shadow_center_distance h original horiginal ha m (2^b) hm (by positivity)
    hNscale hRelScale p z.2.1 rep z.2.2 horig hi.2 hr s P hP hd F Fcfg hF hCfg
    R0 hR0 hbase hmatch
  have hcenter : dist (cellCenter (mesh C) z.1.2) (O.symm cfg) ≤ 2*C.thickness := by
    rw [←O.dist_map,LinearIsometryEquiv.apply_symm_apply,dist_comm]
    change dist cfg (O (cellCenter (C.thickness/2) z.1.2)) ≤ _
    rw [hthickness,hshadow]
    have he : (64/((2^b:ℕ):ℝ))/2=32/((2^b:ℕ):ℝ) := by ring
    rw [he]
    exact hnear
  have hmap := physical_map_dist hC 0 (2^c) (by positivity) pA z.1.1 hcurrent
    (cellCenter (mesh C) z.1.2) (O.symm cfg)
  have hround := local_center_near_map hC cells hcells haC (2^c) (by positivity) pA z.1.1 z.1.2
    ((NativeCubicalIncidenceCounts.mem_incidences cells _ _).mp hzCells)
  have htri := dist_triangle
    (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128) (localCellLabel C 0 (2^c) pA z.1))
    (physicalMap C 0 (2^c) pA (cellCenter (mesh C) z.1.2))
    (physicalMap C 0 (2^c) pA (O.symm cfg))
  have hb := mul_le_mul_of_nonneg_left hcenter (show (0:ℝ) ≤ ((2^c:ℕ):ℝ) by positivity)
  nlinarith only [hmap,hround,htri,hb]

end NativeRememberedCellHalo
