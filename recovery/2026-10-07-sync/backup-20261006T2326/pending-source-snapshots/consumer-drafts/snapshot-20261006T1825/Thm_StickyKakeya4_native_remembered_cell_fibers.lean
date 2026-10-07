/- UNVERIFIED fixed capacity of the ACTUAL final local-cell image over one
original coarse XY key. Original occurrences remain the witnesses. -/
import Theorems.Thm_StickyKakeya4_native_remembered_cell_halo
import Theorems.Thm_StickyKakeya4_native_joint_spatial_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeRememberedCellFibers
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridLinear
open NativeReferenceXYGridMetric NativeHorizontalGrainSlice NativeLocalParentSource
open NativeRememberedCellHalo NativeRememberedSourceMaps NativeJointSpatialGeometry
open NativeLocalCellCoherence NativeOriginalCellChartGeometry NativeAnisotropicShortRowGeometry
open CanonicalConfiguredE4Bridge NativeMatchedShadowConfiguredGeometry
open scoped Matrix.Norms.Elementwise

/-- Equal coarse XY keys include an exact common old height. At raw mesh
512d, the actual configured points are within16d, with all rounding paid. -/
theorem configured_gap_of_coarse_XY {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t,‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 512 ≤ Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    {d : ℝ} (hdpos : 0 < d) (hmu : mu m ≤ d) (hbaseD : mu m*(R0:ℝ) ≤ 64*d)
    (hmesh : (Rd:ℝ)*mu m=512*d) (k l : Index)
    (hxy : coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F k)=
      coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F l)) :
    dist (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 k)
      (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 l) ≤ 16*d := by
  have hOld := coarse_xy_old_dist h m 2 hm p i hi P hP (by norm_num) (by norm_num) hd F hF Rd hRd k l hxy
  rw [hmesh] at hOld
  have hraw := (raw_dist_le_old h m hm p i hi k l).trans (add_le_add_right hOld (256*mu m))
  have hFe : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hF t) i j
  let O := NativePackedFrameIsometry.frame .oneTwo P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
  let x := O ((1/512:ℝ) • rawPoint D a m p k)
  let y := O ((1/512:ℝ) • rawPoint D a m p l)
  have hk := NativeActualConfiguredPoint.point_distance D a m hm p .oneTwo P hP hd F Fcfg hFe hCfg R0 hR0 k hbase
  have hl := NativeActualConfiguredPoint.point_distance D a m hm p .oneTwo P hP hd F Fcfg hFe hCfg R0 hR0 l hbase
  have hs : dist x y=(1/512:ℝ)*dist (rawPoint D a m p k) (rawPoint D a m p l) := by
    simp only [x,y,O.dist_map,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs]
    norm_num
  have h1 := dist_triangle (cfg k) x (cfg l)
  have h2 := dist_triangle x y (cfg l)
  change dist (cfg k) x ≤ _ at hk
  change dist (cfg l) y ≤ _ at hl
  rw [dist_comm y (cfg l),hs] at h2
  nlinarith only [h1,h2,hk,hl,hraw,hmu,hbaseD,hdpos]

/-- The literal integer cell centers have a fixed finite halo whenever
their actual Euclidean diameter is at most24sigma. No direction count occurs. -/
lemma local_cell_image_cap {X : Type*} (A : Finset X) (cell : X → Index)
    {sigma : ℝ} (hs : 0 < sigma)
    (H : ∀x∈A,∀y∈A,
      dist (cellCenter (sigma/2) (cell x)) (cellCenter (sigma/2) (cell y)) ≤ 24*sigma) :
    (A.image cell).card ≤ 129^4 := by
  by_cases hA : A.Nonempty
  · obtain ⟨y,hy⟩ := hA
    have hsub : A.image cell⊆columnHalo 64 64 (cell y) := by
      intro k hk
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
      apply Fintype.mem_piFinset.mpr
      intro j
      simp only [ite_self]
      have hh : |cellCenter (sigma/2) (cell x) j-cellCenter (sigma/2) (cell y) j| ≤ 24*sigma := by
        exact (show _ ≤ dist (cellCenter (sigma/2) (cell x)) (cellCenter (sigma/2) (cell y)) by
          simpa only [Real.dist_eq] using PiLp.dist_apply_le _ _ j).trans (H x hx y hy)
      have he : cellCenter (sigma/2) (cell x) j-cellCenter (sigma/2) (cell y) j =
          (sigma/2)*(((cell x j:ℤ):ℝ)-((cell y j:ℤ):ℝ)) := by dsimp [cellCenter]; ring
      rw [he,abs_mul,abs_of_pos (half_pos hs)] at hh
      have hi : |((cell x j:ℤ):ℝ)-((cell y j:ℤ):ℝ)| ≤ 64 := by
        nlinarith only [hh,hs]
      have hz : |cell x j-cell y j| ≤ (64:ℤ) := by exact_mod_cast hi
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)
  · simp only [not_nonempty_iff_eq_empty.mp hA,image_empty,card_empty,Nat.zero_le]

/-- Combine the actual4sigma occurrence halo with a16d original-point
cluster. The common parent physical map contributes precisely N/64. -/
theorem local_centers_cluster {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (N : ℕ) (hN : 0 < N) (p : Parent)
    (i : Fin n) (hi : parentLabel C 0 N i=p)
    (O : E4 ≃ₗᵢ[ℝ] E4) (x y : E4) (j k : Index)
    (hx : dist (cellCenter ((N:ℝ)*C.thickness/128) j)
      (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm x)) ≤ 4*((N:ℝ)*C.thickness/64))
    (hy : dist (cellCenter ((N:ℝ)*C.thickness/128) k)
      (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm y)) ≤ 4*((N:ℝ)*C.thickness/64))
    (hxy : dist x y ≤ 16*C.thickness) :
    dist (cellCenter ((N:ℝ)*C.thickness/128) j)
      (cellCenter ((N:ℝ)*C.thickness/128) k) ≤ 24*((N:ℝ)*C.thickness/64) := by
  have hm := physical_map_dist hC 0 N hN p i hi (O.symm x) (O.symm y)
  rw [O.symm.dist_map] at hm
  have hm' := mul_le_mul_of_nonneg_left hxy (show (0:ℝ) ≤ N by positivity)
  have h1 := dist_triangle (cellCenter ((N:ℝ)*C.thickness/128) j)
    (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm x))
    (cellCenter ((N:ℝ)*C.thickness/128) k)
  have h2 := dist_triangle (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm x))
    (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm y))
    (cellCenter ((N:ℝ)*C.thickness/128) k)
  have hy' : dist (NativeLocalParentPhysicalMap.physicalMap C 0 N p (O.symm y))
      (cellCenter ((N:ℝ)*C.thickness/128) k) ≤ 4*((N:ℝ)*C.thickness/64) := by
    simpa only [dist_comm] using hy
  nlinarith only [hx,hy',hxy,hm,hm',h1,h2]

/-- Every fiber over an actual original coarse XY key has at most129^4
final cell labels. Both halo inputs are derived from its original occurrences. -/
theorem actual_fiber_card {n : ℕ} {D : FiniteScaleSource n} {eta etaC a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Q.card → Finset Index) (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (A : Finset (Fin n × Index)) (hA : A⊆NativeCubicalIncidenceCounts.incidences original)
    (hparent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t,‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 512 ≤ Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ))
    (hmesh : (Rd:ℝ)*mu m=512*C.thickness)
    (c : ℕ) (pA : Parent)
    (V : Finset ((Fin Q.card × Index) × (Fin n × Index)))
    (hV : V⊆occurrences h backbone a m b p hp Q cells A)
    (hcurrent : ∀z∈V,parentLabel C 0 (2^c) z.1.1=pA)
    (q : NativeReferenceXYGridMaps.XY 2) :
    (((V.filter (fun z => coarseXY 2 Rd
      (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2.2)=q)).image
      (fun z => localCellLabel C 0 (2^c) pA z.1)).card) ≤ 129^4 := by
  let U := V.filter (fun z => coarseXY 2 Rd
    (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2.2)=q)
  have hFe : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hF t) i j
  have hBaseD : mu m*(R0:ℝ) ≤ 64*C.thickness := by rw [hthickness]; convert hmatch using 1; ring
  have hmu : mu m ≤ C.thickness := by
    have hr : rho m=64*mu m := by unfold rho mu; ring
    rw [hr] at hbase
    linarith only [hbase,hBaseD]
  let O := NativePackedFrameIsometry.frame .oneTwo P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
  have halo (z : (Fin Q.card × Index) × (Fin n × Index)) (hz : z∈U) :
      dist (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128) (localCellLabel C 0 (2^c) pA z.1))
        (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg z.2.2))) ≤
          4*(((2^c:ℕ):ℝ)*C.thickness/64) :=
    occurrence_center_near h original horiginal ha backbone m b hm p hp hNscale hRelScale Q C hC
      cells hcells haC hthickness A hA hparent .oneTwo P hP hd F Fcfg hFe hCfg R0 hR0 hbase hmatch
      c pA z (hV (mem_filter.mp hz).1) (hcurrent z (mem_filter.mp hz).1)
  have hs : 0 < ((2^c:ℕ):ℝ)*C.thickness/64 := by have hc := hC.1.2.1; positivity
  apply local_cell_image_cap U (fun z => localCellLabel C 0 (2^c) pA z.1) hs
  intro z hz w hw
  have hzA := ((mem_occurrences h backbone a m b p hp Q cells A z).mp (hV (mem_filter.mp hz).1)).2.1
  have hOldParent := (mem_parentLabels D backbone a (2^m) p _).mp (hparent z.2 hzA)
  have hGap := configured_gap_of_coarse_XY h m hm p z.2.1 hOldParent.2 P hP hd F Fcfg hF hCfg
    R0 Rd hR0 hRd hbase hC.1.2.1 hmu hBaseD hmesh z.2.2 w.2.2
    ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm)
  have hh := local_centers_cluster hC (2^c) (by positivity) pA z.1.1
    (hcurrent z (mem_filter.mp hz).1) O (cfg z.2.2) (cfg w.2.2)
    (localCellLabel C 0 (2^c) pA z.1) (localCellLabel C 0 (2^c) pA w.1) (halo z hz) (halo w hw) hGap
  have he : (((2^c:ℕ):ℝ)*C.thickness/64)/2=((2^c:ℕ):ℝ)*C.thickness/128 := by ring
  simpa only [he] using hh


end NativeRememberedCellFibers
