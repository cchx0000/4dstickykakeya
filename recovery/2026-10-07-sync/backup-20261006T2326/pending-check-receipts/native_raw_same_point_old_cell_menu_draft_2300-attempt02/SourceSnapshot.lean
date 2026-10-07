import Theorems.Thm_StickyKakeya4_native_raw_height_source_adapter
import Theorems.Thm_StickyKakeya4_native_actual_higher_remembered_caller_construction_draft_2100

/- UNVERIFIED actual old coherence-cell menu at one literal remembered
native source point. Only RAW selected original-k3 witnesses enter the
geometry. Translated selection is used solely for the exact source row
readback; its potentially enlarged occurrence set is never substituted.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeRawSamePointOldCellMenuDraft2300
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeRawHeightSourceAdapter NativeRememberedSourceMaps NativeRememberedCellHalo
open NativeLocalCellCoherence NativeTranslatedGrainHeightOverlap NativeReferenceXYGridPoints
open NativeActualConfiguredPoint CanonicalConfiguredE4Bridge NativeHorizontalGrainSlice
open NativePackedHigherCapacityDraft2006 NativeHigherQuotientParentTransport
open NativeRememberedPhaseFootprint NativeRememberedPhaseCover NativeNormalizedCellRelativeMenu

/-- All retained TRUE-original-height witnesses above one actual final
native cell, restricted to the actual final tube parent. -/
def rawCellWitnesses {n nA : ℕ} (C : FiniteScaleSource nA) (c : ℕ) (pA : Parent)
    (Occ : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (k : Index) :
    Finset ((Fin nA × Index) × (Fin n × Index)) :=
  (rawSelectedOccurrences C c pA Occ B).filter (fun z =>
    localCellLabel C 0 (2^c) pA z.1=k ∧ parentLabel C 0 (2^c) z.1.1=pA)

/-- Every cell of the literal translated-tag output has a retained RAW
witness for its same original intermediate tube label and same final cell. -/
theorem source_cell_raw_witness {n nA : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (C : FiniteScaleSource nA) (R : Finset (Fin nA)) (c : ℕ) (pA : Parent)
    (Occ : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index))) (hB : B⊆Occ.image (rawTaggedKey C c pA))
    (i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index)
    (hk : k∈sourceCells C R (selectedPairs D a m C c pA Occ (translatedTags D a m B))
      0 (2^c) pA i) :
    ∃z∈rawCellWitnesses C c pA Occ B k,
      z.1.1=NativePaddedCellSource.originalLabel (parentLabels C R 0 (2^c) pA) i := by
  let j := NativePaddedCellSource.originalLabel (parentLabels C R 0 (2^c) pA) i
  have hk' : k∈outputCells C (selectedPairs D a m C c pA Occ (translatedTags D a m B))
      0 (2^c) pA j := hk
  obtain ⟨l,hl,hCell⟩ := (mem_outputCells C _ 0 (2^c) pA j k).mp hk'
  obtain ⟨z,hOcc,hRaw,hPair⟩ := translated_selected_raw_witness D a m C c pA Occ B hB (j,l) hl
  have hj : parentLabel C 0 (2^c) j=pA :=
    ((mem_parentLabels C R 0 (2^c) pA j).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels C R 0 (2^c) pA) i)).2
  have hTube : z.1.1=j := congrArg Prod.fst hPair
  have hFinal : localCellLabel C 0 (2^c) pA z.1=k :=
    (congrArg Prod.snd hPair).trans hCell
  refine ⟨z,mem_filter.mpr ⟨mem_filter.mpr ⟨hOcc,hRaw⟩,hFinal,?_⟩,hTube⟩
  rw [hTube]
  exact hj

/-- Equal final points recover equality of TRUE original k3 through the
raw tag coherence. No converse from translated heights is used. -/
theorem same_raw_original_height {n nA : ℕ} (C : FiniteScaleSource nA)
    (c : ℕ) (pA : Parent) (Occ : Finset ((Fin nA × Index) × (Fin n × Index)))
    (B : Finset (ℤ × (Fin nA × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (k : Index) (z w : (Fin nA × Index) × (Fin n × Index))
    (hz : z∈rawCellWitnesses C c pA Occ B k) (hw : w∈rawCellWitnesses C c pA Occ B k) :
    z.2.2 3=w.2.2 3 := by
  obtain ⟨hzRaw,hzCell,_hzParent⟩ := mem_filter.mp hz
  obtain ⟨hwRaw,hwCell,_hwParent⟩ := mem_filter.mp hw
  apply hB (rawTaggedKey C c pA z) (mem_filter.mp hzRaw).2
    (rawTaggedKey C c pA w) (mem_filter.mp hwRaw).2
  change localCellLabel C 0 (2^c) pA z.1 3=localCellLabel C 0 (2^c) pA w.1 3
  rw [hzCell,hwCell]

/-- Actual source geometry gives both pairwise old-point diameter and the
257^4 prepared old physical-cell menu at one final native point. The
queried depth remains explicit:64/2^depth>=512*dIntermediate. -/
theorem actual_raw_cell_old_menu {n : ℕ} {D : FiniteScaleSource n} {eta etaC a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (m b : ℕ) (hm : 6 ≤ m) (p : Parent)
    (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness≤1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ)≤64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Q.card → Finset Index) (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (A : Finset (Fin n × Index)) (hA : A⊆incidences original)
    (hParent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)≤4096/((2^b:ℕ):ℝ))
    (c : ℕ) (pA : Parent) (B : Finset (ℤ × (Fin Q.card × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (k : Index) (depth : ℕ) (hQuery : 512*C.thickness≤64/((2^depth:ℕ):ℝ)) :
    let Occ := occurrences h backbone a m b p hp Q cells A
    let V := rawCellWitnesses C c pA Occ B k
    (∀z∈V,∀w∈V,z.2.2 3=w.2.2 3 ∧
      dist (point D a m p .oneTwo P hP hd F Fcfg R0 z.2.2)
        (point D a m p .oneTwo P hP hd F Fcfg R0 w.2.2)≤64*C.thickness ∧
      dist (oldPoint D a m p z.2.2) (oldPoint D a m p w.2.2)≤65536*C.thickness) ∧
    (V.image (fun z => physicalCell D a (2^m) (2^depth) p z.2.2)).card≤257^4 := by
  intro Occ V
  let O := NativePackedFrameIsometry.frame .oneTwo P hP hd
  let cfg := point D a m p .oneTwo P hP hd F Fcfg R0
  let sigma : ℝ := ((2^c:ℕ):ℝ)*C.thickness/64
  have hD : 0<C.thickness := hC.1.2.1
  have hLambda : 0<horizontalScale (2^c) := horizontalScale_pos (by positivity)
  have hWidth : mu m*(R0:ℝ)≤64*C.thickness := by
    rw [hthickness]
    exact hmatch.trans_eq (by ring)
  have hMu : mu m≤C.thickness := by
    have hIdentity : rho m=64*mu m := by unfold mu; ring
    rw [hIdentity] at hbase
    linarith only [hbase,hWidth]
  have hOcc (z : (Fin Q.card × Index) × (Fin n × Index)) (hz : z∈V) : z∈Occ :=
    (mem_filter.mp (mem_filter.mp hz).1).1
  have hOldA (z : (Fin Q.card × Index) × (Fin n × Index)) (hz : z∈V) : z.2∈A :=
    ((mem_occurrences h backbone a m b p hp Q cells A z).mp (hOcc z hz)).2.1
  have hInverseHeight (x : E4) : O.symm x 3=x 3 := by
    simpa only [O,LinearIsometryEquiv.apply_symm_apply] using
      (NativePackedFrameIsometry.frame_height .oneTwo P hP hd (O.symm x)).symm
  have hHalo (z : (Fin Q.card × Index) × (Fin n × Index)) (hz : z∈V) :
      dist (cellCenter (sigma/2) k)
        (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg z.2.2)))≤4*sigma := by
    have hh := occurrence_center_near h original horiginal ha backbone m b hm p hp hNscale hRelScale
      Q C hC cells hcells haC hthickness A hA hParent .oneTwo P hP hd F Fcfg hF hCfg
      R0 hR0 hbase hmatch c pA z (hOcc z hz) (mem_filter.mp hz).2.2
    rw [(mem_filter.mp hz).2.1] at hh
    have hMesh : ((2^c:ℕ):ℝ)*C.thickness/128=sigma/2 := by dsimp only [sigma]; ring
    rw [hMesh] at hh
    exact hh
  have hDistance : ∀z∈V,∀w∈V,z.2.2 3=w.2.2 3 ∧
      dist (cfg z.2.2) (cfg w.2.2)≤64*C.thickness ∧
      dist (oldPoint D a m p z.2.2) (oldPoint D a m p w.2.2)≤65536*C.thickness := by
    intro z hz w hw
    have hOriginal := same_raw_original_height C c pA Occ B hB k z w hz hw
    have hTranslated := translatedHeight_eq_of_original_height_eq D a m hOriginal
    have hTime : O.symm (cfg z.2.2) 3=O.symm (cfg w.2.2) 3 := by
      rw [hInverseHeight,hInverseHeight]
      simp only [cfg,point,graphGrid_height,sourceLabel_height,hTranslated]
    have hPhysical : dist (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg z.2.2)))
        (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg w.2.2)))≤8*sigma := by
      have ht := dist_triangle
        (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg z.2.2)))
        (cellCenter (sigma/2) k)
        (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg w.2.2)))
      rw [dist_comm _ (cellCenter (sigma/2) k)] at ht
      linarith only [ht,hHalo z hz,hHalo w hw]
    have hPhysicalEq : dist (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg z.2.2)))
        (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg w.2.2)))=
        horizontalScale (2^c)*dist (cfg z.2.2) (cfg w.2.2) := by
      rw [dist_eq_norm,physical_difference_same_height C 0 (2^c) pA _ _ hTime,
        norm_smul,Real.norm_eq_abs,abs_of_pos hLambda,←dist_eq_norm,O.symm.dist_map]
    rw [hPhysicalEq] at hPhysical
    have hCfgDist : dist (cfg z.2.2) (cfg w.2.2)≤64*C.thickness := by
      apply (mul_le_mul_iff_right₀ hLambda).mp
      have hCancel : 8*sigma=horizontalScale (2^c)*(64*C.thickness) := by
        dsimp only [sigma,horizontalScale]
        ring
      simpa only [mul_comm,hCancel] using hPhysical
    have hOldDist := oldPoint_dist_of_configured h m hm p z.2.1
      ((mem_parentLabels D backbone a (2^m) p _).mp (hParent z.2 (hOldA z hz))).2
      .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase hD hMu hWidth z.2.2 w.2.2
      (hCfgDist.trans (by linarith only [hD]))
    exact ⟨hOriginal,hCfgDist,by convert hOldDist using 1; ring⟩
  refine ⟨hDistance,?_⟩
  let Old := V.image Prod.snd
  have hCard := physical_image_card_of_diameter D a m depth p Old (by
    intro z hz w hw
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    obtain ⟨v',hv',rfl⟩ := mem_image.mp hw
    have hh := (hDistance v hv v' hv').2.2
    linarith only [hh,hQuery])
  simpa only [Old,image_image,Function.comp_def] using hCard

end NativeRawSamePointOldCellMenuDraft2300
