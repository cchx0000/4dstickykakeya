/- UNVERIFIED actual remembered-source scalar caller. No compiler run.
The final-time field is obtained from the literal first HeightAlignment.
Every source cell supplies its own selected original occurrence; the actual
source halo is then derived. No higher support, hPatch, normalized quotient
membership, common physical-height or halo input is admitted here.
The scalar set Y is FULL first-alignment Y, at rho/tau=sigma/32768.
All cells and keys remain in the original native cubical source coordinates.
-/
import Theorems.Thm_StickyKakeya4_native_remembered_higher_key_factory_draft_2032
import Theorems.Thm_StickyKakeya4_native_remembered_alignment_patch_draft_2036

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeRememberedFinalTimeScalarDraft2054
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeParentLabels
open NativeTranslatedGrainHeightOverlap NativeConfiguredThirdRelation NativeActualConfiguredPoint
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints CanonicalConfiguredE4Bridge
open NativeLiteralYHeightAlignment NativePaperAlignmentScales NativePackedHigherCapacityDraft2006
open NativeRememberedSourceMaps NativeRememberedCellHalo NativeLocalCellCoherence
open NativeRememberedHigherKeyFactoryDraft2032 NativeRememberedAlignmentPatchDraft2036
open NativeFullYHaloCoverDraft2017

def timeCells {n : ℕ} (cells : Fin n → Finset Index) (t : ℤ) : Finset Index :=
  ((incidences cells).image Prod.snd).filter (fun k => k 3=t)

/-- Read the actual common5.3 menu at an occupied final native time.
Its original coarse height is derived from the selected source occurrence.
Consequently the common chart, rho/tau depths, retained exponent bin, and
whole selected planar slice are all available for the following caller. -/
theorem occupied_alignment_height {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (backbone : Finset (Fin n))
    (a : ℝ) (m b : ℕ) (p : Parent) (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card) (cells : Fin Q.card → Finset Index)
    (A : Finset (Fin n × Index)) (c : ℕ) (R : Finset (Fin Q.card)) (pA : Parent)
    (B : Finset (ℤ × (Fin Q.card × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (R0 : ℕ)
    (kept Ybase : Finset NativeLiteralYHeightAlignment.Key) (u bins : ℕ) (t zeta chi : ℝ)
    (W : ∀h : {h : ℤ // h∈Ybase.image Prod.fst},HeightAlignment Ybase u t zeta chi h.val)
    (bin : ℝ → Fin (bins+1)) (menu : NativeYCommonScaleSelection.Menu u bins)
    (hCommon : ∀h∈kept.image Prod.fst,∃hh : h∈Ybase.image Prod.fst,
      (W ⟨h,hh⟩).chart=menu.1 ∧ (W ⟨h,hh⟩).rhoDepth=menu.2.1 ∧
      (W ⟨h,hh⟩).tauDepth=menu.2.2.1 ∧ bin (W ⟨h,hh⟩).exponent=menu.2.2.2 ∧
      heightPoints kept ((2:ℝ)⁻¹^u/512) h=(W ⟨h,hh⟩).selected)
    (hKey : ∀z∈A,coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2∈kept)
    (finalH : ℤ) (i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index)
    (hk : k∈sourceCells C R
      (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B)
      0 (2^c) pA i) (ht : k 3=finalH) :
    ∃hh : oldHeight B finalH/((8*R0:ℕ):ℤ)∈Ybase.image Prod.fst,
      let H := W ⟨oldHeight B finalH/((8*R0:ℕ):ℤ),hh⟩
      H.chart=menu.1 ∧ H.rhoDepth=menu.2.1 ∧ H.tauDepth=menu.2.2.1 ∧
      bin H.exponent=menu.2.2.2 ∧
      heightPoints kept ((2:ℝ)⁻¹^u/512) (oldHeight B finalH/((8*R0:ℕ):ℤ))=H.selected := by
  obtain ⟨v,z,_hv,hOcc,_hCurrent,_hCell,_hTag,hOld⟩ :=
    source_cell_occurrence D a m C R c pA
      (occurrences h backbone a m b p hp Q cells A) B hB i k hk
  have hzA := ((mem_occurrences h backbone a m b p hp Q cells A (v,z)).mp hOcc).2.1
  have hHeight : (coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2).1=
      oldHeight B finalH/((8*R0:ℕ):ℤ) := by
    rw [NativeConfiguredLowerQuotientReadback.coarse_height_readback,hOld,ht]
  apply hCommon
  exact mem_image.mpr ⟨coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2,hKey z hzA,hHeight⟩

/-- For one OCCUPIED native S cell-time, derive the actual common corrected
higher field, full scalar family, and every native-cell witness directly
from selected occurrences and the first HeightAlignment. The old-height
slice is constructed inside the proof, so no per-old-height population
hypothesis is required. Its nonemptiness comes from a genuine S cell. -/
theorem actual_final_time_scalar_family {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS etaC a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref T A : Finset (Fin n × Index))
    (m : ℕ) (hm : 6≤m) (p : Parent) (hp : (parentLabels D backbone a (2^m) p).Nonempty)
    (hscale : D.thickness≤(rho m)^2)
    (hS : IsWangZakharovNativeFiniteInput (source h backbone Eref a m p) etaS)
    (hSK : ∀i,(source h backbone Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (levelS b c : ℕ) (hb : 8≤b) (hc : c≤b)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness≤1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ)≤64)
    (Q : Finset Parent) (C : FiniteScaleSource Q.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Q.card → Finset Index) (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hthickness : C.thickness=64/((2^b:ℕ):ℝ))
    (hA : A⊆incidences original)
    (hParent : ∀z∈A,z.1∈parentLabels D backbone a (2^m) p)
    (q : Parent) (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=q)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (F Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hF : ∀t i j,|F t i j|≤1/4) (hCfg : ∀t i j,|Fcfg t i j|≤1/4)
    (R0 : ℕ) (hR0 : 0<R0) (hbase : rho m≤mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)≤4096/((2^b:ℕ):ℝ))
    (R : Finset (Fin Q.card)) (pA : Parent)
    (B : Finset (ℤ × (Fin Q.card × Index)))
    (hB : ∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1)
    (finalH : ℤ)
    (i0 : Fin (parentLabels C R 0 (2^c) pA).card) (k0 : Index)
    (hk0 : k0∈sourceCells C R
      (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B)
      0 (2^c) pA i0) (ht0 : k0 3=finalH)
    (kept Ybase : Finset NativeLiteralYHeightAlignment.Key) (u : ℕ) (t zeta chi : ℝ)
    (hZeta : 0≤zeta)
    (hBaseEq : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u)
    (W : HeightAlignment Ybase u t zeta chi (oldHeight B finalH/((8*R0:ℕ):ℤ)))
    (hSelected : heightPoints kept ((2:ℝ)⁻¹^u/512)
      (oldHeight B finalH/((8*R0:ℕ):ℤ))=W.selected)
    (hKey : ∀z∈A,coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2∈kept)
    (hTau : NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val=
      4096*(64/((2^c:ℕ):ℝ)))
    (hRho : C.thickness=8*NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val) :
    let sigma := ((2^c:ℕ):ℝ)*C.thickness/64
    let O := (NativePackedFrameIsometry.frame .oneTwo P hP hd).trans (normalChart W.chart)
    let M := chartRows W.chart (Fcfg (oldHeight B finalH/((8*R0:ℕ):ℤ)))
    let cellsS := sourceCells C R
      (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B) 0 (2^c) pA
    ∃(theta beta : ℝ) (Y : Finset ℝ),
      |theta|≤1 ∧ |M 1 0-theta*M 0 0|≤1/2 ∧ Y.Nonempty ∧ (∀y∈Y,|y|≤1) ∧
      FiniteVoronoiRealADCoarsening.ADBounds Y (sigma/32768)
        ((sigma/32768)^(-zeta)) (t-W.exponent) ∧
      (∀(i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index),
        k∈sourceCells C R
          (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B)
          0 (2^c) pA i → k 3=finalH →
        ∃y∈Y,|packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k)-
          (512*y+beta)|≤13*sigma) ∧
      ∀r : ℝ,sigma/2≤r → r≤1 →
        ((scalarGrid (timeCells cellsS finalH)
          (fun k => packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k)) r).card:ℝ)≤
          452*((sigma/32768)^(-zeta))^2*(r/512)^(-(t-W.exponent)) ∧
        ∀(x : Fin 1 → ℝ) (radius : ℝ),r/512≤radius → radius≤1 →
          (((scalarGrid (timeCells cellsS finalH)
            (fun k => packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k)) r).filter
              (fun k => dist (NativeQuotientGridCenters.center (r/512) k) x≤radius)).card:ℝ)≤
            452*((sigma/32768)^(-zeta))^2*58^(t-W.exponent)*(radius/(r/512))^(t-W.exponent) := by
  intro sigma O M cellsS
  let oldH := oldHeight B finalH
  let Occ := occurrences h backbone a m b p hp Q cells A
  let Aold := A.filter (fun z => translatedHeight D a m z.2=oldH)
  let cfg := point D a m p .oneTwo P hP hd F Fcfg R0
  let O0 := NativePackedFrameIsometry.frame .oneTwo P hP hd
  let tau := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val
  let rhoA := NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val
  obtain ⟨v0,z0,_hv0,hOcc0,_hp0,_hcell0,_htag0,hOld0⟩ :=
    source_cell_occurrence D a m C R c pA Occ B hB i0 k0 hk0
  have hz0A : z0∈A := ((mem_occurrences h backbone a m b p hp Q cells A (v0,z0)).mp hOcc0).2.1
  have hz0old : z0∈Aold := by
    apply mem_filter.mpr
    exact ⟨hz0A,by simpa only [ht0] using hOld0⟩
  have hAold : Aold⊆incidences original := fun _ hz => hA (mem_filter.mp hz).1
  have hParentOld : ∀z∈Aold,z.1∈parentLabels D backbone a (2^m) p :=
    fun z hz => hParent z (mem_filter.mp hz).1
  have hHeightOld : ∀z∈Aold,translatedHeight D a m z.2=oldH := fun _ hz => (mem_filter.mp hz).2
  obtain ⟨anchor,theta,Y,_hAnchor,hTheta,hCoeff,hYn,hYbox,hYAD,hOldWitness⟩ :=
    actual_old_height_scalar_family h original horiginal ha backbone Eref T Aold ⟨z0,hz0old⟩
      m hm hscale p hS hSK levelS b c hb hc P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      hAold hParentOld oldH hHeightOld q (fun z hz => hPhase z (mem_filter.mp hz).1)
      kept Ybase u t zeta chi hBaseEq W hSelected (fun z hz => hKey z (mem_filter.mp hz).1) hTau
  let alpha := NativeAngularChartSelection.chartPoint W.chart anchor 1-
    theta*NativeAngularChartSelection.chartPoint W.chart anchor 0
  let anchorNative := O0.symm (cfg z0.2)
  let beta := NativeHigherQuotientParentTransport.horizontalScale (2^c)*alpha+
    packedParentShift C 0 (2^c) pA O (M 1 0-theta*M 0 0) theta anchorNative
  have hSigma : 0<sigma := by have hh := hC.1.2.1; dsimp only [sigma]; positivity
  have hPow : ((2^c:ℕ):ℝ)≠0 := by positivity
  have hTauScale : NativeHigherQuotientParentTransport.horizontalScale (2^c)*tau=512 := by
    change (_:ℝ)*NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val=512
    rw [hTau]
    unfold NativeHigherQuotientParentTransport.horizontalScale
    field_simp [hPow]
    <;> ring
  have hMesh : rhoA/tau=sigma/32768 := by
    change NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.rhoDepth.val/
      NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) W.tauDepth.val=
      (((2^c:ℕ):ℝ)*C.thickness/64)/32768
    rw [hTau,hRho]
    field_simp [hPow]
    <;> ring
  have hNativeWitness : ∀(i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index),
      k∈cellsS i → k 3=finalH →
      ∃y∈Y,|packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k)-
        (512*y+beta)|≤13*sigma := by
    intro i k hk hkt
    obtain ⟨v,z,_hv,hOcc,hCurrent,hCell,_hTag,hOld⟩ :=
      source_cell_occurrence D a m C R c pA Occ B hB i k hk
    have hzA : z∈A := ((mem_occurrences h backbone a m b p hp Q cells A (v,z)).mp hOcc).2.1
    have hzold : z∈Aold := mem_filter.mpr ⟨hzA,by simpa only [hkt] using hOld⟩
    obtain ⟨y,hy,hWitness⟩ := hOldWitness z hzold
    have hTimeCfg : cfg z.2 3=cfg z0.2 3 := by
      simp only [cfg,point,graphGrid_height,sourceLabel_height,hHeightOld z hzold,hHeightOld z0 hz0old]
    have hInverseHeight (x : E4) : O0.symm x 3=x 3 := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (NativePackedFrameIsometry.frame_height .oneTwo P hP hd (O0.symm x)).symm
    have hTime : O0.symm (cfg z.2) 3=anchorNative 3 := by
      rw [hInverseHeight,hInverseHeight]
      exact hTimeCfg
    have hOldScalar : |packedQuotient O (M 1 0-theta*M 0 0) theta (O0.symm (cfg z.2))-
        (tau*y+alpha)|≤2*rhoA := by
      simpa only [packedQuotient,LinearIsometryEquiv.trans_apply,
        LinearIsometryEquiv.apply_symm_apply] using hWitness
    have hHalo := occurrence_center_near h original horiginal ha backbone m b hm p hp hNscale hRelScale
      Q C hC cells hcells haC hthickness A hA hParent .oneTwo P hP hd F Fcfg hF hCfg
      R0 hR0 hbase hmatch c pA (v,z) hOcc hCurrent
    change dist (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128) (localCellLabel C 0 (2^c) pA v))
      (physicalMap C 0 (2^c) pA (O0.symm (cfg z.2)))≤4*sigma at hHalo
    rw [hCell] at hHalo
    have hMu : ((2^c:ℕ):ℝ)*C.thickness/128=sigma/2 := by dsimp only [sigma]; ring
    rw [hMu] at hHalo
    exact ⟨y,hy,parent_scalar_witness C 0 (2^c) pA O (M 1 0-theta*M 0 0) theta
      (hCoeff.trans (by norm_num)) hTheta rhoA tau C.thickness sigma alpha y hSigma hRho rfl
      hTauScale (O0.symm (cfg z.2)) anchorNative hTime k hOldScalar hHalo⟩

  have hAD : FiniteVoronoiRealADCoarsening.ADBounds Y (sigma/32768)
      ((sigma/32768)^(-zeta)) (t-W.exponent) := by simpa only [hMesh] using hYAD
  refine ⟨theta,beta,Y,hTheta,hCoeff,hYn,hYbox,hAD,hNativeWitness,?_⟩
  intro r hr hr1
  have htau0 : 0<tau := NativeDyadicTubeStopping.scale_pos (by positivity) _
  have he1 : sigma/32768≤1 := by
    rw [←hMesh]
    exact (div_le_one htau0).mpr W.scale_order.le
  have hK : 1≤(sigma/32768)^(-zeta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) he1 (neg_nonpos.mpr hZeta)
  have hAlpha : 0≤t-W.exponent := sub_nonneg.mpr (W.exponent_upper.trans (min_le_left _ _))
  apply scalar_halo_grid_upper (timeCells cellsS finalH)
    (fun k => packedQuotient O (M 1 0-theta*M 0 0) theta (cellCenter (sigma/2) k))
    Y sigma (sigma/32768) r beta ((sigma/32768)^(-zeta)) (t-W.exponent)
    hSigma rfl hr hr1 hK hAlpha hAD hYbox
  intro k hk
  obtain ⟨hkCells,hTime⟩ := mem_filter.mp hk
  obtain ⟨ik,hik,heq⟩ := mem_image.mp hkCells
  subst k
  exact hNativeWitness ik.1 ik.2 ((mem_incidences cellsS ik.1 ik.2).mp hik) hTime

end NativeRememberedFinalTimeScalarDraft2054
