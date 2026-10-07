/- UNVERIFIED actual remembered-source union upper. The only AD input is
HasThirdXYData on the unchanged complete T. Later restrictions use original
occurrences and one actual old height per final native cell-time label. -/
import Theorems.Thm_StickyKakeya4_native_remembered_phase_cover
import Theorems.Thm_StickyKakeya4_native_remembered_cell_fibers
import Theorems.Thm_StickyKakeya4_native_remembered_time_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeRememberedSourceUnion
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeParentLabels
open NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridField
open NativeHorizontalGrainSlice NativeSquaredGrainQueries NativeThirdXYData NativeRetainedSliceCore
open NativeGrainQuotientFibers NativeTranslatedGrainHeightOverlap NativeFixedCompactKakeyaExponent
open NativeRememberedSourceMaps NativeRememberedPhaseCover NativeRememberedCellFibers NativeRememberedTimeUpper
open NativeLocalCellCoherence
open scoped ENNReal Matrix.Norms.Elementwise

/-- All source-dependent loss is the actual complete-slice constant K squared. -/
def unionConstant (K : ℝ) : ℝ :=
  (129^4:ℝ)*(257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2*(36:ℝ)^(3-extremalExponent)

/-- Literal same-T source join: original old-phase geometry, complete-slice
AD, actual intermediate shadows, final local cells, and the chosen old-height
relation are composed. Neither an output point-count upper nor a subset AD
lower is assumed. -/
theorem rank_two_union {n d J : ℕ} {D : FiniteScaleSource n} {eta etaS etaC a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (backbone : Finset (Fin n)) (Eref : Finset (Fin n × Index))
    (m level : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m ≤ level) (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hRef : IsWangZakharovNativeFiniteInput (NativeLocalParentSource.source h backbone Eref a m p) etaS)
    (hRefK : ∀i,(NativeLocalParentSource.source h backbone Eref a m p).line i∈fixedCompactClass)
    (levelS b0 c depth : ℕ) (hb0 : 8 ≤ b0) (hc : c ≤ b0) (hdepth : 6 ≤ depth)
    (hwidth : 64/((2^depth:ℕ):ℝ)=512*(64/((2^c:ℕ):ℝ)))
    (plane : Index → Submodule ℝ E4) (E Hgraph S T : Finset (Fin n × Index))
    (hT : T⊆incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D backbone a (2^m) p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata : HasThirdXYData (J:=J) (ell:=2) D zeta a m plane E Hgraph S T P hP
      (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 0 < Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b0:ℕ):ℝ))
    (hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hquery : (Rd:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hkappa : extremalExponent ≤ 3)
    (A : Finset (Fin n × Index)) (hAT : A⊆T) (qOld : Parent)
    (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=qOld)
    (b : ℕ) (hbb : b ≤ b0)
    (hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64)
    (Qmid : Finset Parent) (C : FiniteScaleSource Qmid.card)
    (hC : IsWangZakharovNativeFiniteInput C etaC)
    (cells : Fin Qmid.card → Finset Index) (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (haC : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (hCthick : C.thickness=64/((2^b:ℕ):ℝ))
    (hRd512 : 512 ≤ Rd) (hRdMesh : (Rd:ℝ)*mu m=512*C.thickness)
    (pA : Parent) (hsigma : ((2^c:ℕ):ℝ)*C.thickness/64 ≤ 1) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+2) (J+1) L3
    let K := xyConstant D.thickness zeta population PL PU lambda (G*Cpre*(F3:ℝ)) Qref Q3 J m
    let hp : (parentLabels D backbone a (2^m) p).Nonempty := card_pos.mp hRef.1.1
    let O := occurrences h backbone a m b p hp Qmid cells A
    ∀B⊆O.image (taggedKey D a m C c pA),
      (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) →
      let Efinal := selectedPairs D a m C c pA O B
      (∀z∈Efinal,z.1∈parentLabels C univ 0 (2^c) pA) →
      volume (sourceUnion (NativeLocalParentSource.source hC univ Efinal 0 c pA)) ≤
        ENNReal.ofReal (unionConstant K*(((2^c:ℕ):ℝ)*C.thickness/64)^extremalExponent) := by
  intro Sq F Q3 F3 K hp O B hBO hHeightChoice Efinal hParentFinal
  let V := selectedOccurrences D a m C c pA O B
  let cell := fun z : (Fin Qmid.card × Index) × (Fin n × Index) => localCellLabel C 0 (2^c) pA z.1
  let time := fun z : (Fin Qmid.card × Index) × (Fin n × Index) => cell z (3:Fin 4)
  let xy := fun z : Fin n × Index => coarseXY 2 Rd (pxy D a m 2 p P hP (by norm_num) (by norm_num) hd F z.2)
  let sigma : ℝ := ((2^c:ℕ):ℝ)*C.thickness/64
  let Cover : ℝ := (257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2*6^(3-extremalExponent)*
    ((6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m))^(3-extremalExponent)
  have hs : 0 < sigma := by dsimp [sigma]; have hdC := hC.1.2.1; positivity
  have hCover : 0 ≤ Cover := by dsimp [Cover]; positivity
  have Hcopy := Hdata
  rcases Hcopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,
    _hGrain,_hKey,_hThreshold,_hRet,_Hxy,_hRead,hNorm⟩
  have hVO : V⊆O := filter_subset _ _
  have hOrig (z : (Fin Qmid.card × Index) × (Fin n × Index)) (hz : z∈V) : z.2∈A :=
    ((mem_occurrences h backbone a m b p hp Qmid cells A z).mp (hVO hz)).2.1
  have hEinc : Efinal⊆incidences cells := by
    intro z hz
    obtain ⟨v,hv,he⟩ := mem_image.mp hz
    rw [←he]
    exact ((mem_occurrences h backbone a m b p hp Qmid cells A v).mp (hVO hv)).1
  have hCurrent (z : (Fin Qmid.card × Index) × (Fin n × Index)) (hz : z∈V) :
      parentLabel C 0 (2^c) z.1.1=pA :=
    ((mem_parentLabels C univ 0 (2^c) pA _).mp (hParentFinal z.1 (mem_image_of_mem _ hz))).2
  have hmatchb : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ) := by
    apply hmatch.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hbb
  have hLocal (j : ℤ) (hj : j∈V.image time) :
      (((V.filter (fun z => time z=j)).image cell).card:ℝ) ≤ (129^4:ℝ)*Cover := by
    let W := V.filter (fun z => time z=j)
    obtain ⟨anchor,hanchorV,hanchorTime⟩ := mem_image.mp hj
    have hanchor : anchor∈W := mem_filter.mpr ⟨hanchorV,hanchorTime⟩
    let U := W.image Prod.snd
    have hUA : U⊆A := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact hOrig w (mem_filter.mp hw).1
    have hUT : U⊆T := hUA.trans hAT
    have hOldHeight : ∀z∈U,translatedHeight D a m z.2=translatedHeight D a m anchor.2.2 := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact hHeightChoice (taggedKey D a m C c pA w) (mem_filter.mp (mem_filter.mp hw).1).2
        (taggedKey D a m C c pA anchor) (mem_filter.mp hanchorV).2
        ((mem_filter.mp hw).2.trans hanchorTime.symm)
    have hXY := rank_two_from_third h original horiginal ha backbone Eref m level hm hdy hf hscale p
      hRef hRefK levelS b0 c depth hb0 hc hdepth hwidth plane E Hgraph S T hT hparent
      P hP hd Fraw Fcfg hCfg population PL PU Qref lambda G Cpre threshold L3 Rel Hdata
      R0 Rd hR0 hRd hbase hmatch hsmall hquery hkappa U hUT
      (translatedHeight D a m anchor.2.2) qOld hOldHeight (fun z hz => hPhase z (hUA hz))
    have hXY' : ((W.image (fun z => xy z.2)).card:ℝ) ≤ Cover := by
      simpa only [U,xy,Cover,image_image] using hXY
    have hFiber (q : NativeReferenceXYGridMaps.XY 2) (_hq : q∈W.image (fun z => xy z.2)) :
        (((W.filter (fun z => xy z.2=q)).image cell).card:ℝ) ≤ (129^4:ℝ) := by
      exact_mod_cast actual_fiber_card h original horiginal ha backbone m b (by omega) p hp hNscale hRelScale
        Qmid C hC cells hcells haC hCthick A (hAT.trans hT) (fun z hz => hparent z (hAT hz))
        P hP hd F Fcfg hNorm hCfg R0 Rd hR0 hRd512 hbase hmatchb hRdMesh c pA W
        ((filter_subset _ _).trans hVO) (fun z hz => hCurrent z (mem_filter.mp hz).1) q
    have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images W cell
      (fun z => xy z.2) (129^4:ℝ) hFiber
    exact hh.trans (mul_le_mul_of_nonneg_left hXY' (by positivity))
  have hSupport := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images V cell time
    ((129^4:ℝ)*Cover) hLocal
  have hTime := local_time_card hC cells hcells haC (2^c) (by positivity) pA hsigma Efinal hEinc
  have hTimeRead : Efinal.image (fun z => localCellLabel C 0 (2^c) pA z (3:Fin 4))=V.image time := by
    rw [show Efinal=V.image Prod.fst from rfl,image_image]
    rfl
  rw [hTimeRead] at hTime
  have hSupportRead : Efinal.image (localCellLabel C 0 (2^c) pA)=V.image cell := by
    rw [show Efinal=V.image Prod.fst from rfl,image_image]
    rfl
  have hCount : ((Efinal.image (localCellLabel C 0 (2^c) pA)).card:ℝ) ≤
      ((129^4:ℝ)*Cover)*(6/sigma) := by
    rw [hSupportRead]
    exact hSupport.trans (mul_le_mul_of_nonneg_left hTime (mul_nonneg (by positivity) hCover))
  have hRatio : (6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m)=6/sigma := by
    rw [hwidth,hRdMesh]
    dsimp [sigma]
    have hN : (((2^c:ℕ):ℝ)) ≠ 0 := by positivity
    field_simp [hN,hC.1.2.1.ne']
  have hCoverEq : (129^4:ℝ)*Cover=unionConstant K*sigma^(-(3-extremalExponent)) := by
    dsimp only [Cover,unionConstant]
    rw [hRatio,Real.div_rpow (by norm_num : (0:ℝ) ≤ 6) hs.le,Real.rpow_neg hs.le]
    have hp : (6:ℝ)^(3-extremalExponent)*(6:ℝ)^(3-extremalExponent)=
        (36:ℝ)^(3-extremalExponent) := by
      rw [←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) (by norm_num : (0:ℝ) ≤ 6)]
      norm_num
    calc
      _ = ((129^4:ℝ)*(257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2)*
          ((6:ℝ)^(3-extremalExponent)*(6:ℝ)^(3-extremalExponent))/sigma^(3-extremalExponent) := by ring
      _ = _ := by rw [hp]; ring
  have hBalance : sigma^(-(3-extremalExponent))*sigma^3=sigma^extremalExponent := by
    rw [←Real.rpow_natCast sigma 3,←Real.rpow_add hs]
    congr 1
    ring
  have hscalar : (((129^4:ℝ)*Cover)*(6/sigma))*(sigma/2)^4 ≤
      unionConstant K*sigma^extremalExponent := by
    rw [hCoverEq]
    have he : (6/sigma)*(sigma/2)^4=(3/8:ℝ)*sigma^3 := by field_simp [hs.ne']; ring
    calc
      _ = unionConstant K*(sigma^(-(3-extremalExponent))*sigma^3)*(3/8:ℝ) := by
        rw [mul_assoc,mul_assoc,he]
        ring
      _ = unionConstant K*sigma^extremalExponent*(3/8:ℝ) := by rw [hBalance]
      _ ≤ _ := mul_le_of_le_one_right (by unfold unionConstant; positivity) (by norm_num)
  have hVolReal := (mul_le_mul_of_nonneg_right hCount (show 0 ≤ (sigma/2)^4 by positivity)).trans hscalar
  rw [NativeLocalParentSource.source_union_volume hC univ Efinal 0 c pA hParentFinal]
  have he : ((2^c:ℕ):ℝ)*C.thickness/128=sigma/2 := by dsimp [sigma]; ring
  rw [he]
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_pow (half_pos hs).le,
    ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hVolReal

end NativeRememberedSourceUnion
