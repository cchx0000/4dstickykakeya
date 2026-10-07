import Theorems.Thm_StickyKakeya4_native_actual_raw_remembered_source

/- Rank-three remembered-source geometry. Originally drafted without
verification; consult current receipts. The full original T supplies XY
AD at exponent3-kappa. Later subsets contribute only literal occurrence
images and upper counts. No new source, slice lower or capacity premise.
The fixed geometric constants are the same as the checked rank-two route. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeActualRawRankThreeSource
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeParentLabels
open NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridField
open NativeReferenceXYGridLinear NativeReferenceXYGridMetric NativeHorizontalGrainSlice
open NativeSquaredGrainQueries NativeThirdXYData NativeRetainedSliceCore
open NativeGrainQuotientFibers NativeTranslatedGrainHeightOverlap NativeFixedCompactKakeyaExponent
open NativeRememberedSourceMaps NativeRememberedPhaseCover NativeRememberedCellFibers NativeRememberedTimeUpper
open NativeLocalCellCoherence NativeOriginalCellChartGeometry NativeAnisotropicShortRowGeometry
open CanonicalConfiguredE4Bridge NativeMatchedShadowConfiguredGeometry NativeJointSpatialGeometry
open NativeRememberedCellHalo NativeNormalizedCellRelativeMenu NativeRememberedPhaseFootprint
open NativeJointLocalXYGeometry NativeRememberedSourceUnion NativeRawHeightSourceAdapter
open NativeRememberedOccurrenceReadback NativeActualRawRememberedSource NativeActualRawWeightSource
open NativeCoarseSourceParentReadback NativeRelativeCoarseReadback NativeIntermediateParentPopulation
open NativeCoarseCellSource NativeCoarseDirectionThinning
open scoped ENNReal Matrix.Norms.Elementwise

theorem configured_gap_of_coarse_XY_three {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=2)
    (F Fcfg : ℤ → Matrix (Fin 1) (Fin 2) ℝ)
    (hF : ∀t,‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 512 ≤ Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    {d : ℝ} (hdpos : 0 < d) (hmu : mu m ≤ d) (hbaseD : mu m*(R0:ℝ) ≤ 64*d)
    (hmesh : (Rd:ℝ)*mu m=512*d) (k l : Index)
    (hxy : coarseXY 3 Rd (pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F k)=
      coarseXY 3 Rd (pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F l)) :
    dist (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 k)
      (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 l) ≤ 16*d := by
  have hOld := coarse_xy_old_dist h m 3 hm p i hi P hP (by norm_num) (by norm_num) hd F hF Rd hRd k l hxy
  rw [hmesh] at hOld
  have hraw := (raw_dist_le_old h m hm p i hi k l).trans (add_le_add_right hOld (256*mu m))
  have hFe : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hF t) i j
  let O := NativePackedFrameIsometry.frame .twoOne P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0
  let x := O ((1/512:ℝ) • rawPoint D a m p k)
  let y := O ((1/512:ℝ) • rawPoint D a m p l)
  have hk := NativeActualConfiguredPoint.point_distance D a m hm p .twoOne P hP hd F Fcfg hFe hCfg R0 hR0 k hbase
  have hl := NativeActualConfiguredPoint.point_distance D a m hm p .twoOne P hP hd F Fcfg hFe hCfg R0 hR0 l hbase
  have hs : dist x y=(1/512:ℝ)*dist (rawPoint D a m p k) (rawPoint D a m p l) := by
    simp only [x,y,O.dist_map,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs]
    norm_num
  have h1 := dist_triangle (cfg k) x (cfg l)
  have h2 := dist_triangle x y (cfg l)
  change dist (cfg k) x ≤ _ at hk
  change dist (cfg l) y ≤ _ at hl
  rw [dist_comm y (cfg l),hs] at h2
  nlinarith only [h1,h2,hk,hl,hraw,hmu,hbaseD,hdpos]

theorem actual_fiber_card_three {n : ℕ} {D : FiniteScaleSource n} {eta etaC a : ℝ}
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
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=2)
    (F Fcfg : ℤ → Matrix (Fin 1) (Fin 2) ℝ)
    (hF : ∀t,‖F t‖ ≤ (1/4:ℝ)) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 512 ≤ Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ))
    (hmesh : (Rd:ℝ)*mu m=512*C.thickness)
    (c : ℕ) (pA : Parent)
    (V : Finset ((Fin Q.card × Index) × (Fin n × Index)))
    (hV : V⊆occurrences h backbone a m b p hp Q cells A)
    (hcurrent : ∀z∈V,parentLabel C 0 (2^c) z.1.1=pA)
    (q : NativeReferenceXYGridMaps.XY 3) :
    (((V.filter (fun z => coarseXY 3 Rd
      (pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F z.2.2)=q)).image
      (fun z => localCellLabel C 0 (2^c) pA z.1)).card) ≤ 129^4 := by
  let U := V.filter (fun z => coarseXY 3 Rd
    (pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F z.2.2)=q)
  have hFe : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hF t) i j
  have hBaseD : mu m*(R0:ℝ) ≤ 64*C.thickness := by rw [hthickness]; convert hmatch using 1; ring
  have hmu : mu m ≤ C.thickness := by
    have hr : rho m=64*mu m := by unfold rho mu; ring
    rw [hr] at hbase
    linarith only [hbase,hBaseD]
  let O := NativePackedFrameIsometry.frame .twoOne P hP hd
  let cfg := NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0
  have halo (z : (Fin Q.card × Index) × (Fin n × Index)) (hz : z∈U) :
      dist (cellCenter (((2^c:ℕ):ℝ)*C.thickness/128) (localCellLabel C 0 (2^c) pA z.1))
        (NativeLocalParentPhysicalMap.physicalMap C 0 (2^c) pA (O.symm (cfg z.2.2))) ≤
          4*(((2^c:ℕ):ℝ)*C.thickness/64) :=
    occurrence_center_near h original horiginal ha backbone m b hm p hp hNscale hRelScale Q C hC
      cells hcells haC hthickness A hA hparent .twoOne P hP hd F Fcfg hFe hCfg R0 hR0 hbase hmatch
      c pA z (hV (mem_filter.mp hz).1) (hcurrent z (mem_filter.mp hz).1)
  have hs : 0 < ((2^c:ℕ):ℝ)*C.thickness/64 := by have hc := hC.1.2.1; positivity
  apply local_cell_image_cap U (fun z => localCellLabel C 0 (2^c) pA z.1) hs
  intro z hz w hw
  have hzA := ((mem_occurrences h backbone a m b p hp Q cells A z).mp (hV (mem_filter.mp hz).1)).2.1
  have hOldParent := (mem_parentLabels D backbone a (2^m) p _).mp (hparent z.2 hzA)
  have hGap := configured_gap_of_coarse_XY_three h m hm p z.2.1 hOldParent.2 P hP hd F Fcfg hF hCfg
    R0 Rd hR0 hRd hbase hC.1.2.1 hmu hBaseD hmesh z.2.2 w.2.2
    ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm)
  have hh := local_centers_cluster hC (2^c) (by positivity) pA z.1.1
    (hcurrent z (mem_filter.mp hz).1) O (cfg z.2.2) (cfg w.2.2)
    (localCellLabel C 0 (2^c) pA z.1) (localCellLabel C 0 (2^c) pA w.1) (halo z hz) (halo w hw) hGap
  have he : (((2^c:ℕ):ℝ)*C.thickness/64)/2=((2^c:ℕ):ℝ)*C.thickness/128 := by ring
  simpa only [he] using hh

theorem rank_three_from_third {n d J : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta : ℝ}
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
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=2)
    (Fraw Fcfg : ℤ → Matrix (Fin 1) (Fin 2) ℝ)
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata : HasThirdXYData (J:=J) (ell:=3) D zeta a m plane E Hgraph S T P hP
      (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda G Cpre threshold L3 Rel)
    (R0 Rd : ℕ) (hR0 : 0 < R0) (hRd : 0 < Rd)
    (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ) ≤ 4096/((2^b0:ℕ):ℝ))
    (hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hquery : (Rd:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ))
    (hkappa : extremalExponent ≤ 3)
    (A : Finset (Fin n × Index)) (hAT : A⊆T) (height : ℤ) (q : Parent)
    (hHeight : ∀z∈A,translatedHeight D a m z.2=height)
    (hPhase : ∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=q) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 3 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 3 plane Sq Fraw
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost (d+2) (J+1) L3
    let K := xyConstant D.thickness zeta population PL PU lambda (G*Cpre*(F3:ℝ)) Qref Q3 J m
    ((A.image (fun z => coarseXY 3 Rd (pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F z.2))).card:ℝ) ≤
      (257^4:ℝ)*(9^3:ℝ)*(13^3:ℝ)^2*K^2*6^(3-extremalExponent)*
        ((6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m))^(3-extremalExponent) := by
  intro Sq F Q3 F3 K
  have Hcopy := Hdata
  rcases Hcopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,
    _hGrain,_hKey,_hThreshold,_hRet,Hxy,_hRead,hNorm⟩
  have hF : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hNorm t) i j
  let physical := fun z : Fin n × Index => physicalCell D a (2^m) (2^depth) p z.2
  let xy := fun z : Fin n × Index => coarseXY 3 Rd (pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F z.2)
  let C : ℝ := (9^3:ℝ)*(13^3:ℝ)^2*K^2*6^(3-extremalExponent)*
    ((6*(64/((2^depth:ℕ):ℝ)))/((Rd:ℝ)*mu m))^(3-extremalExponent)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 1 ≤ K := xyConstant_one_le _ _ _ _ _ _ _ _ _ _ _
  have hCard : (A.image physical).card ≤ 257^4 := by
    apply physical_image_card_of_diameter D a m depth p A
    intro z hz w hw
    have hcfg := actual_configured_diameter h original horiginal ha backbone Eref T m (by omega)
      hscale p hRef hRefK levelS b0 c hb0 hc .twoOne P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      z w (hT (hAT hz)) (hT (hAT hw)) (hparent z (hAT hz)) (hparent w (hAT hw))
      ((hHeight z hz).trans (hHeight w hw).symm) ((hPhase z hz).trans (hPhase w hw).symm)
    have hcw : 64/((2^b0:ℕ):ℝ) ≤ 64/((2^c:ℕ):ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hc
    have hbasew : mu m*(R0:ℝ) ≤ 64*(64/((2^c:ℕ):ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hcw (by norm_num : (0:ℝ) ≤ 64)
      have he : 4096/((2^b0:ℕ):ℝ)=64*(64/((2^b0:ℕ):ℝ)) := by ring
      rw [he] at hmatch
      exact hmatch.trans hh
    have hmuw : mu m ≤ 64/((2^c:ℕ):ℝ) := by rw [hwidth] at hsmall; linarith only [hsmall]
    have ho := oldPoint_dist_of_configured h m (by omega) p z.1
      ((mem_parentLabels D backbone a (2^m) p _).mp (hparent z (hAT hz))).2
      .twoOne P hP hd F Fcfg hF hCfg R0 hR0 hbase (by positivity) hmuw hbasew z.2 w.2 hcfg
    simpa only [hwidth] using ho
  have hLocal (v : Index) (_hv : v∈A.image physical) :
      (((A.filter (fun z => physical z=v)).image xy).card:ℝ) ≤ C := by
    let U := A.filter (fun z => physical z=v)
    by_cases hU : U.Nonempty
    · obtain ⟨anchor,hanchor⟩ := hU
      have hUT : U⊆T := (filter_subset _ _).trans hAT
      have hh := source_height_cell_base_keys h original horiginal ha m level 3 hm hdy hf p U T hUT
        hT (fun z hz => ((mem_parentLabels D backbone a (2^m) p _).mp (hparent z hz)).2)
        P hP (by norm_num) (by norm_num) hd F hNorm Rd depth hRd hdepth hsmall hquery
        anchor hanchor
        (fun z hz => (hHeight z (mem_filter.mp hz).1).trans (hHeight anchor (mem_filter.mp hanchor).1).symm)
        (fun z hz => (mem_filter.mp hz).2.trans (mem_filter.mp hanchor).2.symm)
        hK (by linarith only [hkappa]) (Hxy (translatedHeight D a m anchor.2))
      simpa only [U,xy,C,Nat.cast_pow,Nat.cast_ofNat] using hh
    · simp only [U,not_nonempty_iff_eq_empty.mp hU,image_empty,card_empty,Nat.cast_zero]
      exact hC
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images A xy physical C hLocal
  have hreal : ((A.image physical).card:ℝ) ≤ (257^4:ℝ) := by exact_mod_cast hCard
  have hbound := mul_le_mul_of_nonneg_left hreal hC
  exact hh.trans (by dsimp [C] at hbound; simpa only [mul_assoc,mul_left_comm,mul_comm] using hbound)

theorem rank_three_union {n d J : ℕ} {D : FiniteScaleSource n} {eta etaS etaC a zeta : ℝ}
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
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hd : Module.finrank ℝ P=2)
    (Fraw Fcfg : ℤ → Matrix (Fin 1) (Fin 2) ℝ)
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (population PL PU : ℝ) (Qref : ℕ) (lambda G Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata : HasThirdXYData (J:=J) (ell:=3) D zeta a m plane E Hgraph S T P hP
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
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 3 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 3 plane Sq Fraw
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
  let xy := fun z : Fin n × Index => coarseXY 3 Rd (pxy D a m 3 p P hP (by norm_num) (by norm_num) hd F z.2)
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
    have hXY := rank_three_from_third h original horiginal ha backbone Eref m level hm hdy hf hscale p
      hRef hRefK levelS b0 c depth hb0 hc hdepth hwidth plane E Hgraph S T hT hparent
      P hP hd Fraw Fcfg hCfg population PL PU Qref lambda G Cpre threshold L3 Rel Hdata
      R0 Rd hR0 hRd hbase hmatch hsmall hquery hkappa U hUT
      (translatedHeight D a m anchor.2.2) qOld hOldHeight (fun z hz => hPhase z (hUA hz))
    have hXY' : ((W.image (fun z => xy z.2)).card:ℝ) ≤ Cover := by
      simpa only [U,xy,Cover,image_image] using hXY
    have hFiber (q : NativeReferenceXYGridMaps.XY 3) (_hq : q∈W.image (fun z => xy z.2)) :
        (((W.filter (fun z => xy z.2=q)).image cell).card:ℝ) ≤ (129^4:ℝ) := by
      exact_mod_cast actual_fiber_card_three h original horiginal ha backbone m b (by omega) p hp hNscale hRelScale
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

theorem exists_same_Q_source_rank_three {n dRel J : ℕ} {D : FiniteScaleSource n}
    {eta etaS etaC a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (level m b0 b c depth : ℕ)
    (hm : 12 ≤ m) (hb0 : 8 ≤ b0) (hb : b ≤ b0) (hc : c ≤ b-6) (hc6 : 6 ≤ c)
    (hdepth : 6 ≤ depth) (hzeta : 0 ≤ zeta)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (hmb0 : m+b0 ≤ level) (hf : phaseDepth m ≤ level)
    (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hRef : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hRefK : ∀i,(source h R Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hwidth : 64/((2^depth:ℕ):ℝ)=512*(64/((2^c:ℕ):ℝ)))
    (plane : Index → Submodule ℝ E4) (E Hgraph S0 T0 Tcur : Finset (Fin n × Index))
    (hT0 : T0 ⊆ incidences original) (hcur : Tcur ⊆ T0)
    (hparent : ∀z∈T0,z.1∈parentLabels D R a (2^m) p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P=2)
    (Fraw Fcfg : ℤ → Matrix (Fin 1) (Fin 2) ℝ)
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (population PL PU : ℝ) (Qref : ℕ) (lambda Gcost Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin dRel → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata : HasThirdXYData (J:=J) (ell:=3) D zeta a m plane E Hgraph S0 T0 P hP
      (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda Gcost Cpre threshold L3 Rel)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ))
    (hkappa : extremalExponent ≤ 3)
    (Q : Finset Parent)
    (hQ : Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2^b)))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((source h R Eref a m p).line (representative hRef univ 0 (2^b) q)))
        (direction ((source h R Eref a m p).line (representative hRef univ 0 (2^b) q')))) :
    let K := xyConstant D.thickness zeta population PL PU lambda
      (Gcost*Cpre*(refinementCost (dRel+2) (J+1) L3:ℝ)) Qref
      (NativeSourceSizeBounds.radix S0.card L3) J m
    let C := NativeCoarseCellSource.source hRef 0 (level-m+6) b Q
      (representative hRef univ 0 (2^b)) (incidences (sourceCells D R Tcur a (2^m) p)) hsep
    ∀hC : IsWangZakharovNativeFiniteInput C etaC,
    (NativeSameQSourceRestriction.restrict D a m b p Q Tcur).Nonempty →
    let cells := actualRows h R Eref Tcur level m b p hRef Q
    let hp : (parentLabels D R a (2^m) p).Nonempty := card_pos.mp hRef.1.1
    ∃qOld : Parent,∃A : Finset (Fin n × Index),A ⊆ Tcur ∧ A.Nonempty ∧
      (∀z∈A,relativeLabel D a (2^m) p (2^b) z.1∈Q ∧
        relativeLabel D a (2^m) p (2^c) z.1=qOld) ∧
      let pA := zeroProjection qOld
      let Occ := occurrences h R a m b p hp Q cells A
      ∃B ⊆ Occ.image (rawTaggedKey C c pA),
        (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
        translatedTags D a m B ⊆ Occ.image (taggedKey D a m C c pA) ∧
        (∀v∈translatedTags D a m B,∀w∈translatedTags D a m B,
          finalTime v=finalTime w → v.1=w.1) ∧
        let Efinal := selectedPairs D a m C c pA Occ (translatedTags D a m B)
        Efinal.Nonempty ∧ Efinal ⊆ incidences cells ∧
        (∀z∈Efinal,z.1∈parentLabels C univ 0 (2^c) pA) ∧
        Efinal.image (localPair C 0 (2^c) pA)=B.image Prod.snd ∧
        let Sout := source hC univ Efinal 0 c pA
        ENNReal.ofReal ((source h R Eref a m p).thickness^(2*pExp)*normalization D m*
          ((NativeSameQSourceRestriction.restrict D a m b p Q Tcur).card:ℝ)/
          (4294967296*NativeRememberedSourceRealization.phaseConstant)) ≤ wzTotalShadingVolume Sout ∧
        volume (sourceUnion Sout) ≤ ENNReal.ofReal
          (NativeRememberedSourceUnion.unionConstant K*Sout.thickness^extremalExponent) := by
  intro K C hC hTQne cells hp
  have hTcur : Tcur ⊆ incidences original := hcur.trans hT0
  have hParentCur : ∀z∈Tcur,z.1∈parentLabels D R a (2^m) p := fun z hz => hparent z (hcur hz)
  obtain ⟨qOld,A,hATQ,hAne,hPhase,hMass⟩ := massive_old_phase h original R level hzeta HB Eref Tcur
    m b c (by omega) (by omega) p hRef hbudget hParentCur Q hTQne
  have hATcur : A ⊆ Tcur := hATQ.trans (filter_subset _ _)
  let pA := zeroProjection qOld
  let Occ := occurrences h R a m b p hp Q cells A
  obtain ⟨B,hBO,hRawCoherent,hBT,hCoherent,hEne,hEinc,hParentFinal,hImage,hShade⟩ :=
    select_raw_height_and_shading h original R Eref Tcur level m b c (by omega) (by omega)
      (by omega) hc6 HB p hp hRef hbudget hTcur hParentCur Q hQ hsep hC A hATcur hAne
      (fun z hz => (hPhase z hz).1) qOld (fun z hz => (hPhase z hz).2)
  let Efinal := selectedPairs D a m C c pA Occ (translatedTags D a m B)
  have hCthick : C.thickness=64/((2^b:ℕ):ℝ) := rfl
  have hR064 : 64 ≤ R0 := by
    have hrho : rho m=64*mu m := by unfold NativeReferenceXYGridPoints.mu; ring
    have hprod : mu m*64 ≤ mu m*(R0:ℝ) := by
      calc
        _ = rho m := by rw [hrho]; ring
        _ ≤ _ := hbase
    have hh : (64:ℝ) ≤ (R0:ℝ) := (mul_le_mul_iff_left₀ (mu_pos m)).mp
      (by simpa only [mul_comm] using hprod)
    exact_mod_cast hh
  let Rd : ℕ := 8*R0*2^(b0-b)
  have hRd512 : 512 ≤ Rd := by
    have hpw : 1 ≤ 2^(b0-b) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    dsimp only [Rd]
    nlinarith only [hR064,hpw]
  have hRdMesh : (Rd:ℝ)*mu m=512*C.thickness := by
    have hpow : ((2^b0:ℕ):ℝ)=((2^b:ℕ):ℝ)*((2^(b0-b):ℕ):ℝ) := by
      have hpw : (2:ℕ)^b0=2^b*2^(b0-b) := by
        calc
          _ = 2^(b+(b0-b)) := by congr 1; omega
          _ = _ := pow_add _ _ _
      exact_mod_cast hpw
    dsimp only [Rd]
    push_cast
    rw [show (8*(R0:ℝ)*(2:ℝ)^(b0-b))*mu m=8*(2:ℝ)^(b0-b)*(mu m*(R0:ℝ)) by ring,
      hmatch,hpow,hCthick]
    push_cast
    field_simp
    norm_num
  have hdw : 64/((2^b:ℕ):ℝ) ≤ 64/((2^c:ℕ):ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) (by omega : c ≤ b)
  have hquery : (Rd:ℝ)*mu m ≤ 64/((2^depth:ℕ):ℝ) := by
    rw [hRdMesh,hwidth,hCthick]
    exact mul_le_mul_of_nonneg_left hdw (by norm_num)
  have hsmall : 512*mu m ≤ 64/((2^depth:ℕ):ℝ) :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hRd512) (mu_pos m).le).trans hquery
  have hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale HB.2.1 ⟨m,by omega⟩
  have hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64 := by
    calc
      _ = ((2^(m+b):ℕ):ℝ)*D.thickness := by push_cast; rw [pow_add]; ring
      _ ≤ 1 := NativeCompactAncestorRegularity.dyadic_parent_scale HB.2.1 ⟨m+b,by omega⟩
      _ ≤ 64 := by norm_num
  have hSigma : ((2^c:ℕ):ℝ)*C.thickness/64 ≤ 1 := by
    rw [hCthick]
    have hpw : ((2^c:ℕ):ℝ) ≤ ((2^b:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) (by omega : c ≤ b)
    calc
      _ = ((2^c:ℕ):ℝ)/((2^b:ℕ):ℝ) := by ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr hpw
  have hCells : ∀i,C.shading i=wzCellShading (mesh C) cells i :=
    NativeIntermediateParentPopulation.intermediate_common_mesh hRef 0 (level-m+6) b Q
      (representative hRef univ 0 (2^b)) (incidences (sourceCells D R Tcur a (2^m) p)) hsep
  have hCommon := NativeIntermediateParentPopulation.intermediate_common_height hRef 0 (level-m+6) b Q
    (representative hRef univ 0 (2^b)) (incidences (sourceCells D R Tcur a (2^m) p)) hsep hC
  have hUnion := rank_three_union h original horiginal ha R Eref m level hm
    HB.2.1 hf hscale p hRef hRefK (level-m+6) b0 c depth hb0 (by omega) hdepth hwidth
    plane E Hgraph S0 T0 hT0 hparent P hP hd Fraw Fcfg hCfg population PL PU Qref lambda Gcost Cpre
    threshold L3 Rel Hdata R0 Rd hR0 (by omega) hbase hmatch.le hsmall hquery hkappa A
    (hATcur.trans hcur) qOld (fun z hz => (hPhase z hz).2) b hb hNscale hRelScale Q C hC cells
    hCells hCommon hCthick hRd512 hRdMesh pA hSigma (translatedTags D a m B) hBT hCoherent hParentFinal
  have hLower := phase_mass_payment hRef.1.2.1
    (by positivity : 0 < 64/((2^c:ℕ):ℝ)) hMass
  refine ⟨qOld,A,hATcur,hAne,hPhase,B,hBO,hRawCoherent,hBT,hCoherent,
    hEne,hEinc,hParentFinal,hImage,?_,hUnion⟩
  apply (ENNReal.ofReal_le_ofReal ?_).trans hShade
  simpa only [mul_assoc] using hLower

end NativeActualRawRankThreeSource
