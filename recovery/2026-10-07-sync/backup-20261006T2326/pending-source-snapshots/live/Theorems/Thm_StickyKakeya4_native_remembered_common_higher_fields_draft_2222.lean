import Theorems.Thm_StickyKakeya4_native_actual_higher_remembered_caller_construction_draft_2100

/- UNVERIFIED simultaneous actual-source higher fields.
The fields are chosen only after the literal source cells and retained
first-alignment common menu exist. All original-height witnesses, common
chart/meshes, scalar AD, and native-cell halos are read from that source.
The scalar exponent is allowed to vary inside the retained exponent bin.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeRememberedCommonHigherFieldsDraft2222
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeParentLabels
open NativeTranslatedGrainHeightOverlap NativeConfiguredThirdRelation NativeActualConfiguredPoint
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints CanonicalConfiguredE4Bridge
open NativeLiteralYHeightAlignment NativePaperAlignmentScales NativePackedHigherCapacityDraft2006
open NativeRememberedSourceMaps NativeRememberedHigherKeyFactoryDraft2032
open NativeRememberedAlignmentPatchDraft2036 NativeRememberedFinalTimeScalarDraft2054
open NativeFullYHaloCoverDraft2017 NativeOriginalCellChartGeometry

/-- Derive one common packed chart and all time-dependent higher fields on
the ACTUAL remembered source. No per-time field, full-Y cover, halo, or
normalized lower-quotient membership is supplied as an input. The equality
C=B-theta*A is retained together with every actual native-cell witness. -/
theorem actual_common_higher_fields {n : ℕ} {D : FiniteScaleSource n}
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
    (kept Ybase : Finset Key) (u bins : ℕ) (t zeta chi : ℝ) (hZeta : 0≤zeta)
    (hBaseEq : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u)
    (W : ∀height : {height : ℤ // height∈Ybase.image Prod.fst},
      HeightAlignment Ybase u t zeta chi height.val)
    (bin : ℝ → Fin (bins+1)) (menu : NativeYCommonScaleSelection.Menu u bins)
    (hCommon : ∀height∈kept.image Prod.fst,∃hh : height∈Ybase.image Prod.fst,
      (W ⟨height,hh⟩).chart=menu.1 ∧ (W ⟨height,hh⟩).rhoDepth=menu.2.1 ∧
      (W ⟨height,hh⟩).tauDepth=menu.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=menu.2.2.2 ∧
      heightPoints kept ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected)
    (hKey : ∀z∈A,coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2∈kept)
    (hTau : NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) menu.2.2.1.val=
      4096*(64/((2^c:ℕ):ℝ)))
    (hRho : C.thickness=8*NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) menu.2.1.val) :
    let sigma := ((2^c:ℕ):ℝ)*C.thickness/64
    let O := (NativePackedFrameIsometry.frame .oneTwo P hP hd).trans (normalChart menu.1)
    let cellsS := sourceCells C R
      (selectedPairs D a m C c pA (occurrences h backbone a m b p hp Q cells A) B) 0 (2^c) pA
    ∃(higherC higherF beta exponent : ℤ → ℝ) (Y : ℤ → Finset ℝ),
      ∀height∈(incidences cellsS).image (fun z => z.2 3),
        let M := chartRows menu.1 (Fcfg (oldHeight B height/((8*R0:ℕ):ℤ)))
        higherC height=M 1 0-higherF height*M 0 0 ∧
        |higherF height|≤1 ∧ |higherC height|≤1/2 ∧
        0≤exponent height ∧ exponent height≤min t 1 ∧ bin (exponent height)=menu.2.2.2 ∧
        (Y height).Nonempty ∧ (∀y∈Y height,|y|≤1) ∧
        FiniteVoronoiRealADCoarsening.ADBounds (Y height) (sigma/32768)
          ((sigma/32768)^(-zeta)) (t-exponent height) ∧
        (∀(i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index),
          k∈cellsS i → k 3=height → ∃y∈Y height,
            |packedQuotient O (higherC height) (higherF height) (cellCenter (sigma/2) k)-
              (512*y+beta height)|≤13*sigma) ∧
        ∀r : ℝ,sigma/2≤r → r≤1 →
          ((scalarGrid (timeCells cellsS height)
            (fun k => packedQuotient O (higherC height) (higherF height)
              (cellCenter (sigma/2) k)) r).card:ℝ)≤
            452*((sigma/32768)^(-zeta))^2*(r/512)^(-(t-exponent height)) ∧
          ∀(x : Fin 1 → ℝ) (radius : ℝ),r/512≤radius → radius≤1 →
            (((scalarGrid (timeCells cellsS height)
              (fun k => packedQuotient O (higherC height) (higherF height)
                (cellCenter (sigma/2) k)) r).filter
                  (fun k => dist (NativeQuotientGridCenters.center (r/512) k) x≤radius)).card:ℝ)≤
              452*((sigma/32768)^(-zeta))^2*58^(t-exponent height)*
                (radius/(r/512))^(t-exponent height) := by
  intro sigma O cellsS
  let times := (incidences cellsS).image (fun z => z.2 3)
  let matrix := fun height => chartRows menu.1 (Fcfg (oldHeight B height/((8*R0:ℕ):ℤ)))
  have hEach (height : ℤ) : ∃(theta beta s : ℝ) (Y : Finset ℝ),height∈times →
      |theta|≤1 ∧ |matrix height 1 0-theta*matrix height 0 0|≤1/2 ∧
      0≤s ∧ s≤min t 1 ∧ bin s=menu.2.2.2 ∧ Y.Nonempty ∧ (∀y∈Y,|y|≤1) ∧
      FiniteVoronoiRealADCoarsening.ADBounds Y (sigma/32768) ((sigma/32768)^(-zeta)) (t-s) ∧
      (∀(i : Fin (parentLabels C R 0 (2^c) pA).card) (k : Index),
        k∈cellsS i → k 3=height → ∃y∈Y,
          |packedQuotient O (matrix height 1 0-theta*matrix height 0 0) theta
            (cellCenter (sigma/2) k)-(512*y+beta)|≤13*sigma) ∧
      ∀r : ℝ,sigma/2≤r → r≤1 →
        ((scalarGrid (timeCells cellsS height)
          (fun k => packedQuotient O (matrix height 1 0-theta*matrix height 0 0) theta
            (cellCenter (sigma/2) k)) r).card:ℝ)≤452*((sigma/32768)^(-zeta))^2*(r/512)^(-(t-s)) ∧
        ∀(x : Fin 1 → ℝ) (radius : ℝ),r/512≤radius → radius≤1 →
          (((scalarGrid (timeCells cellsS height)
            (fun k => packedQuotient O (matrix height 1 0-theta*matrix height 0 0) theta
              (cellCenter (sigma/2) k)) r).filter
                (fun k => dist (NativeQuotientGridCenters.center (r/512) k) x≤radius)).card:ℝ)≤
            452*((sigma/32768)^(-zeta))^2*58^(t-s)*(radius/(r/512))^(t-s) := by
    by_cases ht : height∈times
    · obtain ⟨z,hz,hzt⟩ := mem_image.mp ht
      have hzCell : z.2∈cellsS z.1 := (mem_incidences cellsS z.1 z.2).mp hz
      obtain ⟨hh,hChart,hRhoDepth,hTauDepth,hBin,hSelected⟩ :=
        occupied_alignment_height h backbone a m b p hp Q C cells A c R pA B hB
          P hP hd F Fcfg R0 kept Ybase u bins t zeta chi W bin menu hCommon hKey
          height z.1 z.2 hzCell hzt
      let H := W ⟨oldHeight B height/((8*R0:ℕ):ℤ),hh⟩
      have hTauH : NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) H.tauDepth.val=
          4096*(64/((2^c:ℕ):ℝ)) := by rw [hTauDepth]; exact hTau
      have hRhoH : C.thickness=8*NativeDyadicTubeStopping.scale ((2:ℝ)⁻¹^u/512) H.rhoDepth.val := by
        rw [hRhoDepth]; exact hRho
      obtain ⟨theta,beta,Y,hTheta,hCoeff,hYn,hYbox,hYAD,hWitness,hCover⟩ :=
        actual_final_time_scalar_family h original horiginal ha backbone Eref T A m hm p hp hscale
          hS hSK levelS b c hb hc hNscale hRelScale Q C hC cells hcells haC hthickness hA hParent
          q hPhase P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch R pA B hB height z.1 z.2 hzCell hzt
          kept Ybase u t zeta chi hZeta hBaseEq H hSelected hKey hTauH hRhoH
      rw [hChart] at hCoeff hWitness hCover
      exact ⟨theta,beta,H.exponent,Y,fun _ =>
        ⟨hTheta,hCoeff,H.exponent_nonneg,H.exponent_upper,hBin,hYn,hYbox,hYAD,hWitness,hCover⟩⟩
    · exact ⟨0,0,0,∅,fun hBad => (ht hBad).elim⟩
  choose theta beta exponent Y hChosen using hEach
  refine ⟨(fun height => matrix height 1 0-theta height*matrix height 0 0),theta,beta,exponent,Y,?_⟩
  intro height ht
  exact ⟨rfl,hChosen height ht⟩

end NativeRememberedCommonHigherFieldsDraft2222
