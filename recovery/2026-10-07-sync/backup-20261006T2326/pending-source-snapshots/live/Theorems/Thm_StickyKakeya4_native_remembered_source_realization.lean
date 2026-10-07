import Theorems.Thm_StickyKakeya4_native_actual_massive_old_phase
import Theorems.Thm_StickyKakeya4_native_remembered_source_shading

/- UNVERIFIED simultaneous remembered-source realization. All source maps
below are the actual same-Q intermediate constructor and its literal local
parent source. Tcur supplies sparse rows; unchanged T0 supplies the full
reference slice AD. No final-source shading or union bound is an input. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

noncomputable section
namespace NativeRememberedSourceRealization
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeCoarseReadback
open NativeConfiguredIncidenceFibers NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open CanonicalConfiguredE4Bridge NativeRememberedSourceMaps NativeRememberedHeightSelection
open NativeRememberedOccurrenceReadback NativeRememberedFineCount NativeFineWeightedCoarseCore
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeCoarseSourceParentReadback
open NativeTranslatedGrainHeightOverlap NativeLocalCellCoherence NativeThirdXYData
open NativeReferenceXYGridField NativeSquaredGrainQueries NativeRetainedSliceCore
open NativeGrainQuotientFibers NativeFixedCompactKakeyaExponent
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

/-- The literal old relative-phase menu is bounded before the current
intercept projection. Its width is w=64/2^c. -/
def phaseConstant : ℝ := 373248*64^3

/-- Exact scalar payment of the massive-phase choice. -/
lemma massive_phase_payment {r eps w p G H : ℝ}
    (hr : 0 < r) (heps : 0 < eps) (hw : 0 < w)
    (hMass : H ≤ phaseConstant*r^(-p)/w^3*G) :
    r^(2*p)*eps^4*H/(65536*phaseConstant*fineCapacity) ≤
      r^p*eps^4*G/(65536*fineCapacity*w^3) := by
  have hp2 : r^(2*p)=r^p*r^p := by rw [←Real.rpow_add hr]; congr 1; ring
  have hCf := fineCapacity_pos
  have hC : 0 < phaseConstant := by norm_num [phaseConstant]
  calc
    _ = (r^(2*p)*eps^4/(65536*phaseConstant*fineCapacity))*H := by ring
    _ ≤ (r^(2*p)*eps^4/(65536*phaseConstant*fineCapacity))*
        (phaseConstant*r^(-p)/w^3*G) := mul_le_mul_of_nonneg_left hMass (by positivity)
    _ = _ := by
      rw [hp2,Real.rpow_neg hr.le]
      field_simp [hw.ne',hCf.ne',hC.ne',(Real.rpow_pos_of_pos hr p).ne']
      ring

/-- The advertised power form follows from the actual same-Q fine mass. -/
lemma power_payment {r eps p z H : ℝ} (hr : 0 < r)
    (hMass : r^(3*z)/2 ≤ eps^4*H) :
    r^(3*z+2*p)/(131072*phaseConstant*fineCapacity) ≤
      r^(2*p)*eps^4*H/(65536*phaseConstant*fineCapacity) := by
  have hCf := fineCapacity_pos
  have hC : 0 < phaseConstant := by norm_num [phaseConstant]
  have hh := mul_le_mul_of_nonneg_left hMass
    (show 0 ≤ r^(2*p)/(65536*phaseConstant*fineCapacity) by positivity)
  rw [Real.rpow_add hr]
  convert hh using 1 <;> ring

/-- One actual old phase and one actual old height per final time bin
produce simultaneous total-shading and union-volume bounds on the SAME S.
The fine mass is the original weighted selector's literal sum over Q.
The proof never asserts disjointness of old-phase geometric images. -/
theorem exists_same_Q_source {n dRel J : ℕ} {D : FiniteScaleSource n}
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
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (population PL PU : ℝ) (Qref : ℕ) (lambda Gcost Cpre threshold : ℝ) (L3 : ℕ)
    (Rel : Fin dRel → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata : HasThirdXYData (J:=J) (ell:=2) D zeta a m plane E Hgraph S0 T0 P hP
      (by norm_num) (by norm_num) hd Fraw p population PL PU Qref lambda Gcost Cpre threshold L3 Rel)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ))
    (Hsingle : ∀x∈T0,∀y∈T0,translatedHeight D a m x.2/((8*R0:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R0:ℕ):ℤ) → translatedHeight D a m x.2=translatedHeight D a m y.2)
    (hkappa : extremalExponent ≤ 3)
    (Q : Finset Parent)
    (hQ : Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2^b)))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((source h R Eref a m p).line (representative hRef univ 0 (2^b) q)))
        (direction ((source h R Eref a m p).line (representative hRef univ 0 (2^b) q')))) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    let cfg := NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0
    let K := xyConstant D.thickness zeta population PL PU lambda
      (Gcost*Cpre*(refinementCost (dRel+2) (J+1) L3:ℝ)) Qref
      (NativeSourceSizeBounds.radix S0.card L3) J m
    let C := NativeCoarseCellSource.source hRef 0 (level-m+6) b Q
      (representative hRef univ 0 (2^b)) (incidences (sourceCells D R Tcur a (2^m) p)) hsep
    ∀hC : IsWangZakharovNativeFiniteInput C etaC,
    (∀x∈T0.image (fun z => cfg z.2),∀y∈T0.image (fun z => cfg z.2),x≠y →
      64/((2^b0:ℕ):ℝ) ≤ dist x y) →
    let WQ := ∑q∈Q,NativeSameQFineGraph.weight h R Eref a m b0 b p hRef cfg Tcur q
    0 < WQ →
    let cells := actualRows h R Eref Tcur level m b p hRef Q
    let hp : (parentLabels D R a (2^m) p).Nonempty := card_pos.mp hRef.1.1
    ∃qOld : Parent,∃A : Finset (Fin n × Index),A ⊆ Tcur ∧ A.Nonempty ∧
      (∀z∈A,relativeLabel D a (2^m) p (2^b) z.1∈Q ∧
        relativeLabel D a (2^m) p (2^c) z.1=qOld) ∧
      let pA := zeroProjection qOld
      let Occ := occurrences h R a m b p hp Q cells A
      ∃B ⊆ Occ.image (taggedKey D a m C c pA),
        (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
        let Efinal := selectedPairs D a m C c pA Occ B
        Efinal.Nonempty ∧ Efinal ⊆ incidences cells ∧
        (∀z∈Efinal,z.1∈parentLabels C univ 0 (2^c) pA) ∧
        let Sout := source hC univ Efinal 0 c pA
        ENNReal.ofReal ((source h R Eref a m p).thickness^(2*pExp)*
          (64/((2^b0:ℕ):ℝ))^4*WQ/(65536*phaseConstant*fineCapacity)) ≤ wzTotalShadingVolume Sout ∧
        volume (sourceUnion Sout) ≤ ENNReal.ofReal
          (NativeRememberedSourceUnion.unionConstant K*Sout.thickness^extremalExponent) := by
  intro Sq F cfg K C hC hpointSep WQ hWQ cells hp
  have hTcur : Tcur ⊆ incidences original := hcur.trans hT0
  have hParentCur : ∀z∈Tcur,z.1∈parentLabels D R a (2^m) p := fun z hz => hparent z (hcur hz)
  have hCopy := Hdata
  rcases hCopy with ⟨_hTS,_hTn,_hCost,_hTH,_hFinal,_hExtra,_hOld,_hXY,_hClass,
    _hGrain,_hKey,_hThreshold,_hRet,_Hxy,_hRead,hNorm⟩
  have hF : ∀t i j,|F t i j| ≤ 1/4 := by
    intro t i j
    simpa only [Real.norm_eq_abs] using (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1/4)).mp (hNorm t) i j
  obtain ⟨qOld,_hqOld,hAne,_hATQ,hATcur,_hAorig,hPhase,_hGne,_hGraph,_hGPhase,_hGCard,hMass⟩ :=
    NativeActualMassiveOldPhase.from_original_reference_same_Q h original R level hzeta HB Eref Tcur
      m b0 b c (by omega) (by omega) (by omega) hb p hRef hbudget hTcur hParentCur cfg Q hWQ
  let A := (NativeSameQSourceRestriction.restrict D a m b p Q Tcur).filter
    (fun z => relativeLabel D a (2^m) p (2^c) z.1=qOld)
  let pA := zeroProjection qOld
  let Occ := occurrences h R a m b p hp Q cells A
  obtain ⟨B,hBO,hCoherent,hEne,hEinc,hParentFinal,hImage,hShade⟩ :=
    NativeRememberedSourceShading.select_height_and_shading h original horiginal ha R Eref Tcur
      level m b0 b c (by omega) hb0 hb (by omega) hc6 HB hmb0 hscale p hp hRef hbudget hTcur hParentCur
      .oneTwo P hP hd F Fcfg hF hCfg R0 hR0 hbase hmatch
      (fun x hx y hy he => Hsingle x (hcur hx) y (hcur hy) he) Q hQ hsep hC
      (fun x hx y hy hxy => hpointSep x (image_subset_image hcur hx) y (image_subset_image hcur hy) hxy)
      A hATcur hAne (fun z hz => (hPhase z hz).1) qOld (fun z hz => (hPhase z hz).2)
  let Efinal := selectedPairs D a m C c pA Occ B
  have hCthick : C.thickness=64/((2^b:ℕ):ℝ) := rfl
  have hR064 : 64 ≤ R0 := by
    have hrho : rho m=64*mu m := by unfold NativeReferenceXYGridPoints.mu; ring
    have hh : (64:ℝ) ≤ (R0:ℝ) := (mul_le_mul_iff_left₀ (mu_pos m)).mp
      (by rw [mul_comm,←hrho]; exact hbase)
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
  have hUnion := NativeRememberedSourceUnion.rank_two_union h original horiginal ha R Eref m level hm
    HB.2.1 hf hscale p hRef hRefK (level-m+6) b0 c depth hb0 (by omega) hdepth hwidth
    plane E Hgraph S0 T0 hT0 hparent P hP hd Fraw Fcfg hCfg population PL PU Qref lambda Gcost Cpre
    threshold L3 Rel Hdata R0 Rd hR0 (by omega) hbase hmatch.le hsmall hquery hkappa A
    (hATcur.trans hcur) qOld (fun z hz => (hPhase z hz).2) b hb hNscale hRelScale Q C hC cells
    hCells hCommon hCthick hRd512 hRdMesh pA hSigma B hBO hCoherent hParentFinal
  have hPhasePaid : WQ ≤ phaseConstant*(source h R Eref a m p).thickness^(-pExp)/
      (64/((2^c:ℕ):ℝ))^3*((NativeSameQFineGraph.graph h R Eref a m b0 p hRef cfg A).card:ℝ) := by
    convert hMass using 1 <;> dsimp only [phaseConstant] <;> field_simp <;> ring
  have hLower := massive_phase_payment hRef.1.2.1
    (by positivity : 0 < 64/((2^b0:ℕ):ℝ)) (by positivity : 0 < 64/((2^c:ℕ):ℝ)) hPhasePaid
  refine ⟨qOld,A,hATcur,hAne,hPhase,B,hBO,hCoherent,hEne,hEinc,hParentFinal,?_,hUnion⟩
  exact (ENNReal.ofReal_le_ofReal hLower).trans hShade

end NativeRememberedSourceRealization
