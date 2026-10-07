import Theorems.Thm_StickyKakeya4_native_actual_raw_whole_Y_total
import Theorems.Thm_StickyKakeya4_native_actual_raw_remembered_source
import Theorems.Thm_StickyKakeya4_native_remembered_source_admission
import Theorems.Thm_StickyKakeya4_native_fine_weighted_coarse_cutoff
import Theorems.Thm_StickyKakeya4_native_local_admission_budget

/- UNVERIFIED actual two-output native source caller. All cutoffs precede
D. The prescribed same-E1 frontend supplies etaRef and pExp below the
fixed window*chi*E/8192 threshold. The actual raw whole-Y supplier chooses
Tcur; this file then chooses Q,
constructs its native C, and admits the exact remembered Sout. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualRawNativeRealization
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeMiddleWindowBalance NativeRelativeParentLabels NativeRelativeCoarseReadback
open NativeRememberedSourceMaps NativeRememberedOccurrenceReadback NativeRawHeightSourceAdapter
open NativeActualRawWeightSource NativeActualRawRememberedSource NativeRememberedSourceRealization
open NativeFineWeightedCoarseCutoff NativeEffectiveOutputThreshold NativeFineWeightedCoarseCore
open NativeCoarseDirectionThinning NativeCoarseSourceParentReadback NativeLocalCellCoherence
open NativeReferenceXYGridPoints NativeReferenceXYGridField NativeHorizontalGrainSlice
open NativeThirdXYData NativeThirdXYSourceData NativeRetainedSliceCore NativeSquaredGrainQueries
open NativeGrainQuotientFibers NativeFixedCompactKakeyaExponent NativeOriginalPrunedMass
open NativeCommonYTotalBudget NativeYCommonScaleSelection NativeConfiguredThirdRelation
open NativeTranslatedGrainHeightOverlap CanonicalConfiguredE4Bridge
open scoped BigOperators ENNReal

/-- Actual absolute 8rho tube depth selected by the planar menu. -/
def absoluteDepth {u bins : ℕ} (menu : Menu u bins) : ℕ := u+12-menu.2.1.val

/-- Actual old tau/4096 phase-parent depth. -/
def parentDepth {u bins : ℕ} (menu : Menu u bins) : ℕ := u+27-menu.2.2.1.val

/-- Literal first-chart physical depth for the old phase footprint. -/
def footprintDepth {u bins : ℕ} (menu : Menu u bins) : ℕ := parentDepth menu-9

/-- A small final relative thickness supplies the integer depth guard
needed by the actual local source; no compatible-depth certificate is input. -/
theorem menu_depth_readback {u bins : ℕ} (menu : Menu u bins)
    (hs : localSigma menu ≤ 1/64) :
    24 ≤ absoluteDepth menu ∧ absoluteDepth menu ≤ u+12 ∧
    18 ≤ parentDepth menu ∧ parentDepth menu ≤ absoluteDepth menu-6 ∧
    9 ≤ footprintDepth menu ∧
    64/((2^(footprintDepth menu):ℕ):ℝ)=512*(64/((2^(parentDepth menu):ℕ):ℝ)) ∧
    (((2^(parentDepth menu):ℕ):ℝ)*(64/((2^(absoluteDepth menu):ℕ):ℝ)))/64=localSigma menu ∧
    64/((2^(absoluteDepth menu):ℕ):ℝ)=8*((2:ℝ)⁻¹^u/512*(2:ℝ)^menu.2.1.val) ∧
    64/((2^(parentDepth menu):ℕ):ℝ)=((2:ℝ)⁻¹^u/512*(2:ℝ)^menu.2.2.1.val)/4096 := by
  let jr := menu.2.1.val
  let jt := menu.2.2.1.val
  have hjr : jr ≤ u+9 := by have hh := menu.2.1.isLt; dsimp only [jr]; omega
  have hjt : jt ≤ u+9 := by have hh := menu.2.2.1.isLt; dsimp only [jt]; omega
  have htwo : (0:ℝ) < (2:ℝ)^jt := by positivity
  have hprod : (2:ℝ)^(jr+21) ≤ (2:ℝ)^jt := by
    have hh := (le_div_iff₀ (by norm_num : (0:ℝ)<64)).mp hs
    change (32768*((2:ℝ)^jr/(2:ℝ)^jt))*64 ≤ 1 at hh
    have hh' := mul_le_mul_of_nonneg_right hh htwo.le
    field_simp [htwo.ne'] at hh'
    rw [pow_add]
    norm_num
    nlinarith only [hh']
  have hgap : jr+21 ≤ jt := by
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1<(2:ℕ))).mp (by exact_mod_cast hprod)
  have hb : 24 ≤ absoluteDepth menu := by dsimp [absoluteDepth]; dsimp only [jr,jt] at *; omega
  have hbb : absoluteDepth menu ≤ u+12 := Nat.sub_le _ _
  have hc : 18 ≤ parentDepth menu := by dsimp [parentDepth]; dsimp only [jt] at *; omega
  have hcb : parentDepth menu ≤ absoluteDepth menu-6 := by
    dsimp [parentDepth,absoluteDepth]; dsimp only [jr,jt] at *; omega
  have hp : 9 ≤ footprintDepth menu := by dsimp [footprintDepth]; omega
  have hbj : absoluteDepth menu+jr=u+12 := by dsimp [absoluteDepth]; dsimp only [jr] at *; omega
  have hct : parentDepth menu+jt=u+27 := by dsimp [parentDepth]; dsimp only [jt] at *; omega
  have hbpow : (2:ℝ)^(absoluteDepth menu)*(2:ℝ)^jr=(2:ℝ)^(u+12) := by rw [←pow_add,hbj]
  have hcpow : (2:ℝ)^(parentDepth menu)*(2:ℝ)^jt=32768*(2:ℝ)^(u+12) := by
    rw [←pow_add,hct,show u+27=(u+12)+15 by omega,pow_add]
    norm_num
    ring
  have hcp : parentDepth menu=footprintDepth menu+9 := by dsimp [footprintDepth]; omega
  refine ⟨hb,hbb,hc,hcb,hp,?_,?_,?_,?_⟩
  · simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [hcp,pow_add]
    norm_num
    field_simp
  · simp only [Nat.cast_pow,Nat.cast_ofNat]
    unfold localSigma
    change ((2:ℝ)^(parentDepth menu)*(64/(2:ℝ)^(absoluteDepth menu)))/64=
      32768*((2:ℝ)^jr/(2:ℝ)^jt)
    field_simp
    nlinarith only [hbpow,hcpow]
  · simp only [Nat.cast_pow,Nat.cast_ofNat,inv_pow]
    have hh : (2:ℝ)^(absoluteDepth menu)*(2:ℝ)^jr=4096*(2:ℝ)^u := by
      rw [hbpow,pow_add]; norm_num; ring
    field_simp
    nlinarith only [hh]
  · simp only [Nat.cast_pow,Nat.cast_ofNat,inv_pow]
    have hh : (2:ℝ)^(parentDepth menu)*(2:ℝ)^jt=134217728*(2:ℝ)^u := by
      rw [hcpow,pow_add]; norm_num; ring
    field_simp
    nlinarith only [hh]

/-- One fixed final-scale cutoff pays the exact AD, CW and raw-shading
constants before D. The CW target is etaA+z2, hence17E/256. -/
theorem exists_final_native_cutoff (E : ℝ) (hE : 0 < E) :
    ∃sigma0 : ℝ,0 < sigma0 ∧ sigma0 ≤ 1/64 ∧
      ∀sigma : ℝ,0 < sigma → sigma ≤ sigma0 →
        (2048:ℝ)^3*sigma^(E/8) ≤ sigma^(E/16) ∧
        (373248*512^4:ℝ)*sigma^(E/8) ≤ sigma^(17*E/256) ∧
        volumeConstant*(5832/64^3)*sigma^(E/8) ≤
          sigma^(5*E/4096)/(8589934592*phaseConstant) := by
  let C : ℝ := (2048:ℝ)^3+(373248*512^4:ℝ)+
    volumeConstant*(5832/64^3)*(8589934592*phaseConstant)
  have hV := volumeConstant_pos
  have hPhase : 0 < phaseConstant := by norm_num [phaseConstant]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hDen : 0 ≤ volumeConstant*(5832/64^3)*(8589934592*phaseConstant) := by positivity
  obtain ⟨s0,hs0,_hs01,H⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < E/32 by positivity) hC (by norm_num : (0:ℝ)<1)
  refine ⟨min s0 (1/64:ℝ),lt_min hs0 (by norm_num),min_le_right _ _,?_⟩
  intro sigma hs hsmall
  have hs1 : sigma ≤ 1 := (hsmall.trans (min_le_right _ _)).trans (by norm_num)
  have hpay := H sigma hs (hsmall.trans (min_le_left _ _))
  have hpayPart (v : ℝ) (hv : v ≤ C) : v*sigma^(E/32) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hs.le _)).trans hpay
  refine ⟨NativeLocalAdmissionBudget.pay_power hs hs1
    (hpayPart _ (by dsimp only [C]; nlinarith only [hDen])) (by linarith),
    NativeLocalAdmissionBudget.pay_power hs hs1
      (hpayPart _ (by dsimp only [C]; nlinarith only [hDen])) (by linarith),?_⟩
  have hh := NativeLocalAdmissionBudget.pay_power (total:=E/8) (target:=5*E/4096) hs hs1
    (hpayPart (volumeConstant*(5832/64^3)*(8589934592*phaseConstant))
      (by dsimp only [C]; linarith)) (by linarith)
  apply (le_div_iff₀ (show 0 < (8589934592:ℝ)*phaseConstant by positivity)).mpr
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

/-- The post-Q raw mass is the actual selector output; it pays the common
source's shading lower at sigma, with the effective exponent unchanged. -/
lemma actual_lower_payment {r sigma p z E mass : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hpz : p ≤ z)
    (hread : r^(5*z)=sigma^(5*E/4096)) (hmass : r^(3*z)/2 ≤ mass) :
    sigma^(5*E/4096)/(8589934592*phaseConstant) ≤
      r^(2*p)*mass/(4294967296*phaseConstant) := by
  have hPhase : 0 < phaseConstant := by norm_num [phaseConstant]
  rw [←hread]
  calc
    _ ≤ r^(3*z+2*p)/(8589934592*phaseConstant) :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)) (by positivity)
    _ = (r^(2*p)/(4294967296*phaseConstant))*(r^(3*z)/2) := by rw [Real.rpow_add hr]; ring
    _ ≤ (r^(2*p)/(4294967296*phaseConstant))*mass :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

/-- Internal stage composition after the genuine raw whole-Y producer.
The final public supplier below derives this raw mass premise itself.
In particular, intermediate C and final Sout native admission are outputs. -/
theorem exists_raw_source_cutoff (Eout widthWindow : ℝ)
    (hEout : 0 < Eout) (hWindowPos : 0 < widthWindow) :
    ∃rCut : ℝ,0 < rCut ∧
    ∀{n dRel J : ℕ} {D : FiniteScaleSource n}
    {eta etaS a zeta pExp : ℝ}
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
    (hRefSmall : (source h R Eref a m p).thickness ≤ rCut)
    (hetaRef : etaS ≤ widthWindow*Eout/4096)
    (hpExp : 0 ≤ pExp) (hpMin : pExp ≤ widthWindow*Eout/4096)
    (hwidth : 64/((2^depth:ℕ):ℝ)=512*(64/((2^c:ℕ):ℝ)))
    (plane : Index → Submodule ℝ E4) (E Hgraph S0 T0 Tcur : Finset (Fin n × Index))
    (hT0 : T0 ⊆ incidences original) (hcur : Tcur ⊆ T0)
    (hEref : Eref ⊆ incidences original) (hTref : T0 ⊆ Eref)
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
    (hkappa : extremalExponent ≤ 3),
    let sigma := (((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ)))/64
    sigma ≤ (source h R Eref a m p).thickness^widthWindow →
    sigma^(Eout/4096) ≤ normalization D m*(Tcur.card:ℝ) →
    let z := exponent (source h R Eref a m p).thickness sigma (Eout/256)
    let etaA := exponent (64/((2^b:ℕ):ℝ)) sigma (Eout/16)
    let K := xyConstant D.thickness zeta population PL PU lambda
      (Gcost*Cpre*(refinementCost (dRel+2) (J+1) L3:ℝ)) Qref
      (NativeSourceSizeBounds.radix S0.card L3) J m
    ∃(Q : Finset Parent)
      (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
        dist (direction ((source h R Eref a m p).line (representative hRef univ 0 (2^b) q)))
          (direction ((source h R Eref a m p).line (representative hRef univ 0 (2^b) q')))),
      Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
        (parentLabel (source h R Eref a m p) 0 (2^b)) ∧ Q.Nonempty ∧
      let C := NativeCoarseCellSource.source hRef 0 (level-m+6) b Q
        (representative hRef univ 0 (2^b)) (incidences (sourceCells D R Tcur a (2^m) p)) hsep
      ∃hC : IsWangZakharovNativeFiniteInput C etaA,
      let cells := actualRows h R Eref Tcur level m b p hRef Q
      let hp : (parentLabels D R a (2^m) p).Nonempty := card_pos.mp hRef.1.1
      ∃qOld : Parent,∃A : Finset (Fin n × Index),A ⊆ Tcur ∧ A.Nonempty ∧
        (∀v∈A,relativeLabel D a (2^m) p (2^b) v.1∈Q ∧
          relativeLabel D a (2^m) p (2^c) v.1=qOld) ∧
        let pA := zeroProjection qOld
        let Occ := occurrences h R a m b p hp Q cells A
        ∃B ⊆ Occ.image (rawTaggedKey C c pA),
          (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
          translatedTags D a m B ⊆ Occ.image (taggedKey D a m C c pA) ∧
          (∀v∈translatedTags D a m B,∀w∈translatedTags D a m B,
            finalTime v=finalTime w → v.1=w.1) ∧
          let Efinal := selectedPairs D a m C c pA Occ (translatedTags D a m B)
          Efinal.Nonempty ∧ Efinal ⊆ incidences cells ∧
          (∀v∈Efinal,v.1∈parentLabels C univ 0 (2^c) pA) ∧
          Efinal.image (localPair C 0 (2^c) pA)=B.image Prod.snd ∧
          let Sout := source hC univ Efinal 0 c pA
          IsWangZakharovNativeFiniteInput Sout (Eout/8) ∧
          (∀i,Sout.line i∈NativeUnitParentNormalization.fixedCompactClass) ∧
          NativeActualLocalAdmission.HasExactTrace hC univ Efinal 0 c pA ∧
          Sout.thickness=sigma ∧
          ENNReal.ofReal (sigma^(5*Eout/4096)/(8589934592*phaseConstant)) ≤ wzTotalShadingVolume Sout ∧
          volume (sourceUnion Sout) ≤ ENNReal.ofReal
            (NativeRememberedSourceUnion.unionConstant K*sigma^extremalExponent) := by
  obtain ⟨sigma0,hsigma0,hsigma064,Hfinal⟩ := exists_final_native_cutoff Eout hEout
  obtain ⟨rCut,hrCut,_hrCut8,Hcut⟩ := exists_two_output_cutoff hWindowPos hEout
    (1/64) sigma0 (by norm_num) hsigma0
  refine ⟨rCut,hrCut,?_⟩
  intro n dRel J D eta etaS a zeta pExp h original horiginal ha R Eref level m b0 b c depth
    hm hb0 hb hc hc6 hdepth hzeta HB hmb0 hf hscale p hRef hRefK hbudget
    hRefSmall hetaRef hpExp hpMin hwidth plane E Hgraph S0 T0 Tcur hT0 hcur hEref hTref
    hparent P hP hd Fraw Fcfg hCfg population PL PU Qref lambda Gcost Cpre threshold L3 Rel Hdata
    R0 hR0 hbase hmatch hkappa sigma hWindow hRaw z etaA K
  let r := (source h R Eref a m p).thickness
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let z2 := exponent d sigma Eout
  have hr : 0 < r := hRef.1.2.1
  have hdpos : 0 < d := by dsimp only [d]; positivity
  have hmb : m+b ≤ level := by omega
  have hguard := NativeSameReferenceChartBounds.source_scale_guard (a:=a) h R Eref level m b p HB.2.1 hmb
  have hrd : r ≤ d := by
    apply (le_div_iff₀ (show (0:ℝ)<((2^b:ℕ):ℝ) by positivity)).mpr
    change ((2^b:ℕ):ℝ)*r ≤ 1 at hguard
    linarith only [hguard]
  have hds : d ≤ sigma := by
    have hnc : (64:ℝ) ≤ ((2^c:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hc6
    change d ≤ ((2^c:ℕ):ℝ)*d/64
    nlinarith only [mul_le_mul_of_nonneg_right hnc hdpos.le]
  have hdy : r=(2:ℝ)⁻¹^(level-m+6) :=
    NativeRelativeCoarseReadback.local_source_dyadic h R Eref a level m p HB.2.1 (by omega)
  obtain ⟨_hdSmall,hsSmall,hs1,hcolor,hprune,hshadeCost,hupper,hdensity,hcw⟩ :=
    Hcut r d sigma etaS (level-m+6) b hr hRefSmall hdy (by omega) hrd hds hWindow hetaRef
  have hparams := ordered_two_output_parameters hr hrd hds hs1 hWindowPos hEout hWindow
  obtain ⟨_hWinD,hzMin,hetaA,hetaAupper,hz2Min,hratio,hA,h8,h5,h2,hpowerA,_hMassPower⟩ := hparams
  have hpz : pExp ≤ z := hpMin.trans hzMin
  have hr1 : r < 1 := hrd.trans_lt (hds.trans_lt hs1)
  have hs : 0 < sigma := hr.trans_le (hrd.trans hds)
  have hzread : r^z=sigma^(Eout/4096) := by
    have hh := NativeEffectiveOutputThreshold.power_readback hr hr1 hs (Eout/256) 1
    simpa only [one_mul,show Eout/256/16=Eout/4096 by ring] using hh
  have htotal : r^z ≤ normalization D m*(Tcur.card:ℝ) := by rw [hzread]; exact hRaw
  have hParentCur : ∀v∈Tcur,v.1∈parentLabels D R a (2^m) p := fun v hv => hparent v (hcur hv)
  obtain ⟨Q,hsep,hQP,hQne,hrep,hterminal,hC,hCthick,_hCompact,_hShadeC,_hret,hMassQ,_hUniversal⟩ :=
    NativeActualRawWeightSource.exists_same_Q_source (e:=etaA) h original R level HB Eref Tcur hEref
      (hcur.trans hTref) m b (by omega) (by omega) hmb p hRef hParentCur hpExp hpz
      htotal hbudget hcolor hprune hshadeCost hpowerA hupper hdensity hcw
  let C := NativeCoarseCellSource.source hRef 0 (level-m+6) b Q
    (representative hRef univ 0 (2^b)) (incidences (sourceCells D R Tcur a (2^m) p)) hsep
  let TQ := NativeSameQSourceRestriction.restrict D a m b p Q Tcur
  have hTQne : TQ.Nonempty := by
    by_contra hh
    have hzero : TQ=∅ := not_nonempty_iff_eq_empty.mp hh
    have hpos : 0 < r^(3*z)/2 := by positivity
    have hn : r^(3*z)/2 ≤ 0 := by
      simpa only [hzero,card_empty,Nat.cast_zero,mul_zero] using hMassQ
    exact (not_lt_of_ge hn) hpos
  obtain ⟨qOld,A,hAT,hAne,hPhase,B,hBO,hRawCoherent,hBT,hCoherent,hEne,hEinc,hParentFinal,hImage,hShade,hUnion⟩ :=
    NativeActualRawRememberedSource.exists_same_Q_source h original horiginal ha R Eref level m b0 b c depth
      hm hb0 hb hc hc6 hdepth hzeta HB hmb0 hf hscale p hRef hRefK hbudget hwidth plane E Hgraph S0 T0 Tcur
      hT0 hcur hparent P hP hd Fraw Fcfg hCfg population PL PU Qref lambda Gcost Cpre threshold L3 Rel Hdata
      R0 hR0 hbase hmatch hkappa Q hQP hsep hC hTQne
  let cells := actualRows h R Eref Tcur level m b p hRef Q
  let hp : (parentLabels D R a (2^m) p).Nonempty := card_pos.mp hRef.1.1
  let pA := zeroProjection qOld
  let Occ := occurrences h R a m b p hp Q cells A
  let Efinal := selectedPairs D a m C c pA Occ (translatedTags D a m B)
  let L := r^(2*pExp)*(normalization D m*(TQ.card:ℝ))/(4294967296*phaseConstant)
  have hLower : sigma^(5*Eout/4096)/(8589934592*phaseConstant) ≤ L :=
    actual_lower_payment hr hr1.le hpz h5 hMassQ
  have hL : 0 ≤ L := by
    dsimp only [L]
    have hnu : 0 ≤ normalization D m := by
      unfold normalization
      have hh := h.1.2.1
      positivity
    have hphase : 0 < phaseConstant := by norm_num [phaseConstant]
    positivity
  have hShadeL : ENNReal.ofReal L ≤ wzTotalShadingVolume (source hC univ Efinal 0 c pA) := by
    simpa only [L,mul_assoc] using hShade
  have hbudgets := Hfinal sigma hs hsSmall
  have hpower2 : d^z2 ≤ r^(8*z) := by
    rw [h2,h8]
    exact Real.rpow_le_rpow_of_exponent_ge hs hs1.le (by linarith)
  have hCWread : d^(etaA+z2)=sigma^(17*Eout/256) := by
    rw [Real.rpow_add hdpos,hA,h2,←Real.rpow_add hs]
    congr 1
    ring
  have hFinal := NativeRememberedSourceAdmission.native_of_selected_shading hRef 0 (level-m+6) b Q
    (representative hRef univ 0 (2^b)) (incidences (sourceCells D R Tcur a (2^m) p)) hsep
    (by omega) (show 0 ≤ z2 from (by have hh : 0 < widthWindow*Eout/16 := by positivity; linarith))
    hC hrep hterminal hpower2 Efinal hEne hEinc c hc pA hParentFinal hL hShadeL
    (by rw [h2]; exact hbudgets.1) (by rw [hCWread]; exact hbudgets.2.1)
    (hbudgets.2.2.trans hLower)
  refine ⟨Q,hsep,hQP,hQne,hC,qOld,A,hAT,hAne,hPhase,B,hBO,hRawCoherent,hBT,hCoherent,
    hEne,hEinc,hParentFinal,hImage,hFinal.1,hFinal.2.1,hFinal.2.2,rfl,?_,hUnion⟩
  exact (ENNReal.ofReal_le_ofReal hLower).trans hShadeL

open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeActualPaidPlanarAlignment NativeActualYEpsilonTotalMass NativeActualBaselineRetentionPayment
open NativePaidThirdRecordReadback NativePaidThirdRecord NativePaidThirdBudget NativeThirdXYSourceData
open NativeRetainedSliceCore NativeRetainedSliceBudgetAlgebra NativeReferenceSliceBudgetAlgebra
open NativeActualNewCutBudget NativeNewCutOutputBudget NativeFinestYOutputBudget
open NativeReferenceXYGridPoints NativeReferenceXYGridField NativeReferenceXYGridMaps
open NativeHorizontalGrainSlice NativeGrainQuotientFibers NativeTranslatedGrainHeightOverlap
open NativeEncodedQuotientAD NativeFixedCompactKakeyaExponent NativeRankExponentHierarchy
open NativeParentHeightGraphCore NativeActivePhasePopulation NativeAllTwoScaleConfiguration
open NativeSingleHeightCoarseYAD NativeLiteralYHeightAlignment NativeConfiguredThirdRelation
open NativeActualSparseReferenceAdmission NativeLocalParentSource NativeOriginalParentDensityCore
open NativeMiddleWindowBalance NativeCubicalIncidenceCounts
open NativeWholeYGraphRetention NativeConfiguredIncidenceFibers NativeCommonYTotalBudget SelfUniform
open NativeSharpXPowerAlgebra NativeSquaredGrainQueries NativeThirdXYData
open scoped BigOperators Matrix.Norms.Elementwise

open NativeActualRawYTotalMass


/-- Actual one-T raw supplier followed by the literal two-output native
construction. No post-Y mass, intermediate C admission, final source
admission, or final shading bound is a premise of this endpoint. -/
theorem exists_actual_native_source (totalLoss zeta53 chi window eB menuTax eta0 c epsilonQ : ℝ)
    (hLossTotal : 0 < totalLoss) (hzetaSmall : zeta53 ≤ totalLoss/16384)
    (hchi : 0 < chi) (hw : 0 < window) (heB : 0 < eB) (hMenuTax : 0 < menuTax)
    (he0 : 0 < eta0) (he01 : eta0 ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1)
    (heQ : 0 < epsilonQ) (heQ1 : epsilonQ ≤ 1) (heQSmall : eta0 ≤ epsilonQ) (hcQ : c ≤ epsilonQ/24)
    (hTax : 5*eB/16+2*(commonBudget eta0 c/4)/window+menuTax ≤ (chi/2)*(totalLoss/16384))
    (Kcoh Ksupport g K bins : ℕ) (meshConstant row : ℝ) (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row)
    (pExp : ℝ) (hpExp : 0 ≤ pExp) (hpMin : pExp ≤ window*chi*totalLoss/8192) :
    ∃epsCut rCut : ℝ,0 < epsCut ∧ epsCut ≤ 1 ∧ 0 < rCut ∧
    ∀ {epsilon delta0 : ℝ} {dExtra J L3 n : ℕ}
    {D : FiniteScaleSource n} {eta : ℝ}
    (Hbudget : HasBudget epsilon eta0 c g K (dExtra+3) J L3 delta0)
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ delta0) (heta : 0 ≤ eta)
    (original : Fin n → Finset Index) (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (S : Finset (Fin n × Index)) (hS : S⊆incidences original) (hSn : S.Nonempty)
    (F1 F2 G Q1 Q2 m : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hQ2 : 0 < Q2)
    (hGF : G ≤ F2) (hm12 : 12 ≤ m) 
    (zeta lambda b tau seed c2 r q : ℝ)
    (hetaSeed : eta ≤ seed/8) (htau0 : 0 ≤ tau) (htau : tau ≤ commonBudget eta0 c/1024)
    (hseed : seed ≤ tau/16384) (hc2 : c2=commonBudget eta0 c/4)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (hr : 0 < r) (hr1 : r ≤ 1) (hrdelta : r ≤ D.thickness^(cutoff c (1:Fin 4)))
    (hlambda : lambda=r^(rankLoss eta0 c (1:Fin 4))/(4*((g:ℝ)+1)))
    (hb : r^((2*((2:ℕ):ℝ)+1)*rankLoss eta0 c (1:Fin 4)) ≤ b)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hqraw : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hscale : ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r)
    (Cpre : ℝ) (hCpre : 0 < Cpre)
    (a : ℝ) (plane : Index → Submodule ℝ E4) (E Hgraph T : Finset (Fin n × Index))
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hdim : Module.finrank ℝ P=2-1)
    (Fraw : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (p : Parent) (t : ℝ) (Rel3 : Fin (dExtra+3) → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata :
      let F3 := refinementCost ((dExtra+3)+2) (J+1) L3
      let Q3 := NativeSourceSizeBounds.radix S.card L3
      let w := min (boundaryWindow tau) ((tau/16)/1000)
      let pop := population D.thickness eta lambda b F1 G
      let eps := columnEpsilon D.thickness lambda (seed/8) c2
      let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2 lambda b
        F1 G Q2 F3 Q3 q (2)
      HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP (by omega) (by omega) hdim Fraw p
        pop (profileLower D.thickness pop eps tau (seed/8) w) (profileUpper D.thickness eps tau)
        Q2 (pop/rowConstant) (selectionCost K) Cpre t L3 Rel3 CX)

    (R : Finset (Fin n))
    (Eref Hp : Finset (Fin n × Index)) (etaRef : ℝ)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (hScale : D.thickness ≤ (rho m)^2)
    (hRefSmall : (source h R Eref a m p).thickness ≤ rCut)
    (hEtaRef : etaRef ≤ window*eB/256)
    (hEtaMin : etaRef ≤ window*chi*totalLoss/8192)
    (hPopulation : population D.thickness eta lambda b F1 G*
      (parentLabels D R a (2^m) p).card ≤ D.thickness*Hp.card)
    (hGraphRet : Hp.card ≤ selectionCost K*Hgraph.card)
    (u R0 : ℕ)
    (hWindow : 64/((2^(u+12):ℕ):ℝ) ≤ (source h R Eref a m p).thickness^window)
    (loss metric epsilonGeom : ℝ) (depths : Fin Kcoh → ℕ)
    (hLoss : 0 ≤ loss) (hmetric : 0 ≤ metric)
    (heGeom : 0 ≤ epsilonGeom) (heGeom4 : epsilonGeom ≤ 1/4)
    (hLip : metric ≤ r^(-2*epsilonGeom))
    (_hstopLo : 3072*r ≤ (rho m)^2)
    (_hHeight : ((8*R0:ℕ):ℝ) ≤ 1280*((rho m)/64)^(-2*epsilonGeom))
    (_hCost : Cpre=quotientCost q*(newCutCharge Kcoh Ksupport 2 g R0 meshConstant row
      r loss (rankLoss eta0 c (1:Fin 4)) metric extremalExponent
      (fun j => 64/((2^(depths j):ℕ):ℝ)):ℝ))
    (_hSmall : (64:ℝ)/((2^(u+12):ℕ):ℝ) ≤ epsCut)
    (_hShape : 64*((64:ℝ)/((2^(u+12):ℕ):ℝ)) ≤
      2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m))
    (_hNu : newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4)) ≤ 1/2)
    (_hBaseMargin : 4*newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4))+
      2*(18*rankLoss eta0 c (1:Fin 4)+4*epsilonQ/3) ≤ eB/64)
    (Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (level : ℕ) (hzeta : 0 ≤ zeta) (HB : HasOriginalBackbone D original R a level zeta)
    (hEref : Eref ⊆ incidences original) (hTref : T ⊆ Eref)
    (hparent : ∀v∈T,v.1∈parentLabels D R a (2^m) p)
    (hProfile : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hmb0 : m+(u+12) ≤ level) (hf : phaseDepth m ≤ level)
    (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^(u+12):ℕ):ℝ))
    (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (extra : Fin dExtra → (Fin n × Index) → (Fin n × Index) → Prop),
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hdim (physicalMesh m (phaseDepth m)/8)
    let field := fixedField D a m 2 plane Sq Fraw
    let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hdim field Fcfg R0 z.2
    Rel3=completeRelations D a m p .oneTwo P hP hdim field Fcfg R0 u extra →
    ∀W : ∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
      HeightAlignment (T.image key) u (2-extremalExponent) zeta53 chi height.val,
    ∀bin : ℝ → Fin (bins+1),
    ∃menu : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
      selected⊆T.image key ∧ selected.Nonempty ∧
      let Ycut := T.filter (fun z => key z∈selected)
      0 < localSigma menu ∧
      localSigma menu ≤ (source h R Eref a m p).thickness^(window*chi/2) ∧
      4096*(64/((2^(u+12):ℕ):ℝ)) ≤ localSigma menu ∧
      (localSigma menu)^(totalLoss/4096) ≤ NativeActualRawWeightSource.normalization D m*(Ycut.card:ℝ) ∧
      Ycut⊆T ∧ Ycut.Nonempty ∧
      (∀k∈Ycut.image Prod.snd,Ycut.filter (fun z => z.2=k)=T.filter (fun z => z.2=k)) ∧
      (∀height∈selected.image Prod.fst,∃hh : height∈(T.image key).image Prod.fst,
        (W ⟨height,hh⟩).chart=menu.1 ∧ (W ⟨height,hh⟩).rhoDepth=menu.2.1 ∧
        (W ⟨height,hh⟩).tauDepth=menu.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=menu.2.2.2 ∧
        heightPoints selected ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected) ∧
      let bOut := absoluteDepth menu
      let cOut := parentDepth menu
      let sigma := localSigma menu
      let pop := population D.thickness eta lambda b F1 G
      let epsProfile := columnEpsilon D.thickness lambda (seed/8) c2
      let PL0 := profileLower D.thickness pop epsProfile tau (seed/8)
        (min (boundaryWindow tau) ((tau/16)/1000))
      let PU0 := profileUpper D.thickness epsProfile tau
    let z := exponent (source h R Eref a m p).thickness sigma (totalLoss/256)
    let etaA := exponent (64/((2^bOut:ℕ):ℝ)) sigma (totalLoss/16)
    let K := xyConstant D.thickness zeta pop PL0 PU0 (pop/rowConstant)
      ((selectionCost K)*Cpre*(refinementCost ((dExtra+3)+2) (J+1) L3:ℝ)) Q2
      (NativeSourceSizeBounds.radix S.card L3) J m
    ∃(Q : Finset Parent)
      (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^bOut:ℕ):ℝ) ≤
        dist (direction ((source h R Eref a m p).line (representative href univ 0 (2^bOut) q)))
          (direction ((source h R Eref a m p).line (representative href univ 0 (2^bOut) q')))),
      Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
        (parentLabel (source h R Eref a m p) 0 (2^bOut)) ∧ Q.Nonempty ∧
      let C := NativeCoarseCellSource.source href 0 (level-m+6) bOut Q
        (representative href univ 0 (2^bOut)) (incidences (sourceCells D R Ycut a (2^m) p)) hsep
      ∃hC : IsWangZakharovNativeFiniteInput C etaA,
      let cells := actualRows h R Eref Ycut level m bOut p href Q
      let hp : (parentLabels D R a (2^m) p).Nonempty := card_pos.mp href.1.1
      ∃qOld : Parent,∃A : Finset (Fin n × Index),A ⊆ Ycut ∧ A.Nonempty ∧
        (∀v∈A,relativeLabel D a (2^m) p (2^bOut) v.1∈Q ∧
          relativeLabel D a (2^m) p (2^cOut) v.1=qOld) ∧
        let pA := zeroProjection qOld
        let Occ := occurrences h R a m bOut p hp Q cells A
        ∃B ⊆ Occ.image (rawTaggedKey C cOut pA),
          (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
          translatedTags D a m B ⊆ Occ.image (taggedKey D a m C cOut pA) ∧
          (∀v∈translatedTags D a m B,∀w∈translatedTags D a m B,
            finalTime v=finalTime w → v.1=w.1) ∧
          let Efinal := selectedPairs D a m C cOut pA Occ (translatedTags D a m B)
          Efinal.Nonempty ∧ Efinal ⊆ incidences cells ∧
          (∀v∈Efinal,v.1∈parentLabels C univ 0 (2^cOut) pA) ∧
          Efinal.image (localPair C 0 (2^cOut) pA)=B.image Prod.snd ∧
          let Sout := source hC univ Efinal 0 cOut pA
          IsWangZakharovNativeFiniteInput Sout (totalLoss/8) ∧
          (∀i,Sout.line i∈NativeUnitParentNormalization.fixedCompactClass) ∧
          NativeActualLocalAdmission.HasExactTrace hC univ Efinal 0 cOut pA ∧
          Sout.thickness=sigma ∧
          ENNReal.ofReal (sigma^(5*totalLoss/4096)/(8589934592*phaseConstant)) ≤ wzTotalShadingVolume Sout ∧
          volume (sourceUnion Sout) ≤ ENNReal.ofReal
            (NativeRememberedSourceUnion.unionConstant K*sigma^extremalExponent) := by
  obtain ⟨epsCut,rTotal,heps,heps1,hrTotal,Htotal⟩ :=
    NativeActualRawThirdTotalMass.exists_raw_total_supplier totalLoss zeta53 chi window eB menuTax eta0 c epsilonQ
      hLossTotal hzetaSmall hchi hw heB hMenuTax he0 he01 hc hc1 heQ heQ1 heQSmall hcQ hTax
      Kcoh Ksupport g K bins meshConstant row hC hrow
  have hv : 0 < window*chi/2 := by positivity
  obtain ⟨rAssembly,hrAssembly,Hassembly⟩ := exists_raw_source_cutoff totalLoss (window*chi/2) hLossTotal hv
  obtain ⟨rMenu,hrMenu,_hrMenu1,Hmenu⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff
    hv (by norm_num : (0:ℝ)<1/64)
  let rCut := min rTotal (min rAssembly rMenu)
  refine ⟨epsCut,rCut,heps,heps1,lt_min hrTotal (lt_min hrAssembly hrMenu),?_⟩
  intro epsilon delta0 dExtra J L3 n D eta Hbudget h hsmall heta original horiginal
    S hS hSn F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm12 zeta lambda b tau seed c2 r q
    hetaSeed htau0 htau hseed hc2 H1 H2 hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale
    Cpre hCpre a plane E Hgraph T P hP hdim Fraw p t Rel3 Hdata R Eref Hp etaRef href
    hScale hRefSmall hEtaRef hEtaMin hPopulation hGraphRet u R0 hWindow loss metric epsilonGeom depths
    hLoss hmetric heGeom heGeom4 hLip hstopLo hHeight hCost hSmall hShape hNu hBaseMargin Fcfg
    level hzeta HB hEref hTref hparent hProfile hmb0 hf hR0 hbase hmatch hCfg
    extra Sq field key hRel W bin
  have hrRef : 0 < (source h R Eref a m p).thickness := href.1.2.1
  have hRefTotal := hRefSmall.trans (min_le_left _ _)
  have hRefAssembly := hRefSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRefMenu := hRefSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨menu,selected,hsel,hselNe,hs,hWin,hBaseLower,hMass,hYsub,hYne,hFibers,hPatch⟩ :=
    Htotal Hbudget h hsmall heta original horiginal S hS hSn F1 F2 G Q1 Q2 m
      hF1 hG hQ1 hQ2 hGF hm12 zeta lambda b tau seed c2 r q hetaSeed htau0 htau hseed hc2 H1 H2
      hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale Cpre hCpre a plane E Hgraph T P hP hdim Fraw p t
      Rel3 Hdata R Eref Hp etaRef href hScale hRefTotal hEtaRef hPopulation hGraphRet u R0 hWindow
      loss metric epsilonGeom depths hLoss hmetric heGeom heGeom4 hLip hstopLo hHeight hCost hSmall
      hShape hNu hBaseMargin Fcfg extra hRel W bin
  let Ycut := T.filter (fun v => key v∈selected)
  have hsSmall : localSigma menu ≤ 1/64 := hWin.trans (Hmenu _ hrRef hRefMenu)
  obtain ⟨hbOut,hbUpper,hcOut,hcb,hdepth,hWidth,hSigma,_hAbsolute,_hParent⟩ :=
    menu_depth_readback menu hsSmall
  have hKref : ∀i,(source h R Eref a m p).line i∈NativeUnitParentNormalization.fixedCompactClass := by
    intro i
    have hi := (mem_parentLabels D R a (2^m) p _).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels D R a (2^m) p) i)
    exact NativeLocalParentGeometry.mem_fixedCompactClass D a (2^m) p _ hi.2
  let pop := population D.thickness eta lambda b F1 G
  let epsProfile := columnEpsilon D.thickness lambda (seed/8) c2
  let PL0 := profileLower D.thickness pop epsProfile tau (seed/8)
    (min (boundaryWindow tau) ((tau/16)/1000))
  let PU0 := profileUpper D.thickness epsProfile tau
  have hWindowOut : (((2^(parentDepth menu):ℕ):ℝ)*(64/((2^(absoluteDepth menu):ℕ):ℝ)))/64 ≤
      (source h R Eref a m p).thickness^(window*chi/2) := by rw [hSigma]; exact hWin
  have hMassOut : ((((2^(parentDepth menu):ℕ):ℝ)*(64/((2^(absoluteDepth menu):ℕ):ℝ)))/64)^(totalLoss/4096) ≤
      normalization D m*(Ycut.card:ℝ) := by rw [hSigma]; exact hMass
  have hEtaStage : etaRef ≤ (window*chi/2)*totalLoss/4096 :=
    hEtaMin.trans_eq (by ring)
  have hpStage : pExp ≤ (window*chi/2)*totalLoss/4096 := hpMin.trans_eq (by ring)
  have Hresult := Hassembly h original horiginal HB.2.2.1 R Eref level m (u+12)
    (absoluteDepth menu) (parentDepth menu) (footprintDepth menu)
    hm12 (by omega) hbUpper hcb (by omega) (by omega) hzeta HB hmb0 hf hScale p href hKref hProfile
    hRefAssembly hEtaStage hpExp hpStage
    hWidth plane E Hgraph S T Ycut (hTref.trans hEref) hYsub hEref hTref hparent
    P hP hdim Fraw Fcfg hCfg pop PL0 PU0 Q2 (pop/rowConstant) (selectionCost K) Cpre t L3 Rel3 Hdata.1
    R0 hR0 hbase hmatch NativeFixedCompactKakeyaExponent.extremalExponent_le_three hWindowOut hMassOut
  refine ⟨menu,selected,hsel,hselNe,hs,hWin,hBaseLower,hMass,hYsub,hYne,hFibers,hPatch,?_⟩
  simpa only [hSigma] using Hresult

end NativeActualRawNativeRealization
end
