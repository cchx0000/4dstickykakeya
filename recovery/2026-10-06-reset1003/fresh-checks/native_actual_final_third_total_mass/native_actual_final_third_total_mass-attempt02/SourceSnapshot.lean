/- Actual-final-third htotal source reader. Originally drafted without verification; consult current receipts. -/
import Theorems.Thm_StickyKakeya4_native_actual_paid_planar_alignment
import Theorems.Thm_StickyKakeya4_native_htotal_implementation
import Theorems.Thm_StickyKakeya4_native_small_loss_parent_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeActualFinalThirdTotalMass
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

/-- Actual planar witnesses, baseline admission payment and whole-Y graph
retention are joined on the same final T.  Raw H1/H2/H3, the exact continuation
cost, source population and the already constructed separator are consumed;
there is no total-mass, fine-Y AD, paid-retention, or new separator premise.
The returned cutoffs depend on fixed parameters and g before the original D. -/
theorem exists_actual_total_supplier (totalLoss zeta53 : ℝ)
    (hLossTotal : 0 < totalLoss) (hzeta53 : 0 < zeta53)
    (hzetaSmall : zeta53 ≤ totalLoss/16384) :
    ∃eta53Threshold chi : ℝ,0 < eta53Threshold ∧ 0 < chi ∧
    ∀eta53 : ℝ,0 < eta53 → eta53 ≤ eta53Threshold →
    ∀window eB menuTax eta0 c epsilonQ : ℝ,
      0 < window → 0 < eB → 0 < menuTax → 0 < eta0 → eta0 ≤ 1 →
      0 < c → c ≤ 1 → 0 < epsilonQ → epsilonQ ≤ 1 → eta0 ≤ epsilonQ → c ≤ epsilonQ/24 →
      5*eB/16+2*(commonBudget eta0 c/4)/window+menuTax ≤ (chi/2)*(totalLoss/16384) →
    ∀Kcoh Ksupport g K bins : ℕ,∀meshConstant row : ℝ,0 ≤ meshConstant → 0 ≤ row →
    ∃epsCut rCut : ℝ,0 < epsCut ∧ epsCut ≤ 1 ∧ 0 < rCut ∧
    ∀ {epsilon delta0 : ℝ} {dExtra J L3 n : ℕ}
    {D : FiniteScaleSource n} {eta : ℝ}
    (Hbudget : HasBudget epsilon eta0 c g K (dExtra+3) J L3 delta0) (he : 0 < epsilon)
    (h : IsWangZakharovNativeFiniteInput D eta) (hsmall : D.thickness ≤ delta0) (heta : 0 ≤ eta)
    (original : Fin n → Finset Index) (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (S : Finset (Fin n × Index)) (hS : S⊆incidences original) (hSn : S.Nonempty)
    (F1 F2 G Q1 Q2 m : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ1 : 1 ≤ Q1) (hQ2 : 0 < Q2)
    (hGF : G ≤ F2) (hm12 : 12 ≤ m) 
    (zeta lambda b tau seed c2 r q : ℝ)
    (hetaSeed : eta ≤ seed/8) (htau0 : 0 ≤ tau) (htau : tau ≤ commonBudget eta0 c/1024)
    (hseed : seed ≤ tau/16384) (hzeta : zeta ≤ seed/256) (hc2 : c2=commonBudget eta0 c/4)
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

    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (hFineDepth : phaseDepth m ≤ level)
    (Eref Hp : Finset (Fin n × Index)) (hRefOld : Eref⊆incidences original)
    (hRefR : ∀z∈Eref,z.1∈R)
    (hGraphRef : Hgraph⊆Eref) (etaRef : ℝ)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (hScale : D.thickness ≤ (rho m)^2)
    (hRefSmall : (source h R Eref a m p).thickness ≤ rCut)
    (hEtaRef : etaRef ≤ window*eB/256)
    (hProfile : (64:ℝ)^3*(source h R Eref a m p).thickness^(window*eB/16) ≤ D.thickness^zeta)
    (hzeta0 : 0 ≤ zeta)
    (hPopulation : population D.thickness eta lambda b F1 G*
      (parentLabels D R a (2^m) p).card ≤ D.thickness*Hp.card)
    (hGraphRet : Hp.card ≤ selectionCost K*Hgraph.card)
    (u R0 : ℕ) (hDepth : m+(u+12) ≤ level)
    (hp : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (hR0 : 0 < R0) (hBase : rho m ≤ mu m*(R0:ℝ))
    (hbaseEq : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u)
    (hWindow : 64/((2^(u+12):ℕ):ℝ) ≤ (source h R Eref a m p).thickness^window)
    (hk : extremalExponent ≤ 2)
    (loss metric epsilonGeom : ℝ) (depths : Fin Kcoh → ℕ)
    (hLoss : 0 ≤ loss) (hmetric : 0 ≤ metric)
    (heGeom : 0 ≤ epsilonGeom) (heGeom4 : epsilonGeom ≤ 1/4)
    (hLip : metric ≤ r^(-2*epsilonGeom))
    (hstopLo : 3072*r ≤ (rho m)^2)
    (hHeight : ((8*R0:ℕ):ℝ) ≤ 1280*((rho m)/64)^(-2*epsilonGeom))
    (hCost : Cpre=quotientCost q*(newCutCharge Kcoh Ksupport 2 g R0 meshConstant row
      r loss (rankLoss eta0 c (1:Fin 4)) metric extremalExponent
      (fun j => 64/((2^(depths j):ℕ):ℝ)):ℝ))
    (hSmall : (64:ℝ)/((2^(u+12):ℕ):ℝ) ≤ epsCut)
    (hShape : 64*((64:ℝ)/((2^(u+12):ℕ):ℝ)) ≤
      2*max ((5/4:ℝ)*(rho m)^(1-2*epsilonGeom)) (rho m))
    (hNu : newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4)) ≤ 1/2)
    (hFineMargin : 16*newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4))+
      4*epsilon ≤ eta53/2)
    (hBaseMargin : 4*newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4))+
      2*(18*rankLoss eta0 c (1:Fin 4)+4*epsilonQ/3) ≤ eB/64)
    (Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (hCfg : ∀height,‖Fcfg height‖≤(1/4:ℝ))
    (extra : Fin dExtra → (Fin n × Index) → (Fin n × Index) → Prop),
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hdim (physicalMesh m (phaseDepth m)/8)
    let field := fixedField D a m 2 plane Sq Fraw
    let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hdim field Fcfg R0 z.2
    let cfg := NativeActualConfiguredPoint.point D a m p .oneTwo P hP hdim field Fcfg R0
    let graph := fun z : Fin n × Index => (cfg z.2,outputTube h R Eref a m (u+12) p href z.1)
    Rel3=completeRelations D a m p .oneTwo P hP hdim field Fcfg R0 u extra →
    (∀z∈T,field (translatedHeight D a m z.2)=Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))) →
    (∀z∈T,∀w∈T,translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=
      translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
      translatedHeight D a m z.2=translatedHeight D a m w.2) →
    (∀x∈T.image (fun z => cfg z.2),∀y∈T.image (fun z => cfg z.2),
      x≠y → (mu m*(R0:ℝ))/64 ≤ dist x y) →
    ∀bin : ℝ → Fin (bins+1),
    ∃W : ∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
      HeightAlignment (T.image key) u (2-extremalExponent) zeta53 chi height.val,
    ∃menu : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
      selected⊆T.image key ∧ selected.Nonempty ∧
      let eps := 64/((2^(u+12):ℕ):ℝ)
      let Ycut := T.filter (fun z => key z∈selected)
      0 < localSigma menu ∧
      localSigma menu ≤ (source h R Eref a m p).thickness^(window*chi/2) ∧
      (localSigma menu)^(totalLoss/4096) ≤ eps^4*((Ycut.image graph).card:ℝ) ∧
      (∀b0 : ℕ,b0 ≤ u+12 →
        (localSigma menu)^(totalLoss/4096) ≤ eps^4*
          (∑q0∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
            (parentLabel (source h R Eref a m p) 0 (2^b0)),
              NativeSameQFineGraph.weight h R Eref a m (u+12) b0 p href cfg Ycut q0)) ∧
      (∀x∈Ycut.image (fun z => cfg z.2),∀y∈Ycut.image (fun z => cfg z.2),
        x≠y → eps ≤ dist x y) ∧
      ∀height∈selected.image Prod.fst,∃hh : height∈(T.image key).image Prod.fst,
        (W ⟨height,hh⟩).chart=menu.1 ∧ (W ⟨height,hh⟩).rhoDepth=menu.2.1 ∧
        (W ⟨height,hh⟩).tauDepth=menu.2.2.1 ∧ bin (W ⟨height,hh⟩).exponent=menu.2.2.2 ∧
        heightPoints selected ((2:ℝ)⁻¹^u/512) height=(W ⟨height,hh⟩).selected := by
  obtain ⟨etaThreshold,chi,hThreshold,hchi,Hplanar⟩ := exists_paid_alignment zeta53 hzeta53
  refine ⟨etaThreshold,chi,hThreshold,hchi,?_⟩
  intro eta53 he53 he53Top window eB menuTax eta0 c epsilonQ
    hw heB hMenuTax he0 he01 hc hc1 heQ heQ1 heQSmall hcQ hTax
    Kcoh Ksupport g K bins meshConstant row hC hrow
  obtain ⟨epsPlanar,hEP,hEP1,H53⟩ :=
    Hplanar eta53 he53 he53Top Kcoh Ksupport g meshConstant row hC hrow
  obtain ⟨epsBase,hEB,hEB1,Hbase⟩ :=
    exists_actual_retention_cutoff eB heB Kcoh Ksupport g K meshConstant row hC hrow
  obtain ⟨rCut,hRC,Hmass⟩ := NativeActualYEpsilonTotalMass.exists_actual_total_mass
    totalLoss zeta53 chi window eB (commonBudget eta0 c/4) menuTax hLossTotal hzeta53
    hzetaSmall hchi hw heB (div_nonneg (commonBudget_pos he0 hc).le (by norm_num)) hMenuTax hTax bins
  refine ⟨min epsPlanar epsBase,rCut,lt_min hEP hEB,(min_le_left _ _).trans hEP1,hRC,?_⟩
  intro epsilon delta0 dExtra J L3 n D eta Hbudget he h hsmall heta original horiginal
    S hS hSn F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm12
    zeta lambda b tau seed c2 r q hetaSeed htau0 htau hseed hzeta hc2 H1 H2
    hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale Cpre hCpre a plane E Hgraph T
    P hP hdim Fraw p t Rel3 Hdata R level HB hFineDepth Eref Hp hRefOld hRefR hGraphRef etaRef href
    hScale hRefSmall hEtaRef hProfile hzeta0 hPopulation hGraphRet u R0 hDepth hp hR0 hBase
    hbaseEq hWindow hk loss metric epsilonGeom depths hLoss hmetric heGeom heGeom4 hLip
    hstopLo hHeight hCost hSmall hShape hNu hFineMargin hBaseMargin Fcfg hCfg extra
    Sq field key cfg graph hRel hfreeze Hsingle hSeparator bin
  let F3 := refinementCost ((dExtra+3)+2) (J+1) L3
  let Q3 := NativeSourceSizeBounds.radix S.card L3
  let pop := population D.thickness eta lambda b F1 G
  let eps : ℝ := 64/((2^(u+12):ℕ):ℝ)
  have hRank : 0 < rankLoss eta0 c (1:Fin 4) := rankLoss_pos he0 hc _
  have hRank1 : rankLoss eta0 c (1:Fin 4) ≤ 1 :=
    (rankLoss_le_initial he0.le hc.le hc1 _).trans he01
  have hm6 : 6 ≤ m := by omega
  have hTcopy := Hdata.1
  rcases hTcopy with ⟨hTS,hTn,_hRetST,hTH,_hRetHT,Hrel,_hPoint,_hXY,_hClasses,
    _hGrain,_hKey,_hThreshold,_hRetParent,_hAD,_hRead,hNorm⟩
  have hTE : T⊆Eref := hTH.trans hGraphRef
  have hTparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p := by
    intro z hz
    exact (mem_parentLabels D R a (2^m) p z.1).mpr
      ⟨hRefR z (hTE hz),hp z (hTS hz)⟩
  have ht := commonBudget_pos he0 hc
  have hetaRaw : eta ≤ commonBudget eta0 c/32 := by linarith only [hetaSeed,hseed,htau,ht]
  have H3 := Hbudget.1 n D eta h hsmall heta hetaRaw original horiginal S hS hSn
  have hF3 : 1 ≤ F3 := by have hh := refinementCost_pos ((dExtra+3)+2) (J+1) L3; omega
  have hQ3 : 1 ≤ Q3 := (by norm_num : 1 ≤ (4:ℕ)).trans
    (NativeSourceSizeBounds.radix_four_le _ _)
  have hQ2one : 1 ≤ Q2 := by omega
  have hRho : 0 < rho m := rho_pos m
  have hRho1 : rho m ≤ 1 := by
    have hpow : (64:ℝ) ≤ ((2^m:ℕ):ℝ) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1≤(2:ℕ)) hm6)
    exact (div_le_one (by positivity)).mpr hpow
  have hTauQ : tau ≤ commonBudget eta0 c/(1000*((0:ℕ)+1:ℝ)) := by
    norm_num
    linarith only [htau,ht]
  have hqLower := NativeSmallLossParentBudget.actual_test_radius_small_loss h.1.2.1 hr hr1
    heQ he0.le heQSmall hc hc1 hcQ (1:Fin 4) hrdelta htau0 g 0 hTauQ hgrid hqraw
  have hB7 : r^(7*rankLoss eta0 c (1:Fin 4)) ≤ b := by
    have hh' := Real.rpow_le_rpow_of_exponent_ge hr hr1
      (show (2*((2:ℕ):ℝ)+1)*rankLoss eta0 c (1:Fin 4) ≤
        7*rankLoss eta0 c (1:Fin 4) by norm_num; linarith only [hRank])
    exact hh'.trans hb
  have hRetention := Hbase D.thickness eta lambda b tau seed (commonBudget eta0 c) c2 r
    (cutoff c (1:Fin 4)) (rankLoss eta0 c (1:Fin 4)) q epsilonQ loss metric epsilonGeom
    extremalExponent eps F1 F2 G Q1 Q2 F3 Q3 m R0 2 depths h.1.2.1 h.1.2.2.1 heta
    hF1 hG hQ1 hQ2one hQ3 hGF H1 H2 H3 ht.le htau hseed hc2 hr hr1 hRank.le hRank1
    hrdelta (cutoff_mul_rankLoss eta0 c _).symm hlambda hB7 hq hq1 heQ.le heQ1 hqLower
    (by norm_num) hLoss hmetric heGeom heGeom4 hLip hRho1 hstopLo hscale hHeight
    (by dsimp [eps]; positivity) (hSmall.trans (min_le_right _ _)) hShape
    (by linarith only [hNu]) hBaseMargin
  have hRetain := (NativeBaselineThirdRetentionTrace.from_third_source D zeta a m plane E Hp Hgraph
    S T P hP (by norm_num) (by norm_num) hdim Fraw p pop _ _ Q2 _ _ Cpre t L3 Rel3 _ Hdata K hGraphRet).2
  have hPop : 0 < pop := by
    have hd := h.1.2.1
    have hlambdaPos : 0 < lambda := by rw [hlambda]; positivity
    have hbPos := (Real.rpow_pos_of_pos hr _).trans_le hb
    dsimp [pop,population]
    positivity
  have hCostPos : 0 < (selectionCost K:ℝ)*Cpre*(F3:ℝ) := by
    have hF3p : (0:ℝ) < F3 := by exact_mod_cast (show 0<F3 by omega)
    have hGraph : 0 < selectionCost K := by
      unfold selectionCost NativeProjectorCellChart.chartCount
      positivity
    positivity
  have hPaid : retentionFactor ((selectionCost K:ℝ)*Cpre*(F3:ℝ)) pop ≤ eps^(-(eB/32)) := by
    rw [hCost]
    simpa only [mul_assoc] using hRetention
  have hMB : mu m*(R0:ℝ)=4096/((2^(u+12):ℕ):ℝ) := by
    rw [hbaseEq]
    push_cast
    simp only [pow_add,inv_pow]
    norm_num
    field_simp
  obtain ⟨W⟩ := H53 Hbudget he h hsmall heta original horiginal S hS hSn
    F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm12 zeta lambda b tau seed c2 r q
    hetaSeed htau0 htau hseed hzeta hc2 H1 H2 hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale
    Cpre hCpre a plane E Hgraph T P hP hdim Fraw p t Rel3 Hdata HB.2.2.1
    level u R0 HB.2.1 hFineDepth hp hR0 hbaseEq hk loss metric epsilonGeom depths
    hLoss hRank.le hmetric heGeom heGeom4 hLip hstopLo hHeight hCost
    (hSmall.trans (min_le_left _ _)) hShape hNu hFineMargin Fcfg hfreeze Hsingle
  have Hrel' : ∀j x y,x∈T → y∈T → degree (fun _ : Fin n × Index => 1)
      (completeRelations D a m p .oneTwo P hP hdim field Fcfg R0 u extra j) T x ≤
      Q3^2*degree (fun _ : Fin n × Index => 1)
        (completeRelations D a m p .oneTwo P hP hdim field Fcfg R0 u extra j) T y := by
    simpa only [hRel] using Hrel
  have hField : ∀height u v,|field height u v|≤1/4 := by
    intro height u v
    exact (Matrix.norm_entry_le_entrywise_sup_norm (field height) (i:=u) (j:=v)).trans (hNorm height)
  have hCfg' : ∀height u v,|Fcfg height u v|≤1/4 := by
    intro height u v
    exact (Matrix.norm_entry_le_entrywise_sup_norm (Fcfg height) (i:=u) (j:=v)).trans (hCfg height)
  obtain ⟨menu,selected,hsel,hsn,hSig,hSigGap,hMass,hWeights,hWhole⟩ :=
    Hmass n D eta h original R level a zeta hzeta0 HB Eref Hp T m hm6 hScale p etaRef href
      hTE hRefOld hTparent hRefSmall hEtaRef hProfile pop ((selectionCost K:ℝ)*Cpre*(F3:ℝ))
      hPop hCostPos hPopulation hRetain u hDepth hWindow hPaid P hP hdim field Fcfg
      hField hCfg' R0 hR0 hBase hMB dExtra Q3 F3 extra hF3 H3 Hrel'
      (2-extremalExponent) W bin
  refine ⟨W,menu,selected,hsel,hsn,hSig,hSigGap,hMass,hWeights,?_,hWhole⟩
  intro x hx y hy hxy
  have hh := hSeparator x (image_subset_image (filter_subset _ _) hx)
    y (image_subset_image (filter_subset _ _) hy) hxy
  rw [hMB] at hh
  have heq : 4096/((2^(u+12):ℕ):ℝ)/64=eps := by dsimp [eps]; ring
  rwa [heq] at hh

end NativeActualFinalThirdTotalMass
