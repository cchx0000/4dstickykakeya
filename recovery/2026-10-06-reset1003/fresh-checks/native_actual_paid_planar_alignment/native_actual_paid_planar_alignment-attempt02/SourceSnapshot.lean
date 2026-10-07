/- UNVERIFIED actual raw-cost-to-planar supplier. No strict Lean check has run. -/
import Theorems.Thm_StickyKakeya4_native_paid_third_record_readback
import Theorems.Thm_StickyKakeya4_native_third_planar_height_alignment
import Theorems.Thm_StickyKakeya4_native_finest_Y_output_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 9000000
noncomputable section
namespace NativeActualPaidPlanarAlignment
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativePaidThirdRecordReadback NativePaidThirdRecord NativePaidThirdBudget NativeThirdXYSourceData
open NativeRetainedSliceCore NativeRetainedSliceBudgetAlgebra NativeReferenceSliceBudgetAlgebra
open NativeActualNewCutBudget NativeNewCutOutputBudget NativeFinestYOutputBudget
open NativeReferenceXYGridPoints NativeReferenceXYGridField NativeReferenceXYGridMaps
open NativeHorizontalGrainSlice NativeGrainQuotientFibers NativeTranslatedGrainHeightOverlap
open NativeEncodedQuotientAD NativeFixedCompactKakeyaExponent NativeRankExponentHierarchy
open NativeParentHeightGraphCore NativeActivePhasePopulation NativeAllTwoScaleConfiguration
open NativeSingleHeightCoarseYAD NativeLiteralYHeightAlignment NativeConfiguredThirdRelation
open NativeCubicalIncidenceCounts NativeSharpXPowerAlgebra NativeSquaredGrainQueries NativeThirdXYData
open scoped Matrix.Norms.Elementwise

/-- The planar parameters precede the rank/source parameters.  After g and
finite menu sizes are known, one cutoff is chosen before D.  The fine-Y
constant is derived from the actual raw first/second/final-third allowances,
the literal newCutCharge, and the actual final T.  No AD or numerical Y-cost
premise is supplied to this entrance. -/
theorem exists_paid_alignment (zeta53 : ℝ) (hzeta53 : 0 < zeta53) :
    ∃eta53Threshold chi : ℝ,0 < eta53Threshold ∧ 0 < chi ∧
    ∀eta53 : ℝ,0 < eta53 → eta53 ≤ eta53Threshold →
    ∀Kcoh Ksupport g : ℕ,∀meshConstant row : ℝ,0 ≤ meshConstant → 0 ≤ row →
    ∃epsCut : ℝ,0 < epsCut ∧ epsCut ≤ 1 ∧
    ∀ {epsilon eta0 c delta0 : ℝ} {K d J L3 n : ℕ}
    {D : FiniteScaleSource n} {eta : ℝ}
    (Hbudget : HasBudget epsilon eta0 c g K d J L3 delta0) (he : 0 < epsilon)
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
    (p : Parent) (t : ℝ) (Rel3 : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hdata :
      let F3 := refinementCost (d+2) (J+1) L3
      let Q3 := NativeSourceSizeBounds.radix S.card L3
      let w := min (boundaryWindow tau) ((tau/16)/1000)
      let pop := population D.thickness eta lambda b F1 G
      let eps := columnEpsilon D.thickness lambda (seed/8) c2
      let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2 lambda b
        F1 G Q2 F3 Q3 q (2)
      HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP (by omega) (by omega) hdim Fraw p
        pop (profileLower D.thickness pop eps tau (seed/8) w) (profileUpper D.thickness eps tau)
        Q2 (pop/rowConstant) (selectionCost K) Cpre t L3 Rel3 CX)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level u R0 : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (hp : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (hR0 : 0 < R0) (hbaseEq : mu m*(R0:ℝ)=(2:ℝ)⁻¹^u)
    (hk : extremalExponent ≤ 2)
    (loss metric epsilonGeom : ℝ) (depths : Fin Kcoh → ℕ)
    (hLoss : 0 ≤ loss) (hRankLoss : 0 ≤ rankLoss eta0 c (1:Fin 4))
    (hmetric : 0 ≤ metric) (heGeom : 0 ≤ epsilonGeom) (heGeom4 : epsilonGeom ≤ 1/4)
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
    (hMargin : 16*newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4))+
      4*epsilon ≤ eta53/2)
    (Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ),
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hdim (physicalMesh m (phaseDepth m)/8)
    let field := fixedField D a m 2 plane Sq Fraw
    let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hdim field Fcfg R0 z.2
    (∀z∈T,field (translatedHeight D a m z.2)=Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))) →
    (∀z∈T,∀w∈T,translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=
      translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
      translatedHeight D a m z.2=translatedHeight D a m w.2) →
    Nonempty (∀height : {height : ℤ // height∈(T.image key).image Prod.fst},
      HeightAlignment (T.image key) u (2-extremalExponent) zeta53 chi height.val) := by
  obtain ⟨etaThreshold,chi,hThreshold,hchi,Hplanar⟩ :=
    NativeThirdPlanarHeightAlignment.exists_actual_height_alignment hzeta53
  refine ⟨etaThreshold,chi,hThreshold,hchi,?_⟩
  intro eta53 he53 he53Top Kcoh Ksupport g meshConstant row hC hrow
  obtain ⟨deltaPlanar,hDeltaPlanar,H53⟩ := Hplanar eta53 he53 he53Top
  let C := fixedFactor Kcoh Ksupport g meshConstant row
  have hCpos : 0 < C := by dsimp [C,fixedFactor,offsetCoefficient]; positivity
  obtain ⟨eps0,heps0,heps01,Hpay⟩ := exists_finest_Y_output_cutoff C eta53 hCpos he53
  refine ⟨min eps0 deltaPlanar,lt_min heps0 hDeltaPlanar,(min_le_left _ _).trans heps01,?_⟩
  intro epsilon eta0 c delta0 K d J L3 n D eta Hbudget he h hsmall heta original horiginal
    S hS hSn F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm12
    zeta lambda b tau seed c2 r q hetaSeed htau0 htau hseed hzeta hc2 H1 H2
    hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale Cpre hCpre a plane E Hgraph T
    P hP hdim Fraw p t Rel3 Hdata ha level u R0 hdy hf hp hR0 hbaseEq hk
    loss metric epsilonGeom depths hLoss hRankLoss hmetric heGeom heGeom4 hLip
    hstopLo hHeight hCost hSmall hShape hNu hMargin Fcfg Sq field key hfreeze Hsingle
  have hm6 : 6 ≤ m := by omega
  let F3 := refinementCost (d+2) (J+1) L3
  let Q3 := NativeSourceSizeBounds.radix S.card L3
  let w := min (boundaryWindow tau) ((tau/16)/1000)
  let pop := population D.thickness eta lambda b F1 G
  let col := columnEpsilon D.thickness lambda (seed/8) c2
  let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2
    lambda b F1 G Q2 F3 Q3 q 2
  let KXY := xyConstant D.thickness zeta pop
    (profileLower D.thickness pop col tau (seed/8) w) (profileUpper D.thickness col tau)
    (pop/rowConstant) ((selectionCost K:ℝ)*Cpre*(F3:ℝ)) Q2 Q3 J m
  let KY := quotientConstant 1 2 (1/(32*CX)) KXY (3-extremalExponent)
  let M := max 1 (Cpre/quotientCost q)
  have Hpaid := (paid_record_from_budget Hbudget he h hsmall heta original horiginal S hS hSn
    F1 F2 G Q1 Q2 m hF1 hG hQ1 hQ2 hGF hm6 (1:Fin 4) (by norm_num) (by norm_num)
    zeta lambda b tau seed c2 r q hetaSeed htau0 htau hseed hzeta hc2 H1 H2
    hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale Cpre hCpre
    a plane E Hgraph T P hP hdim Fraw p t Rel3 Hdata).2
  have hFine : KY ≤ M^2*(rho m)^(-epsilon) := Hpaid.2.2.2.1
  have hKY : 0 ≤ KY := (by norm_num : (0:ℝ) ≤ 1).trans
    (NativeEncodedQuotientAD.quotientConstant_one_le _ _ _ _ _)
  have hRho : 0 < rho m := rho_pos m
  have hRho1 : rho m ≤ 1 := by
    unfold rho
    have hpw : (64:ℝ) ≤ (2:ℝ)^m := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm6
      norm_num at hh
      exact hh
    push_cast
    exact (div_le_one (by positivity)).mpr hpw
  have hCuts := source_new_cut_cost Kcoh Ksupport 2 g R0 m (by norm_num)
    meshConstant row r loss (rankLoss eta0 c (1:Fin 4)) metric epsilonGeom extremalExponent depths
    hC hrow hr hr1 hLoss hRankLoss hmetric heGeom hLip hRho1 hstopLo hHeight
  have hM : M ≤ C*r^(-newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4))) := by
    rw [actual_multiplier (quotientCost q) Cpre _ (quotientCost_pos hq) hCpre hCost]
    exact hCuts
  let eps : ℝ := 64/((2^(u+12):ℕ):ℝ)
  let deltaY : ℝ := (2:ℝ)⁻¹^u/512
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hY : 0 < deltaY := by dsimp [deltaY]; positivity
  have hYEeq : deltaY=eps/8 := by
    dsimp [deltaY,eps]
    push_cast
    simp only [pow_add,inv_pow]
    norm_num
    field_simp
  have hYE : deltaY ≤ eps := by
    rw [hYEeq]
    exact div_le_self heps.le (by norm_num)
  have hShape' : eps^2 ≤ rho m :=
    NativeRetentionOutputPower.configured_square_le_reference hRho hRho1 heps.le
      heGeom heGeom4 hShape
  have hFinal := Hpay M r (rho m) eps deltaY
    (newExponent Kcoh epsilonGeom loss (rankLoss eta0 c (1:Fin 4))) epsilon KY
    (2-extremalExponent) (by dsimp [M]; positivity) hr hRho hY hYE
    (hSmall.trans (min_le_left _ _)) (by unfold newExponent; positivity) hNu he.le hKY
    (by linarith only [extremalExponent_nonneg]) hShape' hscale hM hFine hMargin
  have hFinal' : finalConstant KY (2-extremalExponent) ≤ deltaY^(-eta53) := by
    simpa only [finalConstant,coarseConstant] using hFinal
  exact H53 n d J D eta a zeta h original horiginal ha m level u hm12 hdy hf
    p plane E Hgraph S T hS hp P hP hdim Fraw Fcfg pop
    (profileLower D.thickness pop col tau (seed/8) w) (profileUpper D.thickness col tau)
    Q2 (pop/rowConstant) (selectionCost K) Cpre t L3 Rel3 CX R0 hR0 hbaseEq hk Hdata
    hfreeze Hsingle (hYE.trans (hSmall.trans (min_le_right _ _))) hFinal'

end NativeActualPaidPlanarAlignment
