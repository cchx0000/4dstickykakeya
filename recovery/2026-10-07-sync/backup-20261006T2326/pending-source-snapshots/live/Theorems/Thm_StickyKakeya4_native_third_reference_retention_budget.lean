/- UNVERIFIED actual third-source to sparse-reference retention join.
The chosen coarse-Y set carries its literal cardinal retention; no native
proof for its sparse shading, or desired incidence ratio, is an input. -/
import Theorems.Thm_StickyKakeya4_native_weighted_joint_cleanup
import Theorems.Thm_StickyKakeya4_native_configured_Y_weighted_retention
import Theorems.Thm_StickyKakeya4_native_current_reference_incidence_retention
import Theorems.Thm_StickyKakeya4_native_current_reference_incidence_subset
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_extra

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeThirdReferenceRetentionBudget
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeCubicalIncidenceCounts NativeOriginalPrunedMass
open NativeThirdXYSourceData NativeReferenceXYGridField NativeGrainQuotientFibers NativeSquaredGrainQueries
open NativeHorizontalGrainSlice NativeConfiguredThirdRelation CanonicalConfiguredE4Bridge
open NativeJointUniformCoarseRelations NativeConfiguredPointDegreeReader NativeJointKeyDescent
open NativeConfiguredYWeightedRetention NativeWeightedJointCleanup WeightedRichDirectionalLayers
open NativeParentHeightGraphCore NativeRetainedSliceCore NativeRetainedSliceBudgetAlgebra
open NativeRetainedSliceBudgetExtra NativeReferenceSliceBudgetAlgebra NativeActivePhasePopulation
open NativeNormalizedCellRelativeMenu NativeConfiguredJointRelation RichDirectionalLayers

/-- The reference parent, graph retention, unique third record, actual
coarse-Y selection and weighted pair cleanup produce the REAL retained
sourceCells factor. Old graph/quotient/F3 costs appear exactly once, and
the Y-cut's Q3 squared is absorbed inside the existing Q3 fourth allowance. -/
theorem from_third_source {n d J : ℕ} {D : FiniteScaleSource n} {eta localEta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Rfull : Finset (Fin n)) (Eref Hp E Hgraph S T : Finset (Fin n × Index))
    (hEref : Eref ⊆ NativeOriginalParentDensityCore.retained original Rfull)
    (m : ℕ) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h Rfull Eref a m p) localEta)
    (hS : S ⊆ NativeOriginalParentDensityCore.parentEdges D a (2^m) Eref p)
    (Khalf : ℕ) (hgraph : Hp.card ≤ selectionCost Khalf*Hgraph.card)
    (lambdaRank b : ℝ) (hlambda : 0 < lambdaRank) (hb : 0 < b)
    (F1 G0 : ℕ) (hF1 : 0 < F1) (hG0 : 0 < G0)
    (q Ccuts : ℝ) (hq : 0 < q) (hCcuts : 0 < Ccuts)
    (zeta : ℝ) (plane : Index → Submodule ℝ E4)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P=1)
    (Fraw Fcfg : ℤ → Matrix (Fin 2) (Fin 1) ℝ)
    (referencePop PL PU : ℝ) (Qref : ℕ) (lambdaRef Gref threshold : ℝ) (L3 : ℕ)
    (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (CX : ℝ) (R0 u depth : ℕ) (hR0 : 0 < R0) (hdepth : depth ≤ u+3) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
      (by norm_num) (by norm_num) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    let Rel := completeRelations D a m p .oneTwo P hP hd F Fcfg R0 u extra
    let Q3 := NativeSourceSizeBounds.radix S.card L3
    let F3 := refinementCost ((d+3)+2) (J+1) L3
    let pop := population D.thickness eta lambdaRank b F1 G0
    pop*(parentLabels D Rfull a (2^m) p).card ≤ D.thickness*Hp.card →
    HasThirdXYSourceData (J:=J) D zeta a m plane E Hgraph S T P hP
      (by norm_num) (by norm_num) hd Fraw p referencePop PL PU Qref lambdaRef Gref
      (quotientCost q*Ccuts) threshold L3 Rel CX →
    (∀x∈S,∀y∈S,
      NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 x.2=
        NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 y.2 →
      physicalCell D a (2^m) (2^(u+6)) p x.2=physicalCell D a (2^m) (2^(u+6)) p y.2) →
    ∀(Ysel : Finset (ℤ × CanonicalGridRecoding.Grid 2)) (theta : ℝ),0 < theta →
    let key := fun z : Fin n × Index => coarseYKey D a m p .oneTwo P hP hd F Fcfg R0 z.2
    Ysel ⊆ T.image key → theta*(T.image key).card ≤ (Ysel.card:ℝ) →
    let pair := geometricPairKey D a m p .oneTwo P hP hd F Fcfg R0 u
    let G := T.image pair
    let Ycut := T.filter (fun z => key z ∈ Ysel)
    let A := Ycut.image pair
    let weight := fun v => (T.filter (fun z => pair z=v)).card
    let cls := onPair D a m p .oneTwo P hP hd F Fcfg R0 u depth S
    ∃B⊆A,B.Nonempty ∧
      let E0 := T.filter (fun z => pair z∈B)
      let totalCost := (selectionCost Khalf:ℝ)*quotientCost q*Ccuts*(F3:ℝ)*(2*(Q3:ℝ)^2/theta)
      let retention := (1024*175616*volumeConstant)*totalCost/pop
      E0⊆T ∧ E0⊆Eref ∧ E0.image pair=B ∧
      0 < totalCost ∧ (Hp.card:ℝ) ≤ totalCost*E0.card ∧
      theta*(T.card:ℝ) ≤ 2*(Q3:ℝ)^2*E0.card ∧
      (∀x∈E0,E0.filter (fun z => pair z=pair x)=T.filter (fun z => pair z=pair x)) ∧
      (∀c∈B.image cls,(mass A weight : ℝ)*(G.card:ℝ) <
        2*((A.image cls).card:ℝ)*(Q3:ℝ)^2*(T.card:ℝ)*((classFiber B cls c).card:ℝ)) ∧
      0 < retention ∧
      incidences (sourceCells D Rfull E0 a (2^m) p) ⊆ incidences (sourceCells D Rfull Eref a (2^m) p) ∧
      ((incidences (sourceCells D Rfull Eref a (2^m) p)).card:ℝ) ≤
        retention*(incidences (sourceCells D Rfull E0 a (2^m) p)).card ∧
      retention ≤ (128*175616:ℝ)*Ccuts/theta*
        extraCoefficient D.thickness eta lambdaRank b F1 G0 F3 Q3 q Khalf := by
  intro Sq F Rel Q3 F3 pop hpop Hdata Hbase Ysel theta htheta key hY hYcard pair G Ycut A weight cls
  have hTS : T⊆S := Hdata.1.1
  have hTn : T.Nonempty := Hdata.1.2.1
  have hHgraph : (Hgraph.card:ℝ) ≤ (quotientCost q*Ccuts)*(F3:ℝ)*T.card := Hdata.1.2.2.2.2.1
  have Hrel := Hdata.1.2.2.2.2.2.1
  have HP := caller_geometricPair_uniformity D a m p .oneTwo P hP hd F Fcfg R0 u extra T Q3 Hrel
  have HY : HasUniformFibers T Q3 key := by
    intro x hx y hy
    have hh := Hrel 0 x y hx hy
    change SelfUniform.degree (fun _ : Fin n × Index => 1) (fun x y => key x=key y) T x ≤
      Q3^2*SelfUniform.degree (fun _ : Fin n × Index => 1) (fun x y => key x=key y) T y at hh
    simpa only [unit_degree_eq_fiber] using hh
  have hYmass : theta*(T.card:ℝ) ≤ (Q3:ℝ)^2*Ycut.card :=
    uniform_subset_retention T key Q3 HY Ysel hY theta htheta.le hYcard
  have hYcutT : Ycut⊆T := filter_subset _ _
  have hYcutn : Ycut.Nonempty := by
    apply card_pos.mp
    have hTpos : (0:ℝ) < T.card := by exact_mod_cast hTn.card_pos
    by_contra hh
    have hz : Ycut.card=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hYmass
    exact (not_le_of_gt (mul_pos htheta hTpos)) hYmass
  have hfill : T.filter (fun z => pair z∈A)=Ycut := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw,he⟩ := mem_image.mp (mem_filter.mp hz).2
      have hk := coarseY_eq_of_point_eq D a m p .oneTwo P hP hd F Fcfg R0 hR0 w.2 z.2
        (congrArg Prod.snd he)
      exact mem_filter.mpr ⟨(mem_filter.mp hz).1,by simpa only [key,hk] using (mem_filter.mp hw).2⟩
    · intro hz
      exact mem_filter.mpr ⟨hYcutT hz,mem_image_of_mem pair hz⟩
  have hmassA : mass A weight=Ycut.card := by
    rw [mass,sum_card_fiberwise_eq_card_filter,hfill]
  obtain ⟨B,hBA,hBn,hhalf,himage,hfib,_hread,hrich⟩ :=
    exists_actual_rich_joint_core D a m p .oneTwo P hP hd F Fcfg R0 u hR0
      (fun _ : Fin 1 => depth) (by norm_num) (fun _ => hdepth) S T hTS Hbase Q3 HP A
      (image_subset_image hYcutT) (hYcutn.image pair)
  let E0 := T.filter (fun z => pair z∈B)
  have hE0T : E0⊆T := filter_subset _ _
  have hhalfR : (Ycut.card:ℝ) ≤ 2*(E0.card:ℝ) := by
    rw [hmassA] at hhalf
    exact_mod_cast hhalf
  have hpost : theta*(T.card:ℝ) ≤ 2*(Q3:ℝ)^2*E0.card :=
    hYmass.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left hhalfR (sq_nonneg (Q3:ℝ)))
  have hQ : (1:ℝ) ≤ Q3 := by
    have hh := NativeSourceSizeBounds.radix_four_le S.card L3
    exact_mod_cast (show 1≤Q3 by dsimp only [Q3]; omega)
  have hF3 : (0:ℝ) < F3 := by exact_mod_cast refinementCost_pos ((d+3)+2) (J+1) L3
  have hquot := NativeRetainedSliceBudgetCosts.quotientCost_pos hq
  have hgraphPos := graphCost_pos Khalf
  have hrowPos := rowConstant_pos
  have hpopPos : 0 < pop := by dsimp only [pop,population]; have ht := h.1.2.1; positivity
  let totalCost := (selectionCost Khalf:ℝ)*quotientCost q*Ccuts*(F3:ℝ)*(2*(Q3:ℝ)^2/theta)
  let retention := (1024*175616*volumeConstant)*totalCost/pop
  have hcost : (Hp.card:ℝ) ≤ totalCost*E0.card := by
    have hgraphR : (Hp.card:ℝ) ≤ (selectionCost Khalf:ℝ)*Hgraph.card := by exact_mod_cast hgraph
    have ht : (T.card:ℝ) ≤ (2*(Q3:ℝ)^2/theta)*E0.card := by
      have hh : (T.card:ℝ) ≤ (2*(Q3:ℝ)^2*E0.card)/theta :=
        (le_div_iff₀ htheta).mpr (by simpa only [mul_comm] using hpost)
      simpa only [div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hh
    calc
      _ ≤ (selectionCost Khalf:ℝ)*Hgraph.card := hgraphR
      _ ≤ (selectionCost Khalf:ℝ)*((quotientCost q*Ccuts)*(F3:ℝ)*T.card) :=
        mul_le_mul_of_nonneg_left hHgraph hgraphPos.le
      _ ≤ (selectionCost Khalf:ℝ)*((quotientCost q*Ccuts)*(F3:ℝ)*((2*(Q3:ℝ)^2/theta)*E0.card)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by positivity)) hgraphPos.le
      _ = _ := by dsimp only [totalCost]; ring
  have hE0ref : E0⊆Eref := hE0T.trans (hTS.trans (hS.trans (filter_subset _ _)))
  have hE0orig : E0⊆incidences original := hE0ref.trans (hEref.trans (filter_subset _ _))
  have hE0parent (z : Fin n × Index) (hz : z∈E0) : z.1∈parentLabels D Rfull a (2^m) p := by
    have he := (NativeOriginalParentDensityCore.retained_spec original Rfull z).mp (hEref (hE0ref hz))
    exact (mem_parentLabels D Rfull a (2^m) p z.1).mpr
      ⟨he.1,(mem_filter.mp (hS (hTS (hE0T hz)))).2⟩
  have htotal : 0 < totalCost := by dsimp only [totalCost]; positivity
  have hratio := (NativeCurrentReferenceIncidenceRetention.retained_incidence_ratio h original horiginal ha
    Rfull Eref Hp E0 m p hReferenceNative hE0orig hE0parent pop totalCost hpopPos htotal hpop hcost).2
  refine ⟨B,hBA,hBn,hE0T,hE0ref,himage,htotal,hcost,hpost,hfib,?_,?_,?_,hratio,?_⟩
  · intro c hc
    simpa only [Nat.cast_one,mul_one] using hrich (0:Fin 1) c hc
  · dsimp only [retention]
    exact div_pos (mul_pos (by have hv := volumeConstant_pos; positivity) htotal) hpopPos
  · exact NativeCurrentReferenceIncidenceSubset.source_incidences_mono D Rfull E0 Eref hE0ref a (2^m) p
  · have hQpow : (Q3:ℝ)^2 ≤ (Q3:ℝ)^4 := pow_le_pow_right₀ hQ (by norm_num : 2 ≤ 4)
    have heq : retention = (128*175616:ℝ)*Ccuts/theta*
        ((selectionCost Khalf:ℝ)*quotientCost q*(F3:ℝ)*(Q3:ℝ)^2/(pop/rowConstant)) := by
      dsimp only [retention,totalCost]
      rw [rowConstant]
      field_simp [hpopPos.ne',htheta.ne',volumeConstant_pos.ne'] <;> ring
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change ((selectionCost Khalf:ℝ)*quotientCost q*(F3:ℝ)*(Q3:ℝ)^2/(pop/rowConstant)) ≤
      ((selectionCost Khalf:ℝ)*quotientCost q*(F3:ℝ)*(Q3:ℝ)^4/(pop/rowConstant))
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hQpow (by positivity)

end NativeThirdReferenceRetentionBudget
