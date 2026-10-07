import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_coarse_pruning_budget
import Theorems.Thm_StickyKakeya4_native_middle_window_balance
import Theorems.Thm_StickyKakeya4_native_remembered_source_construction
import Theorems.Thm_StickyKakeya4_native_same_Q_fine_graph

/- UNVERIFIED consolidated actual same-Q phase/height/shading/union constructor.
Original source units and exact hashes are preserved in the manifest. -/

/- Source unit: native_actual_phase_height_population
   Original SHA256: bd9fa064ca5cb153c94bcbdbed55d85c7867cd5ad38d9b2ef47bfb1fb29ff6bb -/
/- UNVERIFIED source-derived full phase support on the same E1 reference. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeActualPhaseHeightPopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeActualRelativeCoarseAdmission NativeCoarsePruningBudget

/-- Full occupied phase count is derived from original HB populations and
the same admitted E1-parent source. The selected shading is irrelevant. -/
theorem actual_full_phase_card {n : ℕ} {D : FiniteScaleSource n} {eta localEta a zeta profile : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (Rfull : Finset (Fin n)) (level : ℕ) (hzeta : 0 ≤ zeta)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original Rfull a level zeta)
    (Eref : Finset (Fin n × Index)) (m c : ℕ) (hm : m ≤ level) (hc : c ≤ level-m+6) (p : Parent)
    (href : IsWangZakharovNativeFiniteInput (source h Rfull Eref a m p) localEta)
    (hbudget : (64:ℝ)^3*(source h Rfull Eref a m p).thickness^profile ≤ D.thickness^zeta) :
    let Sref := source h Rfull Eref a m p
    (((univ : Finset (Fin (parentLabels D Rfull a (2^m) p).card)).image
      (parentLabel Sref 0 (2^c))).card:ℝ) ≤
        373248*Sref.thickness^(-profile)*(((2^c:ℕ):ℝ))^3 := by
  intro Sref
  obtain ⟨_horiginal,hdy,_ha,_hR,_hcard,_hshade,_hden,_hCW,Hpop⟩ := HB
  have Hlocal := source_population_law h Rfull Eref a zeta profile hzeta level hdy Hpop m hm p href hbudget
  exact original_occupied_count href univ (2^c) (by positivity)
    (fun q hq => (Hlocal ⟨c,by omega⟩ q hq).1)

/-- Every current old relative phase is literally an occupied phase of
that same reference source; no active tube count is replaced by the full one. -/
theorem relative_parent_mem_full {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (Rfull : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m c : ℕ) (p : Parent)
    (i : Fin n) (hi : i∈parentLabels D Rfull a (2^m) p) :
    NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^c) i∈
      (univ : Finset (Fin (parentLabels D Rfull a (2^m) p).card)).image
        (parentLabel (source h Rfull Eref a m p) 0 (2^c)) := by
  have hrange : i∈Set.range (NativePaddedCellSource.originalLabel (parentLabels D Rfull a (2^m) p)) := by
    rw [NativePaddedCellSource.originalLabel_range]
    exact hi
  obtain ⟨j,rfl⟩ := hrange
  exact mem_image.mpr ⟨j,mem_univ j,NativeRelativeParentProfiles.source_parentLabel h Rfull Eref a m p (2^c) j⟩

end NativeActualPhaseHeightPopulation

end -- anonymous noncomputable section of native_actual_phase_height_population

/- Source unit: native_actual_massive_old_phase
   Original SHA256: 92c1e0921a6fe260b44d08e86a97df498d0282234297868ea7a1f641d14c09ca -/
/- UNVERIFIED source consumer. No compiler was run for this draft.

The only phase population estimate used below is
NativeActualPhaseHeightPopulation.actual_full_phase_card, applied to the
same original HB, Rfull, Eref, and admitted source hS as the fine graph.
The selected key is exactly relativeLabel at c, so its fixed factor is
373248. There is no current-parent intercept projection in this key.

The mass selection uses an image-cover inequality, not disjointness of
geometric images. The separate graph-fiber readback uses the unchanged
baseline b0 tube index. No configuration property of cfg is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeActualMassiveOldPhase
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeRelativeParentLabels NativeConfiguredIncidenceFibers
open NativeSameQSourceRestriction NativeSameQFineGraph NativeActualPhaseHeightPopulation
open scoped BigOperators

/-- Images of all original key fibers cover the whole image. The images
may overlap; the estimate does not charge or assume any disjointness. -/
theorem image_card_le_sum_fiber_images {alpha beta gamma : Type*}
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq gamma]
    (T : Finset alpha) (pair : alpha → beta) (key : alpha → gamma) :
    (T.image pair).card ≤
      ∑ q ∈ T.image key, ((T.filter (fun z => key z = q)).image pair).card := by
  have hcover : T.image pair ⊆ (T.image key).biUnion
      (fun q => (T.filter (fun z => key z = q)).image pair) := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
    exact mem_biUnion.mpr ⟨key z, mem_image_of_mem _ hz,
      mem_image_of_mem _ (mem_filter.mpr ⟨hz, rfl⟩)⟩
  exact (card_le_card hcover).trans card_biUnion_le

/-- Filtering original occurrences by one relative c-phase gives the
literal c-phase fiber in the fine graph with its baseline b0 index. -/
theorem graph_filter_relative_phase {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (Rfull : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m b0 c : ℕ)
    (hc : c ≤ b0) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h Rfull Eref a m p) etaS)
    (cfg : Index → E4) (qOld : Parent)
    (hParent : ∀ z ∈ T, z.1 ∈ parentLabels D Rfull a (2 ^ m) p) :
    graph h Rfull Eref a m b0 p hS cfg
        (T.filter (fun z => relativeLabel D a (2 ^ m) p (2 ^ c) z.1 = qOld)) =
      (graph h Rfull Eref a m b0 p hS cfg T).filter
        (fun v => phase h Rfull Eref a m b0 c p v.2 = qOld) := by
  simpa only [NativeSameQSourceRestriction.restrict, mem_singleton] using
    graph_restrict h Rfull Eref T a m b0 c hc p hS cfg {qOld} hParent

/-- Select an actual massive old phase inside the already chosen SAME Q.

Positive mass is the sum of the actual same-Q fine-pair weights. Original
HB and the same admitted Eref-native source supply the full c-phase count;
neither a phase-count certificate nor a final-density certificate is an
input. The current shading T is only required to retain original support
and original parent membership. Every graph below uses the original cfg
and the same b0 outputTube index, including after both restrictions.
-/
theorem from_original_reference_same_Q {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS a zeta profile : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (Rfull : Finset (Fin n))
    (level : ℕ) (hzeta : 0 ≤ zeta)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original Rfull a level zeta)
    (Eref T : Finset (Fin n × Index)) (m b0 b c : ℕ)
    (hm : m ≤ level) (hb0 : b0 ≤ level - m + 6)
    (hcb : c ≤ b) (hbb0 : b ≤ b0) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h Rfull Eref a m p) etaS)
    (hbudget : (64 : ℝ) ^ 3 * (source h Rfull Eref a m p).thickness ^ profile ≤
      D.thickness ^ zeta)
    (hsupport : T ⊆ NativeCubicalIncidenceCounts.incidences original)
    (hParent : ∀ z ∈ T, z.1 ∈ parentLabels D Rfull a (2 ^ m) p)
    (cfg : Index → E4) (Q : Finset Parent)
    (hmassPos : 0 < ∑ q ∈ Q, weight h Rfull Eref a m b0 b p hS cfg T q) :
    let Gfine := fun U : Finset (Fin n × Index) =>
      graph h Rfull Eref a m b0 p hS cfg U
    let TQ := restrict D a m b p Q T
    let allParents :=
      (univ : Finset (Fin (parentLabels D Rfull a (2 ^ m) p).card)).image
        (parentLabel (source h Rfull Eref a m p) 0 (2 ^ c))
    let phaseCap := 373248 * (source h Rfull Eref a m p).thickness ^ (-profile) *
      (((2 ^ c : ℕ) : ℝ)) ^ 3
    ∃ qOld ∈ allParents,
      let A := TQ.filter
        (fun z => relativeLabel D a (2 ^ m) p (2 ^ c) z.1 = qOld)
      A.Nonempty ∧ A ⊆ TQ ∧ A ⊆ T ∧
      A ⊆ NativeCubicalIncidenceCounts.incidences original ∧
      (∀ z ∈ A,
        relativeLabel D a (2 ^ m) p (2 ^ b) z.1 ∈ Q ∧
        relativeLabel D a (2 ^ m) p (2 ^ c) z.1 = qOld) ∧
      (Gfine A).Nonempty ∧
      Gfine A = (Gfine TQ).filter
        (fun v => phase h Rfull Eref a m b0 c p v.2 = qOld) ∧
      (∀ v ∈ Gfine A,
        phase h Rfull Eref a m b0 b p v.2 ∈ Q ∧
        phase h Rfull Eref a m b0 c p v.2 = qOld) ∧
      ((Gfine TQ).card : ℝ) ≤ phaseCap * ((Gfine A).card : ℝ) ∧
      (∑ q ∈ Q, weight h Rfull Eref a m b0 b p hS cfg T q) ≤
        phaseCap * ((Gfine A).card : ℝ) := by
  intro Gfine TQ allParents phaseCap
  let old : Fin n × Index → Parent :=
    fun z => relativeLabel D a (2 ^ m) p (2 ^ c) z.1
  let oldPhases := TQ.image old
  let oldFiber := fun q : Parent => TQ.filter (fun z => old z = q)
  have hc0 : c ≤ b0 := hcb.trans hbb0
  have hcLevel : c ≤ level - m + 6 := hc0.trans hb0
  have hTQT : TQ ⊆ T := filter_subset _ _
  have hParentQ : ∀ z ∈ TQ, z.1 ∈ parentLabels D Rfull a (2 ^ m) p :=
    fun z hz => hParent z (hTQT hz)
  have hFull : (allParents.card : ℝ) ≤ phaseCap :=
    actual_full_phase_card h original Rfull level hzeta HB Eref m c hm hcLevel p hS hbudget
  have hphaseSub : oldPhases ⊆ allParents := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hq
    exact relative_parent_mem_full h Rfull Eref a m c p z.1 (hParentQ z hz)
  have hphaseCard : (oldPhases.card : ℝ) ≤ phaseCap :=
    (Nat.cast_le.mpr (card_le_card hphaseSub)).trans hFull
  have hmass :
      (∑ q ∈ Q, weight h Rfull Eref a m b0 b p hS cfg T q) =
        ((Gfine TQ).card : ℝ) :=
    sum_weight_eq_graph h Rfull Eref T a m b0 b hbb0 p hS cfg Q hParent
  have hGposR : (0 : ℝ) < (Gfine TQ).card := by
    rw [← hmass]
    exact hmassPos
  have hGpos : 0 < (Gfine TQ).card := by exact_mod_cast hGposR
  have hTQn : TQ.Nonempty := by
    obtain ⟨v, hv⟩ := card_pos.mp hGpos
    obtain ⟨z, hz, _he⟩ := mem_image.mp hv
    exact ⟨z, hz⟩
  have hphaseN : oldPhases.Nonempty := hTQn.image old
  obtain ⟨qOld, hqOld, hmax⟩ := exists_max_image oldPhases
    (fun q => (Gfine (oldFiber q)).card) hphaseN
  let A := oldFiber qOld
  have hAn : A.Nonempty := by
    obtain ⟨z, hz, he⟩ := mem_image.mp hqOld
    exact ⟨z, mem_filter.mpr ⟨hz, he⟩⟩
  have hATQ : A ⊆ TQ := filter_subset _ _
  have hAT : A ⊆ T := hATQ.trans hTQT
  have hAsupport : A ⊆ NativeCubicalIncidenceCounts.incidences original :=
    hAT.trans hsupport
  have hOriginal : ∀ z ∈ A,
      relativeLabel D a (2 ^ m) p (2 ^ b) z.1 ∈ Q ∧
      relativeLabel D a (2 ^ m) p (2 ^ c) z.1 = qOld := by
    intro z hz
    exact ⟨(mem_filter.mp (hATQ hz)).2, (mem_filter.mp hz).2⟩
  have hGAn : (Gfine A).Nonempty := hAn.image _
  have hGraphFiber : Gfine A = (Gfine TQ).filter
      (fun v => phase h Rfull Eref a m b0 c p v.2 = qOld) :=
    graph_filter_relative_phase h Rfull Eref TQ a m b0 c hc0 p hS cfg qOld hParentQ
  have hSameQ : Gfine TQ = (Gfine T).filter
      (fun v => phase h Rfull Eref a m b0 b p v.2 ∈ Q) :=
    graph_restrict h Rfull Eref T a m b0 b hbb0 p hS cfg Q hParent
  have hGraphSub : Gfine A ⊆ Gfine TQ := image_subset_image hATQ
  have hGraphPhase : ∀ v ∈ Gfine A,
      phase h Rfull Eref a m b0 b p v.2 ∈ Q ∧
      phase h Rfull Eref a m b0 c p v.2 = qOld := by
    intro v hv
    have hvQ := hGraphSub hv
    have hvOld := hv
    rw [hSameQ] at hvQ
    rw [hGraphFiber] at hvOld
    exact ⟨(mem_filter.mp hvQ).2, (mem_filter.mp hvOld).2⟩
  have hcover : (Gfine TQ).card ≤
      ∑ q ∈ oldPhases, (Gfine (oldFiber q)).card :=
    image_card_le_sum_fiber_images TQ
      (fun z => (cfg z.2, outputTube h Rfull Eref a m b0 p hS z.1)) old
  have hNatCard : (Gfine TQ).card ≤ oldPhases.card * (Gfine A).card := by
    calc
      _ ≤ ∑ q ∈ oldPhases, (Gfine (oldFiber q)).card := hcover
      _ ≤ ∑ _q ∈ oldPhases, (Gfine A).card :=
        sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]
  have hCard : ((Gfine TQ).card : ℝ) ≤ phaseCap * ((Gfine A).card : ℝ) := by
    have hNatCardR : ((Gfine TQ).card : ℝ) ≤
        (oldPhases.card : ℝ) * ((Gfine A).card : ℝ) := by exact_mod_cast hNatCard
    exact hNatCardR.trans
      (mul_le_mul_of_nonneg_right hphaseCard (Nat.cast_nonneg _))
  refine ⟨qOld, hphaseSub hqOld, hAn, hATQ, hAT, hAsupport, hOriginal,
    hGAn, hGraphFiber, hGraphPhase, hCard, ?_⟩
  rw [hmass]
  exact hCard

end NativeActualMassiveOldPhase

end -- anonymous noncomputable section of native_actual_massive_old_phase

/- Source unit: native_remembered_source_shading
   Original SHA256: 2ea98633124bc06942e8cff1d7f9935ed3fe434e0a4010aafc8b84595c28fa96 -/
/- UNVERIFIED actual remembered-source shading construction. The sparse
set T supplies the literal same-Q rows; it need not have native admission.
The output source is the exact one to which rank_two_union applies. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeRememberedSourceShading
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeCoarseReadback
open NativeConfiguredIncidenceFibers NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open CanonicalConfiguredE4Bridge NativeRememberedSourceMaps NativeRememberedHeightSelection
open NativeRememberedOccurrenceReadback NativeRememberedFineCount NativeFineWeightedCoarseCore
open NativeCoarseCellSource NativeCoarseDirectionThinning NativeCoarseSourceParentReadback
open NativeTranslatedGrainHeightOverlap NativeLocalCellCoherence
open scoped BigOperators ENNReal

/-- The actual fine-pair and remembered-height counts pay exactly the
final local cell volume. There is no separate old-height retention charge. -/
lemma count_to_mass {r eps d w sigma p G H M : ℝ}
    (hr : 0 < r) (heps : 0 < eps) (hd : 0 < d) (hw : 0 < w)
    (hscale : sigma=d/w)
    (hG : G ≤ fineCapacity*r^(-p)*(d/eps)^3*H)
    (hH : H ≤ 4096*(sigma/eps)*M) :
    r^p*eps^4*G/(65536*fineCapacity*w^3) ≤ M*(sigma/2)^4 := by
  have hCf := fineCapacity_pos
  calc
    _ = (r^p*eps^4/(65536*fineCapacity*w^3))*G := by ring
    _ ≤ (r^p*eps^4/(65536*fineCapacity*w^3))*
        (fineCapacity*r^(-p)*(d/eps)^3*H) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ ≤ (r^p*eps^4/(65536*fineCapacity*w^3))*
        (fineCapacity*r^(-p)*(d/eps)^3*(4096*(sigma/eps)*M)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hH (by positivity)) (by positivity)
    _ = _ := by
      rw [hscale,Real.rpow_neg hr.le]
      field_simp [heps.ne',hw.ne',hCf.ne',(Real.rpow_pos_of_pos hr p).ne']
      ring

/-- Select a genuine old height per final bin, on the actual same-Q
intermediate source, and derive the total shading lower on its literal
local source. All phase, row, capacity and parent readbacks are performed
here. The retained fine graph keeps its baseline b0 tube indices. -/
theorem select_height_and_shading {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS etaC a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index))
    (level m b0 b c : ℕ) (hm : 6 ≤ m) (hb0 : 8 ≤ b0) (hb : b ≤ b0)
    (hc : c ≤ b) (hc6 : 6 ≤ c)
    (HB : NativeMiddleWindowBalance.HasOriginalBackbone D original R a level zeta)
    (hmb0 : m+b0 ≤ level) (hscale : D.thickness ≤ (rho m)^2) (p : Parent)
    (hp : (parentLabels D R a (2^m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hT : T ⊆ incidences original)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
    (hdim : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (hF : ∀t i j,|F t i j| ≤ 1/4) (hCfg : ∀t i j,|Fcfg t i j| ≤ 1/4)
    (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (hmatch : mu m*(R0:ℝ)=4096/((2^b0:ℕ):ℝ))
    (Hsingle : ∀x∈T,∀y∈T,translatedHeight D a m x.2/((8*R0:ℕ):ℤ)=
      translatedHeight D a m y.2/((8*R0:ℕ):ℤ) → translatedHeight D a m x.2=translatedHeight D a m y.2)
    (Q : Finset Parent)
    (hQ : Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2^b)))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((source h R Eref a m p).line (representative hS univ 0 (2^b) q)))
        (direction ((source h R Eref a m p).line (representative hS univ 0 (2^b) q')))) :
    let C := NativeCoarseCellSource.source hS 0 (level-m+6) b Q
      (representative hS univ 0 (2^b)) (incidences (sourceCells D R T a (2^m) p)) hsep
    ∀hC : IsWangZakharovNativeFiniteInput C etaC,
    let cfg := NativeActualConfiguredPoint.point D a m p s P hP hdim F Fcfg R0
    (∀x∈T.image (fun z => cfg z.2),∀y∈T.image (fun z => cfg z.2),x≠y →
      64/((2^b0:ℕ):ℝ) ≤ dist x y) →
    ∀(A : Finset (Fin n × Index)),A ⊆ T → A.Nonempty →
      (∀z∈A,relativeLabel D a (2^m) p (2^b) z.1∈Q) →
    ∀qOld : Parent,(∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=qOld) →
    let pA := zeroProjection qOld
    let cells := actualRows h R Eref T level m b p hS Q
    let Occ := occurrences h R a m b p hp Q cells A
    ∃B ⊆ Occ.image (taggedKey D a m C c pA),
      (∀v∈B,∀w∈B,finalTime v=finalTime w → v.1=w.1) ∧
      let Efinal := selectedPairs D a m C c pA Occ B
      Efinal.Nonempty ∧ Efinal ⊆ incidences cells ∧
      (∀z∈Efinal,z.1∈parentLabels C univ 0 (2^c) pA) ∧
      Efinal.image (localPair C 0 (2^c) pA)=B.image Prod.snd ∧
      ENNReal.ofReal ((source h R Eref a m p).thickness^pExp*(64/((2^b0:ℕ):ℝ))^4*
        ((NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A).card:ℝ)/
        (65536*fineCapacity*(64/((2^c:ℕ):ℝ))^3)) ≤
        wzTotalShadingVolume (source hC univ Efinal 0 c pA) := by
  intro C hC cfg hpointSep A hAT hAne hAQ qOld hPhase pA cells Occ
  let eps : ℝ := 64/((2^b0:ℕ):ℝ)
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let w : ℝ := 64/((2^c:ℕ):ℝ)
  let sigma : ℝ := ((2^c:ℕ):ℝ)*C.thickness/64
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hw : 0 < w := by dsimp only [w]; positivity
  have hthickness : C.thickness=d := rfl
  have hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale HB.2.1 ⟨m,by omega⟩
  have hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^b:ℕ):ℝ) ≤ 64 := by
    calc
      _ = ((2^(m+b):ℕ):ℝ)*D.thickness := by push_cast; rw [pow_add]; ring
      _ ≤ 1 := NativeCompactAncestorRegularity.dyadic_parent_scale HB.2.1 ⟨m+b,by omega⟩
      _ ≤ 64 := by norm_num
  have hepsd : eps ≤ d := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hb
  have hnc : (64:ℝ) ≤ ((2^c:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hc6
  have hdsigma : C.thickness ≤ sigma := by
    dsimp only [sigma]
    nlinarith only [hnc,hC.1.2.1]
  have hepssigma : eps ≤ sigma := hepsd.trans (by simpa only [hthickness] using hdsigma)
  have hmatchb : mu m*(R0:ℝ) ≤ 4096/((2^b:ℕ):ℝ) := by
    rw [hmatch]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hb
  have hmesh : mu m*(R0:ℝ)=64*eps := by rw [hmatch]; dsimp only [eps]; ring
  have hsigmaread : sigma=d/w := by
    dsimp only [sigma,w]
    rw [hthickness]
    field_simp
  obtain ⟨B,hBO,hret,hCoherent,hImage⟩ := select_actual_old_height h original horiginal ha R m b hm p hp
    hNscale hRelScale Q C hthickness cells A (hAT.trans hT) (fun z hz => hparent z (hAT hz))
    s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatchb eps heps hmesh c pA hdsigma hepssigma
    T hAT Hsingle
  let Efinal := selectedPairs D a m C c pA Occ B
  change ((Occ.image (taggedKey D a m C c pA)).card:ℝ) ≤
    (4096*(sigma/eps))*((Efinal.image (localPair C 0 (2^c) pA)).card:ℝ) at hret
  have hsigma : 0 < sigma := by rw [hsigmaread]; positivity
  have hFine := fine_graph_le_tagged h original horiginal ha R Eref T level m b0 b hm hb0 hb
    HB hmb0 hscale p hp hS hbudget hT hparent s P hP hdim F Fcfg hF hCfg R0 hR0 hbase hmatch
    Q C c pA A hAT hAQ hpointSep
  change ((NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A).card:ℝ) ≤
    fineCapacity*(source h R Eref a m p).thickness^(-pExp)*(d/eps)^3*
      ((Occ.image (taggedKey D a m C c pA)).card:ℝ) at hFine
  have hCard := count_to_mass hS.1.2.1 heps hd hw hsigmaread hFine hret
  have hEinc : Efinal ⊆ incidences cells := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    exact ((mem_occurrences h R a m b p hp Q cells A z).mp (mem_filter.mp hz).1).1
  have hCurrent := occurrence_current_parent h R Eref T level m b p hp hS Q hQ hsep A c hc qOld hPhase
  have hParentFinal : ∀v∈Efinal,v.1∈parentLabels C univ 0 (2^c) pA := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    exact (mem_parentLabels C univ 0 (2^c) pA _).mpr
      ⟨mem_univ _,hCurrent z (mem_filter.mp hz).1⟩
  have hEne : Efinal.Nonempty := by
    by_contra hEmpty
    have hEmpty' : Efinal=∅ := not_nonempty_iff_eq_empty.mp hEmpty
    have hretZero : ((Occ.image (taggedKey D a m C c pA)).card:ℝ) ≤ 0 := by
      simpa only [hEmpty',image_empty,card_empty,Nat.cast_zero,mul_zero] using hret
    have htags : ((Occ.image (taggedKey D a m C c pA)).card:ℝ)=0 :=
      le_antisymm hretZero (Nat.cast_nonneg _)
    rw [htags,mul_zero] at hFine
    have hgpos : (0:ℝ) < (NativeSameQFineGraph.graph h R Eref a m b0 p hS cfg A).card := by
      exact_mod_cast card_pos.mpr (hAne.image _)
    linarith only [hFine,hgpos]
  refine ⟨B,hBO,hCoherent,hEne,hEinc,hParentFinal,hImage,?_⟩
  rw [source_total_shading hC univ Efinal 0 c pA hParentFinal]
  have hlocalMesh : ((2^c:ℕ):ℝ)*C.thickness/128=sigma/2 := by dsimp only [sigma]; ring
  rw [hlocalMesh]
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_pow (half_pos hsigma).le,
    ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hCard

end NativeRememberedSourceShading

end -- anonymous noncomputable section of native_remembered_source_shading

/- Source unit: native_remembered_source_realization
   Original SHA256: a36e18018f75e19091d7cb9e4e93e940db805b4090fc89b9586b4e87d1238041 -/
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

/-- The advertised power form follows from the actual same-Q fine mass. -/
lemma power_payment {r eps p z H : ℝ} (hr : 0 < r)
    (hMass : r^(3*z)/2 ≤ eps^4*H) :
    r^(3*z+2*p)/(131072*phaseConstant*fineCapacity) ≤
      r^(2*p)*eps^4*H/(65536*phaseConstant*fineCapacity) := by
  have hCf := fineCapacity_pos
  have hC : 0 < phaseConstant := by norm_num [phaseConstant]
  have hh := mul_le_mul_of_nonneg_left hMass
    (show 0 ≤ r^(2*p)/(65536*phaseConstant*fineCapacity) by positivity)
  calc
    _ = (r^(2*p)/(65536*phaseConstant*fineCapacity))*(r^(3*z)/2) := by
      rw [Real.rpow_add hr]
      ring
    _ ≤ (r^(2*p)/(65536*phaseConstant*fineCapacity))*(eps^4*H) := hh
    _ = _ := by ring

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
  have hUnion := NativeRememberedSourceUnion.rank_two_union h original horiginal ha R Eref m level hm
    HB.2.1 hf hscale p hRef hRefK (level-m+6) b0 c depth hb0 (by omega) hdepth hwidth
    plane E Hgraph S0 T0 hT0 hparent P hP hd Fraw Fcfg hCfg population PL PU Qref lambda Gcost Cpre
    threshold L3 Rel Hdata R0 Rd hR0 (by omega) hbase hmatch.le hsmall hquery hkappa A
    (hATcur.trans hcur) qOld (fun z hz => (hPhase z hz).2) b hb hNscale hRelScale Q C hC cells
    hCells hCommon hCthick hRd512 hRdMesh pA hSigma B hBO hCoherent hParentFinal
  have hPhasePaid : WQ ≤ phaseConstant*(source h R Eref a m p).thickness^(-pExp)/
      (64/((2^c:ℕ):ℝ))^3*((NativeSameQFineGraph.graph h R Eref a m b0 p hRef cfg A).card:ℝ) := by
    convert hMass using 1
    dsimp only [phaseConstant]
    field_simp
    ring
  have hLower := massive_phase_payment hRef.1.2.1
    (by positivity : 0 < 64/((2^b0:ℕ):ℝ)) (by positivity : 0 < 64/((2^c:ℕ):ℝ)) hPhasePaid
  refine ⟨qOld,A,hATcur,hAne,hPhase,B,hBO,hCoherent,hEne,hEinc,hParentFinal,?_,hUnion⟩
  exact (ENNReal.ofReal_le_ofReal hLower).trans hShade

end NativeRememberedSourceRealization

end -- anonymous noncomputable section of native_remembered_source_realization
