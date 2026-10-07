import Theorems.Thm_StickyKakeya4_native_actual_raw_weight_source
import Theorems.Thm_StickyKakeya4_native_raw_height_source_adapter
import Theorems.Thm_StickyKakeya4_native_remembered_source_mass_construction

/- UNVERIFIED actual raw-incidence remembered-source realization.
The mass remains on original (tube, original cell) incidences. The same
actual intermediate Q rows supply the final local source; the unchanged
third-core reference supplies its hereditary union upper. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeActualRawRememberedSource
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeLocalParentSource NativeRelativeParentLabels NativeRelativeParentProfiles
open NativeRelativeCoarseReadback NativeRelativeCoarsePointMenu NativeMiddleWindowBalance
open NativeRememberedSourceMaps NativeRememberedOccurrenceReadback NativeRawHeightSourceAdapter
open NativeRawIncidenceHeightPopulationDraft2123 NativeActualRawWeightSource
open NativeActualPhaseHeightPopulation NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeCoarseDirectionThinning NativeCoarseSourceParentReadback NativeLocalCellCoherence
open NativeTranslatedGrainHeightOverlap NativeThirdXYData NativeReferenceXYGridField
open NativeSquaredGrainQueries NativeRetainedSliceCore NativeGrainQuotientFibers
open NativeFixedCompactKakeyaExponent CanonicalConfiguredE4Bridge
open scoped BigOperators ENNReal

/-- Choose a massive old phase using the original raw incidence partition.
The phase alphabet is bounded by the actual same-reference HB population. -/
theorem massive_old_phase {n : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (hzeta : 0 ≤ zeta)
    (HB : HasOriginalBackbone D original R a level zeta)
    (Eref T : Finset (Fin n × Index)) (m b c : ℕ)
    (hm : m ≤ level) (hc : c ≤ level-m+6) (p : Parent)
    (hRef : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (Q : Finset Parent) (hTQ : (NativeSameQSourceRestriction.restrict D a m b p Q T).Nonempty) :
    let TQ := NativeSameQSourceRestriction.restrict D a m b p Q T
    ∃qOld : Parent,∃A : Finset (Fin n × Index),A ⊆ TQ ∧ A.Nonempty ∧
      (∀z∈A,relativeLabel D a (2^m) p (2^b) z.1∈Q ∧
        relativeLabel D a (2^m) p (2^c) z.1=qOld) ∧
      normalization D m*(TQ.card:ℝ) ≤
        NativeRememberedSourceRealization.phaseConstant*(source h R Eref a m p).thickness^(-pExp)/
          (64/((2^c:ℕ):ℝ))^3*(normalization D m*(A.card:ℝ)) := by
  intro TQ
  let f := fun z : Fin n × Index => relativeLabel D a (2^m) p (2^c) z.1
  let phases := TQ.image f
  have hfull := actual_full_phase_card h original R level hzeta HB Eref m c hm hc p hRef hbudget
  have hsub : phases ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2^c)) := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    exact relative_parent_mem_full h R Eref a m c p z.1 (hparent z (mem_filter.mp hz).1)
  have hcount := (Nat.cast_le.mpr (card_le_card hsub)).trans hfull
  obtain ⟨q,hq,hmax⟩ := exists_max_image phases
    (fun q => (TQ.filter (fun z => f z=q)).card) (hTQ.image f)
  let A := TQ.filter (fun z => f z=q)
  have hAne : A.Nonempty := by
    obtain ⟨z,hz,he⟩ := mem_image.mp hq
    exact ⟨z,mem_filter.mpr ⟨hz,he⟩⟩
  have hcard : TQ.card ≤ phases.card*A.card := by
    calc
      _ = ∑q∈phases,(TQ.filter (fun z => f z=q)).card := card_eq_sum_card_image f TQ
      _ ≤ ∑_q∈phases,A.card := sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
  have hreal : (TQ.card:ℝ) ≤
      (373248*(source h R Eref a m p).thickness^(-pExp)*(((2^c:ℕ):ℝ))^3)*(A.card:ℝ) :=
    (show (TQ.card:ℝ) ≤ (phases.card:ℝ)*(A.card:ℝ) by exact_mod_cast hcard).trans
      (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _))
  have hnu : 0 ≤ normalization D m := by
    unfold normalization
    have hdelta := h.1.2.1
    positivity
  refine ⟨q,A,filter_subset _ _,hAne,?_,?_⟩
  · intro z hz
    exact ⟨(mem_filter.mp (mem_filter.mp hz).1).2,(mem_filter.mp hz).2⟩
  · have hh := mul_le_mul_of_nonneg_left hreal hnu
    convert hh using 1
    unfold NativeRememberedSourceRealization.phaseConstant
    field_simp
    ring

/-- A raw tag fixes the actual intermediate tube parent and the exact
original integer height. The original-occurrence map is injective, so the
HB raw-height atom bound applies without a configured-point fiber tax. -/
theorem occurrence_tagged_bound {n : ℕ} {D : FiniteScaleSource n} {eta a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (Eref A : Finset (Fin n × Index)) (m b c : ℕ) (hm : 6 ≤ m) (hmb : m+b ≤ level)
    (p : Parent) (hp : (parentLabels D R a (2^m) p).Nonempty)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hA : A ⊆ incidences original) (hparent : ∀z∈A,z.1∈parentLabels D R a (2^m) p)
    (Q : Finset Parent) (cells : Fin Q.card → Finset Index)
    (C : FiniteScaleSource Q.card) (pA : Parent) :
    let O := occurrences h R a m b p hp Q cells A
    normalization D m*(O.card:ℝ) ≤ D.thickness*(source h R Eref a m p).thickness^(-pExp)*
      (64/((2^b:ℕ):ℝ))^3*((O.image (rawTaggedKey C c pA)).card:ℝ) := by
  intro O
  let r := (source h R Eref a m p).thickness
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let f := rawTaggedKey C c pA
  have hr : 0 < r := by
    change 0 < ((2^m:ℕ):ℝ)*D.thickness/64
    have hdelta := h.1.2.1
    positivity
  have hcap (v : ℤ × (Fin Q.card × Index)) :
      ((O.filter (fun z => f z=v)).card:ℝ) ≤ r^(-pExp)*(d/r)^3 := by
    let V := O.filter (fun z => f z=v)
    let B := V.image Prod.snd
    have hcard : B.card=V.card := card_image_iff.mpr
      ((occurrence_original_injective h R a m b p hp Q cells A).mono (filter_subset _ _))
    have hBO : ∀z∈V,z∈O := fun z hz => (mem_filter.mp hz).1
    have hOriginal : B ⊆ incidences original := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact hA ((mem_occurrences h R a m b p hp Q cells A w).mp (hBO w hw)).2.1
    have hTube : ∀z∈B,z.1∈relativeAtom D R a (2^m) p (2^b)
        (NativeCoarseCellSource.parentIndex Q v.2.1) := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      have hwo := (mem_occurrences h R a m b p hp Q cells A w).mp (hBO w hw)
      have he := congrArg (fun t : ℤ × (Fin Q.card × Index) => t.2.1) (mem_filter.mp hw).2
      change w.1.1=v.2.1 at he
      refine mem_filter.mpr ⟨hparent w.2 hwo.2.1,?_⟩
      rw [←hwo.2.2.1,he]
    have hHeight : ∀z∈B,z.2 3=v.1 := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact congrArg Prod.fst (mem_filter.mp hw).2
    have hh := (actual_relative_raw_capacities h original R level HB Eref m b hm hmb p
      (NativeCoarseCellSource.parentIndex Q v.2.1) hbudget).1 B hOriginal hTube v.1 hHeight
    rw [hcard] at hh
    exact hh
  have hcard : (O.card:ℝ)=∑v∈O.image f,((O.filter (fun z => f z=v)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image f O
  have hsum : (O.card:ℝ) ≤ r^(-pExp)*(d/r)^3*((O.image f).card:ℝ) := by
    rw [hcard]
    calc
      _ ≤ ∑_v∈O.image f,r^(-pExp)*(d/r)^3 := sum_le_sum (fun v _hv => hcap v)
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  have hnu : normalization D m=D.thickness*r^3 := rfl
  rw [hnu]
  calc
    _ ≤ (D.thickness*r^3)*(r^(-pExp)*(d/r)^3*((O.image f).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by have hdelta := h.1.2.1; positivity)
    _ = _ := by field_simp [hr.ne']; ring

/-- The final time bin bounds TRUE original k3 labels by its actual floor
formula, with the two earlier rounded height maps kept visible. -/
theorem occurrence_raw_heights_per_bin {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (m b c : ℕ)
    (p : Parent) (hp : (parentLabels D R a (2^m) p).Nonempty)
    (Q : Finset Parent) (cells : Fin Q.card → Finset Index) (A : Finset (Fin n × Index))
    (C : FiniteScaleSource Q.card) (hC : C.thickness=64/((2^b:ℕ):ℝ)) (pA : Parent)
    (hFine : D.thickness ≤ ((2^m:ℕ):ℝ)*D.thickness/64)
    (hScale : ((2^m:ℕ):ℝ)*D.thickness/64 ≤ 64/((2^b:ℕ):ℝ))
    (hSigma : 64/((2^b:ℕ):ℝ) ≤ ((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64)
    (j : ℤ) :
    let O := occurrences h R a m b p hp Q cells A
    (((((O.image (rawTaggedKey C c pA)).filter (fun v => finalTime v=j)).image Prod.fst).card:ℝ) ≤
      (268435456*((((2^c:ℕ):ℝ)*(64/((2^b:ℕ):ℝ))/64))/D.thickness:ℝ) := by
  intro O
  let V := O.filter (fun z => finalTime (rawTaggedKey C c pA z)=j)
  have he : ((O.image (rawTaggedKey C c pA)).filter (fun v => finalTime v=j)).image Prod.fst=
      V.image (fun z => z.2.2 (3:Fin 4)) := by
    ext t
    constructor
    · intro ht
      obtain ⟨v,hv,hvt⟩ := mem_image.mp ht
      obtain ⟨w,hw,hwv⟩ := mem_image.mp (mem_filter.mp hv).1
      refine mem_image.mpr ⟨w,mem_filter.mpr ⟨hw,?_⟩,?_⟩
      · rw [hwv]
        exact (mem_filter.mp hv).2
      · exact (congrArg Prod.fst hwv).trans hvt
    · intro ht
      obtain ⟨w,hw,hwt⟩ := mem_image.mp ht
      exact mem_image.mpr ⟨rawTaggedKey C c pA w,
        mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hw).1,(mem_filter.mp hw).2⟩,hwt⟩
  rw [he]
  apply final_time_original_height_count h.1.2.1 a (2^m) (2^b) (2^c)
    (by positivity) (by positivity) (by positivity) p C hC pA V (fun z => z.2.2) (fun z => z.2.1)
    (fun z => originalRepresentative h R a m p hp (2^b)
      (relativeLabel D a (2^m) p (2^b) z.2.1)) (fun z => z.1.1) hFine hScale hSigma j
  intro z hz
  have ho := (mem_occurrences h R a m b p hp Q cells A z).mp (mem_filter.mp hz).1
  have hh := (mem_filter.mp hz).2
  change NativeLocalParentCells.cellLabel C 0 (2^c) pA z.1.1 z.1.2 3=j at hh
  rw [ho.2.2.2] at hh
  exact hh

/-- The raw height-selection loss is paid by the literal final cell volume.
Its original delta factor cancels, leaving only a fixed constant. -/
lemma count_to_mass {delta r d w sigma p G H M : ℝ}
    (hdelta : 0 < delta) (hr : 0 < r) (hd : 0 < d) (hw : 0 < w) (hscale : sigma=d/w)
    (hG : G ≤ delta*r^(-p)*d^3*H)
    (hH : H ≤ 268435456*(sigma/delta)*M) :
    r^p*G/(4294967296*w^3) ≤ M*(sigma/2)^4 := by
  calc
    _ = (r^p/(4294967296*w^3))*G := by ring
    _ ≤ (r^p/(4294967296*w^3))*(delta*r^(-p)*d^3*H) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ ≤ (r^p/(4294967296*w^3))*(delta*r^(-p)*d^3*(268435456*(sigma/delta)*M)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH (by positivity)) (by positivity)
    _ = _ := by
      rw [hscale,Real.rpow_neg hr.le]
      field_simp [hdelta.ne',hw.ne',(Real.rpow_pos_of_pos hr p).ne']
      ring

/-- Select one true original k3 per final bin and construct the literal local
source from the SAME intermediate Q rows. Every mass capacity is derived
from original HB incidences; no configured-point separation is consumed. -/
theorem select_raw_height_and_shading {n : ℕ} {D : FiniteScaleSource n}
    {eta etaS etaC a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (Eref T : Finset (Fin n × Index)) (level m b c : ℕ)
    (hm : 6 ≤ m) (hmb : m+b ≤ level) (hc : c ≤ b) (hc6 : 6 ≤ c)
    (HB : HasOriginalBackbone D original R a level zeta) (p : Parent)
    (hp : (parentLabels D R a (2^m) p).Nonempty)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hT : T ⊆ incidences original) (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (Q : Finset Parent)
    (hQ : Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2^b)))
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((source h R Eref a m p).line (representative hS univ 0 (2^b) q)))
        (direction ((source h R Eref a m p).line (representative hS univ 0 (2^b) q')))) :
    let C := NativeCoarseCellSource.source hS 0 (level-m+6) b Q
      (representative hS univ 0 (2^b)) (incidences (sourceCells D R T a (2^m) p)) hsep
    ∀hC : IsWangZakharovNativeFiniteInput C etaC,
    ∀(A : Finset (Fin n × Index)),A ⊆ T → A.Nonempty →
      (∀z∈A,relativeLabel D a (2^m) p (2^b) z.1∈Q) →
    ∀qOld : Parent,(∀z∈A,relativeLabel D a (2^m) p (2^c) z.1=qOld) →
    let pA := zeroProjection qOld
    let cells := actualRows h R Eref T level m b p hS Q
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
      ENNReal.ofReal ((source h R Eref a m p).thickness^pExp*
        (normalization D m*(A.card:ℝ))/(4294967296*(64/((2^c:ℕ):ℝ))^3)) ≤
        wzTotalShadingVolume (source hC univ Efinal 0 c pA) := by
  intro C hC A hAT hAne hAQ qOld hPhase pA cells Occ
  let r := (source h R Eref a m p).thickness
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  let w : ℝ := 64/((2^c:ℕ):ℝ)
  let sigma : ℝ := ((2^c:ℕ):ℝ)*C.thickness/64
  have hr : 0 < r := hS.1.2.1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hw : 0 < w := by dsimp only [w]; positivity
  have hthickness : C.thickness=d := rfl
  have hnc : (64:ℝ) ≤ ((2^c:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hc6
  have hnm : (64:ℝ) ≤ ((2^m:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hm
  have hFine : D.thickness ≤ ((2^m:ℕ):ℝ)*D.thickness/64 := by
    nlinarith only [mul_le_mul_of_nonneg_right hnm h.1.2.1.le]
  have hScale : ((2^m:ℕ):ℝ)*D.thickness/64 ≤ d := by
    have hh := NativeSameReferenceChartBounds.source_scale_guard (a:=a) h R Eref level m b p HB.2.1 hmb
    apply (le_div_iff₀ (show (0:ℝ) < ((2^b:ℕ):ℝ) by positivity)).mpr
    change r*((2^b:ℕ):ℝ) ≤ 64
    change ((2^b:ℕ):ℝ)*r ≤ 1 at hh
    linarith only [hh]
  have hdsigma : d ≤ sigma := by
    dsimp only [sigma]
    rw [hthickness]
    nlinarith only [mul_le_mul_of_nonneg_right hnc hd.le]
  have hsigmaread : sigma=d/w := by
    dsimp only [sigma,w]
    rw [hthickness]
    field_simp
  have hsigma : 0 < sigma := by rw [hsigmaread]; positivity
  have hRawHeights := occurrence_raw_heights_per_bin h R m b c p hp Q cells A C rfl pA
    hFine hScale hdsigma
  obtain ⟨B,hBO,hret,hRawCoherent,hBT,hCoherent,hImage⟩ := select_raw_height D a m C c pA Occ
    (K:=268435456*sigma/D.thickness) (by positivity) hRawHeights
  let Efinal := selectedPairs D a m C c pA Occ (translatedTags D a m B)
  have hrestrict : NativeSameQSourceRestriction.restrict D a m b p Q A=A :=
    filter_eq_self.mpr (fun z hz => hAQ z hz)
  have hOcc : Occ.card=A.card := by
    rw [actual_occurrences_card h R Eref T level m b p hp hS hparent HB.2.1
      (by omega) (by omega) Q A hAT,hrestrict]
  have hRaw := occurrence_tagged_bound h original R level HB Eref A m b c hm hmb p hp hbudget
    (hAT.trans hT) (fun z hz => hparent z (hAT hz)) Q cells C pA
  change normalization D m*(Occ.card:ℝ) ≤ D.thickness*r^(-pExp)*d^3*
    ((Occ.image (rawTaggedKey C c pA)).card:ℝ) at hRaw
  rw [hOcc] at hRaw
  have hret' : ((Occ.image (rawTaggedKey C c pA)).card:ℝ) ≤
      268435456*(sigma/D.thickness)*((Efinal.image (localPair C 0 (2^c) pA)).card:ℝ) := by
    simpa only [div_eq_mul_inv,mul_assoc] using hret
  have hMass := count_to_mass h.1.2.1 hr hd hw hsigmaread hRaw hret'
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
  have hNu : 0 < normalization D m := by
    unfold normalization
    have hdelta := h.1.2.1
    positivity
  have hApos : (0:ℝ) < A.card := by exact_mod_cast card_pos.mpr hAne
  have hEne : Efinal.Nonempty := by
    by_contra hEmpty
    have he : Efinal=∅ := not_nonempty_iff_eq_empty.mp hEmpty
    have hpos : 0 < r^pExp*(normalization D m*(A.card:ℝ))/(4294967296*w^3) := by positivity
    have hz : r^pExp*(normalization D m*(A.card:ℝ))/(4294967296*w^3) ≤ 0 := by
      simpa only [he,image_empty,card_empty,Nat.cast_zero,zero_mul] using hMass
    exact (not_lt_of_ge hz) hpos
  refine ⟨B,hBO,hRawCoherent,hBT,hCoherent,hEne,hEinc,hParentFinal,hImage,?_⟩
  rw [source_total_shading hC univ Efinal 0 c pA hParentFinal]
  have hlocalMesh : ((2^c:ℕ):ℝ)*C.thickness/128=sigma/2 := by dsimp only [sigma]; ring
  rw [hlocalMesh]
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_pow (half_pos hsigma).le,
    ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hMass

/-- Pay the single actual raw massive-phase choice. -/
lemma phase_mass_payment {r w W A p : ℝ} (hr : 0 < r) (hw : 0 < w)
    (hMass : W ≤ NativeRememberedSourceRealization.phaseConstant*r^(-p)/w^3*A) :
    r^(2*p)*W/(4294967296*NativeRememberedSourceRealization.phaseConstant) ≤
      r^p*A/(4294967296*w^3) := by
  have hC : 0 < NativeRememberedSourceRealization.phaseConstant := by
    norm_num [NativeRememberedSourceRealization.phaseConstant]
  calc
    _ = (r^(2*p)/(4294967296*NativeRememberedSourceRealization.phaseConstant))*W := by ring
    _ ≤ (r^(2*p)/(4294967296*NativeRememberedSourceRealization.phaseConstant))*
        (NativeRememberedSourceRealization.phaseConstant*r^(-p)/w^3*A) :=
      mul_le_mul_of_nonneg_left hMass (by positivity)
    _ = _ := by
      rw [show 2*p=p+p by ring,Real.rpow_add hr,Real.rpow_neg hr.le]
      field_simp [hw.ne',hC.ne',(Real.rpow_pos_of_pos hr p).ne']
      ring

/-- Simultaneously construct the actual raw remembered source and its two
volume bounds. Tcur supplies the unchanged SAME-Q rows; T0 supplies the
complete rank-two XY reference. The selected B retains true original k3. -/
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
  have hUnion := NativeRememberedSourceUnion.rank_two_union h original horiginal ha R Eref m level hm
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

end NativeActualRawRememberedSource
end
