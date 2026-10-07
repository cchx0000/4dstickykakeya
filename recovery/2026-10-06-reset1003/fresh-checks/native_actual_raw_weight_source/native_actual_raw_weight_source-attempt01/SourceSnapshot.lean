import Theorems.Thm_StickyKakeya4_native_raw_incidence_height_population_draft_2123
import Theorems.Thm_StickyKakeya4_native_same_Q_shadow_mass
import Theorems.Thm_StickyKakeya4_native_fine_weighted_coarse_core
import Theorems.Thm_StickyKakeya4_native_actual_sparse_reference_admission
import Theorems.Thm_StickyKakeya4_native_original_incidence_mass_lower

/- UNVERIFIED actual ORIGINAL-incidence weights and same-Q admission.
The weights count original T, not its deduplicated sourceCells image.
All geometric capacities are derived from the actual raw source reader. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeActualRawWeightSource
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts
open NativeOriginalParentDensityCore NativeLocalParentSource NativeRelativeParentLabels
open NativeRelativeParentProfiles NativeRelativeCoarseReadback NativeRelativeCoarsePointMenu
open NativeMiddleWindowBalance NativeSameQSourceRestriction NativeFineWeightedCoarseCore
open NativeActualSparseReferenceAdmission NativeOriginalIncidenceMassLower
open NativeRawIncidenceHeightPopulationDraft2123 NativeActivePhasePopulation
open NativeCoarsePowerWindow NativeCoarseRelativeCW NativeDyadicParentCells NativeUnitParentNormalization
open scoped BigOperators ENNReal

/-- The actual one-T parent witness is used only through its two true
cardinality bounds. No identity Hp=parentEdges H p is requested. -/
theorem raw_cardinality_lower {n : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref Hp T : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (population cost : ℝ) (hpopulation : 0 < population) (hcost : 0 < cost)
    (hparent : population*(parentLabels D R a (2^m) p).card ≤
      D.thickness*Hp.card)
    (hretain : (Hp.card:ℝ) ≤ cost*T.card) :
    (population/cost)*(source h R Eref a m p).thickness^etaRef ≤
      D.thickness*(source h R Eref a m p).thickness^3*(T.card:ℝ) := by
  let r := (source h R Eref a m p).thickness
  have hr : 0 < r := href.1.2.1
  have hn := native_volume_population_lower href
  have hpar : population*(parentLabels D R a (2^m) p).card ≤ D.thickness*cost*T.card :=
    hparent.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hretain h.1.2.1.le)
  calc
    _ ≤ (population/cost)*(r^3*(parentLabels D R a (2^m) p).card) :=
      mul_le_mul_of_nonneg_left hn (div_nonneg hpopulation.le hcost.le)
    _ = (r^3/cost)*(population*(parentLabels D R a (2^m) p).card) := by ring
    _ ≤ (r^3/cost)*(D.thickness*cost*T.card) :=
      mul_le_mul_of_nonneg_left hpar (by positivity)
    _ = (r^3*D.thickness*(T.card:ℝ))*(cost/cost) := by ring
    _ = r^3*D.thickness*(T.card:ℝ) := by rw [div_self hcost.ne',mul_one]
    _ = _ := by
      change r^3*D.thickness*(T.card:ℝ)=D.thickness*r^3*(T.card:ℝ)
      ring

/-- Direct Hp-cardinality version of the same etaRef/window payment.
This consumes the actual one-T witness without asserting a filter identity. -/
theorem paid_raw_cardinality_lower {n : ℕ} {D : FiniteScaleSource n} {eta etaRef a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref Hp T : Finset (Fin n × Index)) (m : ℕ) (p : Parent)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (population cost : ℝ) (hpopulation : 0 < population) (hcost : 0 < cost)
    (hparent : population*(parentLabels D R a (2^m) p).card ≤
      D.thickness*Hp.card)
    (hretain : (Hp.card:ℝ) ≤ cost*T.card)
    (eps eB window : ℝ) (heps : 0 < eps) (heB : 0 < eB) (_hwindow : 0 < window)
    (hetaRef : etaRef ≤ window*eB/256)
    (hscale : eps ≤ (source h R Eref a m p).thickness^window)
    (hF : retentionFactor cost population ≤ eps^(-(eB/32))) :
    retentionConstant*eps^(9*eB/256) ≤
      D.thickness*(source h R Eref a m p).thickness^3*(T.card:ℝ) := by
  let r := (source h R Eref a m p).thickness
  have hr : 0 < r := href.1.2.1
  have hr1 : r ≤ 1 := href.1.2.2.1
  have hpay : retentionFactor cost population*eps^(eB/32) ≤ 1 := by
    rw [Real.rpow_neg heps.le,←one_div] at hF
    exact (le_div_iff₀ (Real.rpow_pos_of_pos heps (eB/32))).mp hF
  have hCoefficient : retentionConstant*eps^(eB/32) ≤ population/cost := by
    calc
      _ = (population/cost)*(retentionFactor cost population*eps^(eB/32)) := by
        unfold retentionFactor retentionConstant
        field_simp [hcost.ne',hpopulation.ne']
      _ ≤ (population/cost)*1 := mul_le_mul_of_nonneg_left hpay (by positivity)
      _ = _ := mul_one _
  have hReferencePower : eps^(eB/256) ≤ r^etaRef := by
    have hh := Real.rpow_le_rpow heps.le hscale (show 0 ≤ eB/256 by positivity)
    have he : ((source h R Eref a m p).thickness^window)^(eB/256)=r^(window*eB/256) := by
      rw [←Real.rpow_mul hr.le]
      congr 1
      ring
    rw [he] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_ge hr hr1 hetaRef)
  have hraw := raw_cardinality_lower h R Eref Hp T m p href population cost hpopulation hcost hparent hretain
  calc
    _ = (retentionConstant*eps^(eB/32))*eps^(eB/256) := by
      rw [mul_assoc,←Real.rpow_add heps]
      congr 2
      ring
    _ ≤ (population/cost)*r^etaRef :=
      mul_le_mul hCoefficient hReferencePower (Real.rpow_nonneg heps.le _) (by positivity)
    _ ≤ _ := hraw


/-- deltaOriginal times the cube of the actual Eref-parent thickness. -/
def normalization {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) : ℝ :=
  D.thickness*(((2^m:ℕ):ℝ)*D.thickness/64)^3

def rawWeight {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m b : ℕ) (p : Parent)
    (T : Finset (Fin n × Index)) (q : Parent) : ℝ :=
  normalization D m*((T.filter (fun z => relativeLabel D a (2^m) p (2^b) z.1=q)).card:ℝ)

/-- Restriction by Q preserves the exact ORIGINAL raw mass. -/
theorem sum_raw_weight {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m b : ℕ)
    (p : Parent) (T : Finset (Fin n × Index)) (Q : Finset Parent) :
    (∑q∈Q,rawWeight D a m b p T q)=normalization D m*
      ((NativeSameQSourceRestriction.restrict D a m b p Q T).card:ℝ) := by
  let f := fun z : Fin n × Index => relativeLabel D a (2^m) p (2^b) z.1
  have hc : (T.filter (fun z => f z∈Q)).card=∑q∈Q,(T.filter (fun z => f z=q)).card := by
    rw [card_eq_sum_card_fiberwise (fun z hz => (mem_filter.mp hz).2)]
    apply sum_congr rfl
    intro q hq
    congr 1
    ext z
    simp only [mem_filter]
    constructor
    · exact fun hz => ⟨hz.1.1,hz.2⟩
    · exact fun hz => ⟨⟨hz.1,by rw [hz.2]; exact hq⟩,hz.2⟩
  have hr : ((T.filter (fun z => f z∈Q)).card:ℝ)=
      ∑q∈Q,((T.filter (fun z => f z=q)).card:ℝ) := by exact_mod_cast hc
  simp only [rawWeight,←mul_sum]
  rw [←hr]
  rfl

/-- The full actual Eref-parent alphabet contains every original T tube. -/
theorem total_raw_weight {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (m b : ℕ) (p : Parent)
    (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p) :
    (∑q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2^b)),rawWeight D a m b p T q)=
      normalization D m*(T.card:ℝ) := by
  rw [sum_raw_weight]
  congr 1
  apply congrArg (fun A : Finset (Fin n × Index) => (A.card:ℝ))
  apply filter_eq_self.mpr
  intro z hz
  have hi : z.1∈Set.range (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p)) := by
    rw [NativePaddedCellSource.originalLabel_range]
    exact hparent z hz
  obtain ⟨i,hi⟩ := hi
  refine mem_image.mpr ⟨i,mem_univ _,?_⟩
  rw [NativeRelativeParentProfiles.source_parentLabel,hi]

/-- Every fiber is an actual original-incidence fiber of doublePair.
The HB-derived raw capacity is summed without replacing the original mass
by the cardinality of sourceCells(T). -/
theorem raw_shadow_card_bound {n : ℕ} {D : FiniteScaleSource n} {eta a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (Eref T : Finset (Fin n × Index)) (m b : ℕ) (hm : 6 ≤ m) (hmb : m+b ≤ level)
    (p : Parent) (hp : (parentLabels D R a (2^m) p).Nonempty)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hT : T ⊆ incidences original) (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p) :
    normalization D m*(T.card:ℝ) ≤ 87808*(source h R Eref a m p).thickness^(-pExp)*
      (64/((2^b:ℕ):ℝ))^4*((T.image (doublePair h R a m p hp (2^b))).card:ℝ) := by
  let f := doublePair h R a m p hp (2^b)
  let C : ℝ := 87808*(source h R Eref a m p).thickness^(-pExp)*(64/((2^b:ℕ):ℝ))^4
  have hcap (v : Parent × Index) :
      normalization D m*((T.filter (fun z => f z=v)).card:ℝ) ≤ C := by
    let A := T.filter (fun z => f z=v)
    have H := (actual_relative_raw_capacities h original R level HB Eref m b hm hmb p v.1 hbudget).2.2
    apply H A ((filter_subset _ _).trans hT) ?_
      (fun z => originalRepresentative h R a m p hp (2^b)
        (relativeLabel D a (2^m) p (2^b) z.1)) (v.2 3)
    · intro z hz
      apply mem_filter.mpr
      exact ⟨hparent z (mem_filter.mp hz).1,congrArg Prod.fst (mem_filter.mp hz).2⟩
    · intro z hz
      exact congrFun (congrArg Prod.snd (mem_filter.mp hz).2) 3
  have hcard : (T.card:ℝ)=∑v∈T.image f,((T.filter (fun z => f z=v)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image f T
  rw [hcard,mul_sum]
  calc
    _ ≤ ∑_v∈T.image f,C := sum_le_sum (fun v _hv => hcap v)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

/-- The normalized original raw row fits the existing weighted selector's
U, using the actual tube-volume constant and its fixed numerical bound. -/
theorem raw_weight_upper {n : ℕ} {D : FiniteScaleSource n} {eta a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (Eref T : Finset (Fin n × Index)) (m b : ℕ) (hm : 6 ≤ m) (hmb : m+b ≤ level)
    (p : Parent) (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hT : T ⊆ incidences original) (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (q : Parent) :
    rawWeight D a m b p T q ≤ 18*fineCapacity*(source h R Eref a m p).thickness^(-pExp)*
      (64/((2^b:ℕ):ℝ))^3 := by
  have hr : 0 < (source h R Eref a m p).thickness := by
    change 0 < ((2^m:ℕ):ℝ)*D.thickness/64
    have hdelta := h.1.2.1
    positivity
  have H := (actual_relative_raw_capacities h original R level HB Eref m b hm hmb p q hbudget).2.1
  have hh := H (T.filter (fun z => relativeLabel D a (2^m) p (2^b) z.1=q))
    ((filter_subset _ _).trans hT)
    (fun z hz => mem_filter.mpr ⟨hparent z (mem_filter.mp hz).1,(mem_filter.mp hz).2⟩)
  have hcoef : rowConstant/64^3 ≤ 18*fineCapacity := by
    have hpi := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
    norm_num only [rowConstant,NativeOriginalPrunedMass.volumeConstant,fineCapacity] at ⊢
    nlinarith only [hpi]
  exact hh.trans (by
    have hx : 0 ≤ (source h R Eref a m p).thickness^(-pExp)*(64/((2^b:ℕ):ℝ))^3 := by positivity
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hx)

/-- Universal genuine Q-row shading lower for the unchanged original raw
weights. The stronger denominator16*87808 is retained explicitly. -/
theorem same_Q_shading_bridge {n : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (Eref T : Finset (Fin n × Index)) (m b : ℕ) (hm : 6 ≤ m) (hmb : m+b ≤ level)
    (p : Parent) (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hT : T ⊆ incidences original) (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (Q : Finset Parent) :
    (source h R Eref a m p).thickness^pExp*(∑q∈Q,rawWeight D a m b p T q)/(16*87808) ≤
      ∑q∈Q,NativeCoarseShadingPruning.weight (source h R Eref a m p) 0 (level-m+6) b
        (NativeCoarseDirectionThinning.representative hS univ 0 (2^b))
        (incidences (sourceCells D R T a (2^m) p)) q := by
  let hp : (parentLabels D R a (2^m) p).Nonempty := card_pos.mp hS.1.1
  let TQ := NativeSameQSourceRestriction.restrict D a m b p Q T
  have hsub : TQ ⊆ T := filter_subset _ _
  have hc := raw_shadow_card_bound h original R level HB Eref TQ m b hm hmb p hp hbudget
    (hsub.trans hT) (fun z hz => hparent z (hsub hz))
  rw [sum_raw_weight,NativeSameQShadowMass.sum_shadow_weight_eq_pairs h R Eref T a level m b p hS
    hparent hp HB.2.1 (by omega) (by omega) Q]
  let r := (source h R Eref a m p).thickness
  let d : ℝ := 64/((2^b:ℕ):ℝ)
  have hr : 0 < r := hS.1.2.1
  calc
    _ = (r^pExp/(16*87808))*(normalization D m*(TQ.card:ℝ)) := by ring
    _ ≤ (r^pExp/(16*87808))*(87808*r^(-pExp)*d^4*
        ((TQ.image (doublePair h R a m p hp (2^b))).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      dsimp only [d]
      rw [Real.rpow_neg hr.le]
      field_simp [(Real.rpow_pos_of_pos hr pExp).ne']
      ring

/-- The universal row lower is the actual source's total shading on any
specified separated Q. Q is not selected again in this readback. -/
theorem same_Q_source_shading {n : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta pExp : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (Eref T : Finset (Fin n × Index)) (m b : ℕ) (hm : 6 ≤ m) (hmb : m+b ≤ level)
    (p : Parent) (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^pExp ≤ D.thickness^zeta)
    (hT : T ⊆ incidences original) (hparent : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (Q : Finset Parent)
    (hsep : ∀q∈Q,∀q'∈Q,q≠q' → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((source h R Eref a m p).line
        (NativeCoarseDirectionThinning.representative hS univ 0 (2^b) q)))
      (direction ((source h R Eref a m p).line
        (NativeCoarseDirectionThinning.representative hS univ 0 (2^b) q')))) :
    (source h R Eref a m p).thickness^pExp*(∑q∈Q,rawWeight D a m b p T q)/(16*87808) ≤
      (wzTotalShadingVolume (NativeCoarseCellSource.source hS 0 (level-m+6) b Q
        (NativeCoarseDirectionThinning.representative hS univ 0 (2^b))
        (incidences (sourceCells D R T a (2^m) p)) hsep)).toReal := by
  rw [NativeCoarseSourceMass.source_total_shading_real]
  exact same_Q_shading_bridge h original R level HB Eref T m b hm hmb p hS hbudget hT hparent Q

/-- Select one actual Q with ORIGINAL raw weights, then admit its actual
coarse shadow source. The original-row retention and terminal populations
are returned on that same Q; sourceCells(T) is only its shading data. -/
theorem exists_same_Q_source {n : ℕ} {D : FiniteScaleSource n} {eta etaS a zeta pExp z e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (Eref T : Finset (Fin n × Index)) (hEref : Eref ⊆ incidences original) (hTE : T ⊆ Eref)
    (m b : ℕ) (hm : 6 ≤ m) (hb : 6 ≤ b) (hmb : m+b ≤ level) (p : Parent)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hparent : ∀v∈T,v.1∈parentLabels D R a (2^m) p)
    (hpExp : 0 ≤ pExp) (hpz : pExp ≤ z) :
    let Sref := source h R Eref a m p
    let r := Sref.thickness
    let d : ℝ := 64/((2^b:ℕ):ℝ)
    let rep := NativeCoarseDirectionThinning.representative hS univ 0 (2^b)
    r^z ≤ normalization D m*(T.card:ℝ) →
    (64:ℝ)^3*r^pExp ≤ D.thickness^zeta →
    colorCost*r^z ≤ 1 → 2*pruneCost*((b:ℝ)+1)*r^(3*z) ≤ 1 →
    1088*fineCapacity*r^z ≤ 1 → d^e ≤ r^(8*z) →
    10077696*r^(8*z) ≤ 1 → densityCost*r^z ≤ 1 → cwCost*r^(2*z-etaS) ≤ 1 →
    ∃(Q : Finset Parent)
      (hsep : ∀q∈Q,∀q'∈Q,q≠q' → d ≤ dist (direction (Sref.line (rep q))) (direction (Sref.line (rep q')))),
      Q ⊆ (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image (parentLabel Sref 0 (2^b)) ∧
      Q.Nonempty ∧ (∀q∈Q,parentLabel Sref 0 (2^b) (rep q)=q) ∧
      (∀ell : Fin (b+1),∀q : Parent,(Q.filter (fun q' => ancestor b ell.val q'=q)).Nonempty →
        r^(8*z)*(((2^b:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
          ((Q.filter (fun q' => ancestor b ell.val q'=q)).card:ℝ)) ∧
      let TQ := NativeSameQSourceRestriction.restrict D a m b p Q T
      let C := NativeCoarseCellSource.source hS 0 (level-m+6) b Q rep
        (incidences (sourceCells D R T a (2^m) p)) hsep
      IsWangZakharovNativeFiniteInput C e ∧ C.thickness=d ∧ (∀i,C.line i∈fixedCompactClass) ∧
      r^(5*z) ≤ (wzTotalShadingVolume C).toReal ∧
      r^pExp/(2*colorCost)*(normalization D m*(T.card:ℝ)) ≤ normalization D m*(TQ.card:ℝ) ∧
      r^(3*z)/2 ≤ normalization D m*(TQ.card:ℝ) ∧
      r^pExp*(normalization D m*(TQ.card:ℝ))/(16*87808) ≤ (wzTotalShadingVolume C).toReal := by
  intro Sref r d rep htotal hprofile hcolor hprune hshadeCost hpower hupper hdensity hcw
  have hT : T ⊆ incidences original := hTE.trans hEref
  have hr : 0 < r := hS.1.2.1
  have hmlevel : m ≤ level := by omega
  have hblevel : b ≤ level-m+6 := by omega
  have H := NativeSameReferenceChartBounds.population_through h original R level HB Eref m b hmb p hprofile
  have hscale : ((2^b:ℕ):ℝ)*Sref.thickness ≤ 1 :=
    NativeSameReferenceChartBounds.source_scale_guard (a:=a) h R Eref level m b p HB.2.1 hmb
  let W := rawWeight D a m b p T
  have hNu : 0 < normalization D m := by unfold normalization; have hdelta := h.1.2.1; positivity
  have hW : ∀q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel Sref 0 (2^b)),0 ≤ W q := by
    intro q _hq
    exact mul_nonneg hNu.le (Nat.cast_nonneg _)
  have hU := raw_weight_upper h original R level HB Eref T m b hm hmb p hprofile hT hparent
  have hWtotal := total_raw_weight h R Eref T m b p hparent
  have htotalW : r^z ≤ (1:ℝ)^4*(∑q∈(univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel Sref 0 (2^b)),W q) := by
    simpa only [one_pow,one_mul,hWtotal] using htotal
  obtain ⟨Q,hQP,hQne,hrep,hsep,hret,hnorm,_hbare,hterminal⟩ :=
    NativeFineWeightedCoarseCore.same_Q_selection hS hpExp hpz (by norm_num : (0:ℝ) < 1) univ b hscale
      (fun ell q hq => (H ell q hq).1) W hW
      (fun q _hq => by simpa only [one_pow,div_one] using hU q) htotalW hcolor hprune
  have hbridge := same_Q_shading_bridge h original R level HB Eref T m b hm hmb p hS hprofile hT hparent Q
  have hDen : (16*87808:ℝ) ≤ 544*fineCapacity := by norm_num [fineCapacity]
  have hsum : 0 ≤ ∑q∈Q,W q := sum_nonneg (fun q hq => hW q (hQP hq))
  have hweak : r^pExp*(1:ℝ)^4*(∑q∈Q,W q)/(544*fineCapacity) ≤
      ∑q∈Q,NativeCoarseShadingPruning.weight Sref 0 (level-m+6) b rep
        (incidences (sourceCells D R T a (2^m) p)) q := by
    simp only [one_pow,mul_one]
    exact (div_le_div_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hr.le _) hsum)
      (by norm_num) hDen).trans hbridge
  have hshade := NativeFineWeightedCoarseCore.actual_shading_from_fine_weights hr hS.1.2.2.1 hpz
    hnorm hweak hshadeCost
  let originalRef := sourceCells D R Eref a (2^m) p
  let I := incidences (sourceCells D R T a (2^m) p)
  have hI : ∀v∈I,v.2∈originalRef v.1 := by
    intro v hv
    exact (mem_incidences originalRef v.1 v.2).mp
      (NativeCurrentReferenceIncidenceSubset.source_incidences_mono D R T Eref hTE a (2^m) p hv)
  have hRefDyadic : Sref.thickness=(2:ℝ)⁻¹^(level-m+6) :=
    NativeRelativeCoarseReadback.local_source_dyadic h R Eref a level m p HB.2.1 hmlevel
  have hRefCube : ∀i,Sref.shading i=wzCellShading (mesh Sref) originalRef i :=
    NativeActualRelativeCoarseAdmission.source_common_mesh h R Eref a m p
  have hRefCommon : ∀i,wzGraphTime (Sref.line i) 0-mark (Sref.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ) :=
    NativeActualRelativeCoarseAdmission.source_common_height_zero h R Eref a m p hS
  have hRefCompact : ∀i,Sref.line i∈fixedCompactClass := by
    intro i
    have hi := (mem_parentLabels D R a (2^m) p _).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels D R a (2^m) p) i)
    exact NativeLocalParentGeometry.mem_fixedCompactClass D a (2^m) p _ hi.2
  have Hcoarse : ∀q : Parent,
      ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
        (fun i => parentLabel Sref 0 (2^b) i=q)).Nonempty →
      r^z*((1/((2^b:ℕ):ℝ))/r)^3 ≤
        (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).filter
          (fun i => parentLabel Sref 0 (2^b) i=q)).card:ℝ) := by
    intro q hq
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hr hS.1.2.2.1 hpz)
      (show 0 ≤ ((1/((2^b:ℕ):ℝ))/r)^3 by positivity)).trans (H ⟨b,by omega⟩ q hq).1
  have hnative := NativeCoarseNativeAdmissibility.native_input hS hRefCompact (hpExp.trans hpz)
    originalRef hRefCube hRefCommon univ (level-m+6) b hRefDyadic hblevel hb hscale Q hQP hQne rep
    (fun q hq => (hrep q hq).2) I hI hsep Hcoarse hterminal hshade hpower hupper hdensity
    (by simpa only [show 8*z-(etaS+6*z)=2*z-etaS by ring] using hcw)
  have hWQ := sum_raw_weight D a m b p T Q
  dsimp only [W] at hret hnorm
  rw [hWtotal,hWQ] at hret
  simp only [one_pow,one_mul,hWQ] at hnorm
  refine ⟨Q,hsep,hQP,hQne,fun q hq => (hrep q hq).2,hterminal,hnative,rfl,?_,?_,hret,hnorm,?_⟩
  · intro i
    exact NativeCoarseRepresentativeGeometry.zero_parent_mem_fixedCompactClass hS hRefCompact hRefCommon
      (rep (NativeCoarseCellSource.parentIndex Q i))
  · rw [NativeCoarseSourceMass.source_total_shading_real]
    exact hshade
  · rw [NativeCoarseSourceMass.source_total_shading_real,←hWQ]
    exact hbridge

end NativeActualRawWeightSource
