import Theorems.Thm_StickyKakeya4_native_normalized_cell_source_upper
import Theorems.Thm_StickyKakeya4_native_normalized_cell_angular_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000

noncomputable section
namespace NativeBoundedReferenceRelativeUpper
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeMiddleWindowBalance
open NativeActualRelativeCoarseAdmission NativeRelativeCoarseReadback NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeJointLocalCoarseUpper NativeNormalizedCellAngularMenu
open NativeUnitParentNormalization
open scoped ENNReal

/-- The relative native exponent is explicitly CLAMPED after the rank
cutoff is fixed. It is then chosen before tau, seed, and the original source.
Every later incidence subset inherits the angular union by literal inclusion. -/
theorem exists_bounded_reference_engine (epsilon window budget : ℝ)
    (hepsilon : 0 < epsilon) (hwindow : 0 < window) (hbudgetPos : 0 < budget) :
    ∃e localEtaMax sigma0 : ℝ,0 < e ∧ e ≤ 32*budget/(7*window) ∧
      0 < localEtaMax ∧ 0 < sigma0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),0 ≤ zeta →
      ∀(original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta →
      ∀(m : ℕ),m ≤ level → ∀(p : Parent) (E : Finset (Fin n × Index)),
        E⊆incidences original → (∀z∈E,z.1∈parentLabels D R a (2^m) p) →
      ∀hp : (parentLabels D R a (2^m) p).Nonempty,
      ∀localEta : ℝ,∀_hS : IsWangZakharovNativeFiniteInput (source h R E a m p) localEta,
        (∀i,(source h R E a m p).line i∈fixedCompactClass) → localEta ≤ localEtaMax →
        (source h R E a m p).thickness ≤ sigma0 →
        (64:ℝ)^3*(source h R E a m p).thickness^(window*e/32) ≤ D.thickness^zeta →
      ∀s : ℕ,s ≤ level-m+6 →
        1/((2^s:ℕ):ℝ) ≤ (source h R E a m p).thickness^window →
        (source h R E a m p).thickness/(1/((2^s:ℕ):ℝ)) ≤ (source h R E a m p).thickness^window →
      ∀Q : ℕ,HasUniformFibers E Q (doublePair h R a m p hp (2^s)) →
        HasUniformFibers E Q (fun z => (doublePair h R a m p hp (2^s) z).2) →
      ∀T⊆E,∀q : Index,((angularMenu D a m (2^s) p T q).card:ℝ) ≤
        81*(Q:ℝ)^4*(source h R E a m p).thickness^(-budget)*
          (64/((2^s:ℕ):ℝ))^(-extremalExponent-epsilon) := by
  obtain ⟨eUpper,heUpper,dUpper,hdUpper,hUpper⟩ := NativeFixedCompactMultiplicity.fixed_compact_multiplicity_upper hepsilon
  let e := min eUpper (32*budget/(7*window))
  have he : 0 < e := lt_min heUpper (by positivity)
  have heU : e ≤ eUpper := min_le_left _ _
  have heB : e ≤ 32*budget/(7*window) := min_le_right _ _
  obtain ⟨ds,hds,Hs⟩ := actual_local_relative_coarse_admission he hwindow
  obtain ⟨dc,hdc,_hdc1,Hc⟩ := exists_positive_rpow_absorption_threshold hwindow
    (show 0 ≤ 64/dUpper by positivity) (show (0:ℝ)<1 by norm_num)
  refine ⟨e,window*e/512,min ds dc,he,heB,by positivity,lt_min hds hdc,?_⟩
  intro n D eta zeta a h hzeta original R level HB m hm p E hE hlabels hp localEta hS hSK
    hlocal hsmall hprofile s hs hcoarse hfine Q hPair hPoint T hTE q
  let S := source h R E a m p
  let theta : ℝ := 64/((2^s:ℕ):ℝ)
  let loss := 7*(window*e/32)
  have hSigma : 0 < S.thickness := hS.1.2.1
  have hSigma1 : S.thickness ≤ 1 := hS.1.2.2.1
  have hTheta : 0 < theta := by dsimp [theta]; positivity
  obtain ⟨C,hsep,_hCsub,_hCne,hNative,hCompact,hthick,hTransfer,_hshade⟩ :=
    Hs n D eta h R E a zeta hzeta level HB.2.1 HB.2.2.2.2.2.2.2.2 m hm p localEta hS hSK
      (hsmall.trans (min_le_left _ _)) hlocal hprofile s hcoarse hfine
  have hSmallCoarse : theta ≤ dUpper := by
    have hh := Hc S.thickness hSigma (hsmall.trans (min_le_right _ _))
    have hscalar : 64*S.thickness^window ≤ dUpper := by
      have hmul := (mul_le_mul_iff_right₀ hdUpper).mpr hh
      field_simp at hmul
      nlinarith only [hmul]
    exact (show theta ≤ 64*S.thickness^window by
      dsimp [theta]
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hcoarse (by norm_num : (0:ℝ)≤64)).trans hscalar
  have hCoarseUpper := hUpper C.card _ (by rw [hthick]; exact hSmallCoarse)
    (NativeFiniteKakeyaCounts.input_mono hNative heU) hCompact
  have hCross := hTransfer.trans hCoarseUpper
  have hMu := remove_small_power hSigma hSigma1 (le_refl loss) hCross
  have hFinite : (ENNReal.ofReal S.thickness).rpow (-loss)*
      (ENNReal.ofReal theta).rpow (-extremalExponent-epsilon)≠⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hSigma) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hTheta) ENNReal.ofReal_ne_top)
  have hReal : (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) s
        (incidences (sourceCells D R E a (2^m) p)))).toReal ≤
      S.thickness^(-loss)*theta^(-extremalExponent-epsilon) := by
    have hh := ENNReal.toReal_mono hFinite hMu
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hSigma.le,ENNReal.toReal_ofReal hTheta.le,hthick] using hh
  rw [relative_full_multiplicity_readback h R E a level m s p hp hlabels hS HB.2.1 hm hs] at hReal
  have hLoss : loss ≤ budget := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<7*window)).mp heB
    dsimp [loss]
    nlinarith only [hh]
  have hReal' : NativeIncidenceMultiplicityTower.multiplicity (E.image (doublePair h R a m p hp (2^s))) ≤
      S.thickness^(-budget)*theta^(-extremalExponent-epsilon) := hReal.trans
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hSigma hSigma1 (neg_le_neg hLoss)) (by positivity))
  have hNscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale HB.2.1 hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^s:ℕ):ℝ) ≤ 64 := by
    have hh := hfine.trans (Real.rpow_le_one hSigma.le hSigma1 hwindow.le)
    change (((2^m:ℕ):ℝ)*D.thickness/64)/(1/((2^s:ℕ):ℝ)) ≤ 1 at hh
    have hh' := (div_le_iff₀ (by positivity : (0:ℝ)<1/((2^s:ℕ):ℝ))).mp hh
    rw [one_mul] at hh'
    have hh'' := (le_div_iff₀ (by positivity : (0:ℝ)<((2^s:ℕ):ℝ))).mp hh'
    nlinarith only [hh'']
  have hAngular := original_angular_menu_upper h original HB.1 HB.2.2.1 R m (2^s) (by positivity)
    hNscale hRelScale p hp E hE hlabels Q hPair hPoint q
  have hMono : angularMenu D a m (2^s) p T q⊆angularMenu D a m (2^s) p E q :=
    image_subset_image (filter_subset_filter _ hTE)
  exact (Nat.cast_le.mpr (card_le_card hMono)).trans (hAngular.trans (by
    calc
      _ ≤ 81*(Q:ℝ)^4*(S.thickness^(-budget)*theta^(-extremalExponent-epsilon)) := by gcongr
      _ = _ := by ring))

end NativeBoundedReferenceRelativeUpper
