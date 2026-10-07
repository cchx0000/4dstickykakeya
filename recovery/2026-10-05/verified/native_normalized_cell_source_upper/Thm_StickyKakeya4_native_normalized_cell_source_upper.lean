import Theorems.Thm_StickyKakeya4_native_normalized_cell_relative_core
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_actual_local_admission
import Theorems.Thm_StickyKakeya4_native_joint_local_coarse_upper
import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8500000

noncomputable section
namespace NativeNormalizedCellSourceUpper
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeMiddleWindowBalance NativeActualLocalAdmission NativeActualRelativeCoarseAdmission
open NativeNormalizedCellRelativeCore NativeRelativeCoarseReadback NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeJointLocalCoarseUpper
open NativeUnitParentNormalization
open scoped ENNReal

/-- Admit the CURRENT retained parent source from its actual original-edge
population. Only scalar absorption budgets remain; no new source is chosen. -/
theorem source_native_from_population {n : ℕ} {D : FiniteScaleSource n} {eta zeta a localEta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m : ℕ) (hm : m ≤ level) (p : Parent) (E : Finset (Fin n × Index))
    (hE : E⊆incidences original) (hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p)
    (hp : (parentLabels D R a (2^m) p).Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hpop : population*(parentLabels D R a (2^m) p).card ≤ D.thickness*E.card)
    (had : (2048:ℝ)^3*(source h R E a m p).thickness^localEta ≤ D.thickness^zeta)
    (hcw : (373248*512^4:ℝ)*(source h R E a m p).thickness^localEta ≤ D.thickness^(eta+zeta))
    (hden : (1024*175616*NativeOriginalPrunedMass.volumeConstant)*
      (source h R E a m p).thickness^localEta ≤ population) :
    IsWangZakharovNativeFiniteInput (source h R E a m p) localEta ∧
      (∀i,(source h R E a m p).line i∈fixedCompactClass) := by
  let F := D.thickness^(eta+2*zeta)/population
  have hd := h.1.2.1
  have hF : 0<F := by dsimp [F]; positivity
  have hFp : F*population=D.thickness^(eta+2*zeta) := by dsimp [F]; field_simp
  have hParent : D.thickness^(eta+2*zeta)*(parentLabels D R a (2^m) p).card ≤
      D.thickness*F*(1:ℝ)^2*E.card := by
    have hh := mul_le_mul_of_nonneg_left hpop hF.le
    rw [←mul_assoc,hFp] at hh
    simpa only [one_pow,mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  have hDensity : (1024*175616*NativeOriginalPrunedMass.volumeConstant)*F*(1:ℝ)^2*
      (source h R E a m p).thickness^localEta ≤ D.thickness^(eta+2*zeta) := by
    have hh := mul_le_mul_of_nonneg_left hden hF.le
    rw [hFp] at hh
    simpa only [one_pow,mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  exact native_input h hzeta original Hbackbone.1 Hbackbone.2.2.1 R E hE level m
    Hbackbone.2.1 hm p hlabels hp (fun j q hq => (Hbackbone.2.2.2.2.2.2.2.2 j q hq).1)
    F 1 hF (by norm_num) hParent had hcw hDensity

/-- The relative extremal allowances precede the original source. On that
SAME source, actual population admits the local family, exact doublePair
readback gives its average upper, and the proved physical menu gives every
normalized-cell degree. No common angular-menu or output-profile premise. -/
theorem exists_source_normalized_degree_upper {epsilon window : ℝ}
    (hepsilon : 0 < epsilon) (hwindow : 0 < window) :
    ∃ e eta0 eps0 : ℝ,0<e ∧ 0<eta0 ∧ 0<eps0 ∧
      ∀ localEta : ℝ,0<localEta → localEta≤eta0 →
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta zeta a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),0≤zeta →
      ∀ (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta →
      ∀ m : ℕ,m≤level → ∀ (p : Parent) (E : Finset (Fin n × Index)),
        E⊆incidences original → (∀z∈E,z.1∈parentLabels D R a (2^m) p) →
      ∀ hp : (parentLabels D R a (2^m) p).Nonempty,
      ∀ population : ℝ,0<population →
        population*(parentLabels D R a (2^m) p).card ≤ D.thickness*E.card →
        (2048:ℝ)^3*(source h R E a m p).thickness^localEta ≤ D.thickness^zeta →
        (373248*512^4:ℝ)*(source h R E a m p).thickness^localEta ≤ D.thickness^(eta+zeta) →
        (1024*175616*NativeOriginalPrunedMass.volumeConstant)*
          (source h R E a m p).thickness^localEta ≤ population →
        (source h R E a m p).thickness ≤ eps0 →
        (64:ℝ)^3*(source h R E a m p).thickness^(window*e/32) ≤ D.thickness^zeta →
      ∀ ell : ℕ,ell≤level-m+6 →
        1/((2^ell:ℕ):ℝ) ≤ (source h R E a m p).thickness^window →
        (source h R E a m p).thickness/(1/((2^ell:ℕ):ℝ)) ≤ (source h R E a m p).thickness^window →
      ∀ Q : ℕ,HasUniformFibers E Q (doublePair h R a m p hp (2^ell)) →
        HasUniformFibers E Q (fun z => (doublePair h R a m p hp (2^ell) z).2) →
      ∀ q : Index,
        (((E.image (normalizedPair D a m (2^ell) p)).filter (fun z => z.2=q)).card:ℝ) ≤
          81*(Q:ℝ)^4*(source h R E a m p).thickness^(-(7*(window*e/32)))*
            (64/((2^ell:ℕ):ℝ))^(-extremalExponent-epsilon) := by
  obtain ⟨e,eta0,eps0,he,heta0,heps0,hUpper⟩ := actual_local_relative_full_coarse_upper hepsilon hwindow
  refine ⟨e,eta0,eps0,he,heta0,heps0,?_⟩
  intro localEta _hlocalEta heta n D eta zeta a h hzeta original R level Hbackbone m hm p E hE hlabels hp
    population hpopulation hpop had hcw hden hsmall hbudget ell hell hcoarse hfine Q hPair hPoint q
  obtain ⟨hS,hSK⟩ := source_native_from_population h hzeta original R level Hbackbone m hm p E hE
    hlabels hp population hpopulation hpop had hcw hden
  let S := source h R E a m p
  let theta : ℝ := 64/((2^ell:ℕ):ℝ)
  let loss : ℝ := 7*(window*e/32)
  have heps : 0<S.thickness := hS.1.2.1
  have heps1 : S.thickness≤1 := hS.1.2.2.1
  have htheta : 0<theta := by dsimp [theta]; positivity
  have hBound := hUpper n D eta h R E a zeta hzeta level Hbackbone.2.1 Hbackbone.2.2.2.2.2.2.2.2
    m hm p localEta hS hSK hsmall heta hbudget ell hcoarse hfine
  have hMu := remove_small_power heps heps1 (le_refl loss) hBound
  have hFinite : (ENNReal.ofReal S.thickness).rpow (-loss)*
      (ENNReal.ofReal theta).rpow (-extremalExponent-epsilon)≠⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr heps) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr htheta) ENNReal.ofReal_ne_top)
  have hReal : (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource hS univ 0 (level-m+6) ell
        (incidences (sourceCells D R E a (2^m) p)))).toReal ≤
      S.thickness^(-loss)*theta^(-extremalExponent-epsilon) := by
    have hh := ENNReal.toReal_mono hFinite hMu
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal heps.le,ENNReal.toReal_ofReal htheta.le] using hh
  rw [relative_full_multiplicity_readback h R E a level m ell p hp hlabels hS Hbackbone.2.1 hm hell] at hReal
  have hNscale : ((2^m:ℕ):ℝ)*D.thickness≤1 := by
    rw [NativeLocalParentScales.relative_scale Hbackbone.2.1 hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hPower : S.thickness^window≤1 := Real.rpow_le_one heps.le heps1 hwindow.le
  have hRelScale : ((2^m:ℕ):ℝ)*D.thickness*((2^ell:ℕ):ℝ)≤64 := by
    have hh := hfine.trans hPower
    change (((2^m:ℕ):ℝ)*D.thickness/64)/(1/((2^ell:ℕ):ℝ))≤1 at hh
    have hh' := (div_le_iff₀ (by positivity : (0:ℝ)<1/((2^ell:ℕ):ℝ))).mp hh
    rw [one_mul] at hh'
    have hh'' := (le_div_iff₀ (by positivity : (0:ℝ)<((2^ell:ℕ):ℝ))).mp hh'
    nlinarith only [hh'']
  have hDegree := normalized_cell_degree_upper h original Hbackbone.1 Hbackbone.2.2.1
    R m (2^ell) (by positivity) hNscale hRelScale p hp E hE hlabels Q hPair hPoint q
  calc
    _ ≤ 81*(Q:ℝ)^4*NativeIncidenceMultiplicityTower.multiplicity
        (E.image (doublePair h R a m p hp (2^ell))) := hDegree
    _ ≤ 81*(Q:ℝ)^4*(S.thickness^(-loss)*theta^(-extremalExponent-epsilon)) :=
      mul_le_mul_of_nonneg_left hReal (by positivity)
    _ = _ := by ring

end NativeNormalizedCellSourceUpper
