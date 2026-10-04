import Theorems.Thm_StickyKakeya4_native_padded_source_ad_upper
import Theorems.Thm_StickyKakeya4_native_padded_source_ad_lower
import Theorems.Thm_StickyKakeya4_native_padded_source_count_budget
import Theorems.Thm_StickyKakeya4_native_padded_source_density
import Theorems.Thm_StickyKakeya4_native_padded_source_power_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativePaddedSourceAdmissibility
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativePaddedCellSource NativePaddedSourceADLower NativePaddedSourceADUpper NativePaddedSourceTransport
open NativePaddedSourceDensity NativePaddedSourcePowerBudget NativeDenseRetainedUnitParent NativeOriginalPrunedMass
open scoped ENNReal

lemma real_AD_to_enn {d r e : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (m : ℕ)
    (hl : d^e*(r/d)^3 ≤ (m:ℝ)) (hu : (m:ℝ) ≤ d^(-e)*(r/d)^3) :
    (ENNReal.ofReal d).rpow e*(ENNReal.ofReal (r/d))^3 ≤ (m:ℝ≥0∞) ∧
      (m:ℝ≥0∞) ≤ (ENNReal.ofReal d).rpow (-e)*(ENNReal.ofReal (r/d))^3 := by
  constructor
  · simpa only [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd e).le,
      ENNReal.ofReal_rpow_of_pos hd,ENNReal.rpow_eq_pow,
      ENNReal.ofReal_pow (div_nonneg hr hd.le),ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hl
  · simpa only [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd (-e)).le,
      ENNReal.ofReal_rpow_of_pos hd,ENNReal.rpow_eq_pow,
      ENNReal.ofReal_pow (div_nonneg hr hd.le),ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hu

/-- Both new carrier AD inequalities follow from actual separation and
the already proved same-original-label ancestor estimates. -/
theorem source_AD {n : ℕ} {D : FiniteScaleSource n} {eta zeta e a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta) (he : 0 ≤ e)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (p : Parent)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (H : ∀ell : Fin (level+1),∀q : Parent,
      (R.filter (fun j => parentLabel D a (2^ell.val) j=q)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun j => parentLabel D a (2^ell.val) j=q)).card:ℝ))
    (hloss : (2048:ℝ)^3*D.thickness^(e-zeta) ≤ 1)
    (hupper : (10077696:ℝ)*D.thickness^e ≤ 1)
    (i : Fin (parentSubset D R a p).card) {r : ℝ}
    (hr : (rootSource h original R a p).thickness ≤ r) (hr1 : r ≤ 1) :
    let S := rootSource h original R a p
    (ENNReal.ofReal S.thickness).rpow e*(ENNReal.ofReal (r/S.thickness))^3 ≤
        (wzCarrierBallCount S i r:ℝ≥0∞) ∧
      (wzCarrierBallCount S i r:ℝ≥0∞) ≤
        (ENNReal.ofReal S.thickness).rpow (-e)*(ENNReal.ofReal (r/S.thickness))^3 := by
  let S := rootSource h original R a p
  have hd := h.1.2.1
  have hdS : 0 < S.thickness := by change 0 < D.thickness/64; positivity
  have hrp := hdS.trans_le hr
  have hc := positive_power_ratio hd he (show (0:ℝ) < (2048:ℝ)^3 by positivity) hloss
  have hlo := source_carrier_lower h hzeta original R p level hdy H i hr hr1
  have hu := source_carrier_upper h original (parentSubset D R a p) p
    (fun _ hj => (mem_filter.mp hj).2) i hr
  have huc : (10077696:ℝ) ≤ S.thickness^(-e) := by
    have hp : (10077696:ℝ)*S.thickness^e ≤ 1 :=
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hdS.le (by change D.thickness/64 ≤ D.thickness; linarith) he)
        (by norm_num : (0:ℝ) ≤ 10077696)).trans hupper
    rw [Real.rpow_neg hdS.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hdS e)).mpr hp
  exact real_AD_to_enn hdS hrp.le _
    ((mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (r/S.thickness)^3)).trans hlo)
    (hu.trans (mul_le_mul_of_nonneg_right huc (by positivity)))

/-- Original CW and the actual original/selected label count imply CW for
the constructed tubes through the literal physical inverse map. -/
theorem source_CW {n : ℕ} {D : FiniteScaleSource n} {eta zeta e a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (he : 0 ≤ e)
    (original : Fin n → Finset Index)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Q : Finset (Fin n)) (p : Parent) (hp : ∀i∈Q,parentLabel D a 1 i=p)
    (hcount : (n:ℝ) ≤ 373248*D.thickness^(-zeta)*Q.card)
    (hbudget : (373248*512^4:ℝ)*D.thickness^(e-(eta+zeta)) ≤ 1)
    (U : Set E4) (hU : Convex ℝ U) :
    (wzContainedTubeCount (source h original Q a p hp) U:ℝ≥0∞) ≤
      (ENNReal.ofReal (source h original Q a p hp).thickness).rpow (-e)*volume U*Q.card := by
  have hd := h.1.2.1
  let d := ENNReal.ofReal D.thickness
  have hd0 : d ≠ 0 := by dsimp [d]; positivity
  have hdT : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : (n:ℝ≥0∞) ≤ 373248*d.rpow (-zeta)*Q.card := by
    simpa only [d,ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 373248*D.thickness^(-zeta)),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 373248),ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast,ENNReal.ofReal_rpow_of_pos hd,ENNReal.rpow_eq_pow] using
      ENNReal.ofReal_le_ofReal hcount
  have hexp : d.rpow (-eta)*d.rpow (-zeta)=d.rpow (-(eta+zeta)) := by
    simp only [ENNReal.rpow_eq_pow]
    rw [←ENNReal.rpow_add _ _ hd0 hdT]
    congr 1
    ring
  have hco := new_exponent_coefficient hd he (373248*512^4)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hbudget)
  calc
    _ ≤ (512:ℝ≥0∞)^4*d.rpow (-eta)*volume U*n := source_CW_original_count h original ha Q p hp U hU
    _ ≤ (512:ℝ≥0∞)^4*d.rpow (-eta)*volume U*(373248*d.rpow (-zeta)*Q.card) := mul_le_mul' le_rfl hc
    _ = (373248*512^4:ℝ≥0∞)*(d.rpow (-eta)*d.rpow (-zeta))*volume U*Q.card := by ring
    _ = (373248*512^4:ℝ≥0∞)*d.rpow (-(eta+zeta))*volume U*Q.card := by rw [hexp]
    _ ≤ _ := mul_le_mul' (mul_le_mul' (by
      simpa only [d,source_thickness,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hco) le_rfl) le_rfl

theorem source_density {n : ℕ} {D : FiniteScaleSource n} {eta zeta e a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (he : 0 ≤ e) (hsmall : D.thickness ≤ 1/8)
    (original : Fin n → Finset Index) (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Q : Finset (Fin n)) (p : Parent) (hp : ∀i∈Q,parentLabel D a 1 i=p)
    (hden : (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D Q ≤ 2*shadingMass D Q)
    (hbudget : (512*175616*64^4:ℝ)*D.thickness^(e-zeta) ≤ 1) :
    (ENNReal.ofReal (source h original Q a p hp).thickness).rpow e*
      wzTotalTubeVolume (source h original Q a p hp) ≤ wzTotalShadingVolume (source h original Q a p hp) := by
  have hd := h.1.2.1
  have hh := source_raw_density h hsmall original horiginal ha Q p hp hden
  have hpow := density_power hd (512*175616*64^4)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hbudget) (by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh)
  have hm : (ENNReal.ofReal (D.thickness/64)).rpow e ≤ (ENNReal.ofReal D.thickness).rpow e := by
    simpa only [ENNReal.rpow_eq_pow] using ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (by linarith : D.thickness/64 ≤ D.thickness)) he
  exact (mul_le_mul' hm le_rfl).trans hpow
end NativePaddedSourceAdmissibility
