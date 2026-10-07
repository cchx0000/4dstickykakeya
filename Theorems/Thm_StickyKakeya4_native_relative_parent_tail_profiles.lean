import Theorems.Thm_StickyKakeya4_native_relative_parent_profiles

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeRelativeParentTailProfiles
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeLocalParentSource
open NativeRelativeParentProfiles

/-- The exact dyadic level includes the six fixed contraction levels. -/
lemma source_thickness_dyadic {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a : ℝ)
    (level m : ℕ) (hdy : D.thickness = (2:ℝ)⁻¹^level) (hm : m ≤ level) (p : Parent) :
    (source h R E a m p).thickness = (2:ℝ)⁻¹^(level-m+6) := by
  rw [source_thickness,NativeLocalParentScales.relative_scale hdy hm,pow_add]
  norm_num [div_eq_mul_inv]

/-- Below the old product-scale endpoint the new radius ratio is at most64.
This fact uses the exact original dyadic scale, not a new regularization. -/
lemma tail_radius_ratio_le {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index)) (a : ℝ)
    (level m ell : ℕ) (hdy : D.thickness = (2:ℝ)⁻¹^level)
    (hm : m ≤ level) (htail : level-m ≤ ell) (p : Parent) :
    (1/((2^ell:ℕ):ℝ))/(source h R E a m p).thickness ≤ 64 := by
  have hd := h.1.2.1
  have heps : 0 < (source h R E a m p).thickness := by rw [source_thickness]; positivity
  apply (div_le_iff₀ heps).mpr
  rw [source_thickness]
  have hr : (1/((2^ell:ℕ):ℝ)) ≤ ((2^m:ℕ):ℝ)*D.thickness := by
    rw [NativeLocalParentScales.relative_scale hdy hm]
    simpa only [one_div,Nat.cast_pow,Nat.cast_ofNat,inv_pow] using
      (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)
        (by norm_num : (2:ℝ)⁻¹ ≤ 1) htail)
  linarith

/-- The final six relative levels have lower population from occupancy;
the upper bound at every local level is geometric direction packing.
The native local hypothesis is supplied by actual admission; only its
validity, north chart and separation fields are used for the upper bound. -/
theorem source_all_dyadic_population {n : ℕ} {D : FiniteScaleSource n}
    {eta localExponent : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (E : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (a zeta : ℝ) (hzeta : 0 ≤ zeta) (level : ℕ)
    (hdy : D.thickness = (2:ℝ)⁻¹^level)
    (H : ∀ k : Fin (level+1), ∀ z : Parent,
      (R.filter (fun i => parentLabel D a (2^k.val) i = z)).Nonempty →
        D.thickness^zeta*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ≤
          D.thickness^(-zeta)*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3)
    (m : ℕ) (hm : m ≤ level) (p : Parent)
    (hlocal : IsWangZakharovNativeFiniteInput (source h R E a m p) localExponent)
    (ell : ℕ) (hell : ell ≤ level-m+6) (q : Parent)
    (hq : (backbone (source h R E a m p) 0 (2^ell) q).Nonempty) :
    let S := source h R E a m p
    D.thickness^zeta/(64:ℝ)^3*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 ≤
      ((backbone S 0 (2^ell) q).card : ℝ) ∧
    ((backbone S 0 (2^ell) q).card : ℝ) ≤
      (18:ℝ)^3*D.thickness^(-zeta)*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 := by
  let S := source h R E a m p
  have hd := h.1.2.1
  have heps : 0 < S.thickness := hlocal.1.2.1
  have hdz : D.thickness^zeta ≤ 1 := Real.rpow_le_one hd.le h.1.2.2.1 hzeta
  have hdz' : 1 ≤ D.thickness^(-zeta) := by
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd zeta)).mpr (by simpa using hdz)
  constructor
  · by_cases hwithin : m+ell ≤ level
    · exact (source_dyadic_population h R E a zeta level H m ell hwithin p q hq).1
    · have hr := tail_radius_ratio_le h R E a level m ell hdy hm (by omega) p
      have hpow : ((1/((2^ell:ℕ):ℝ))/S.thickness)^3 ≤ (64:ℝ)^3 :=
        pow_le_pow_left₀ (by positivity) hr 3
      have hl : D.thickness^zeta/(64:ℝ)^3*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 ≤ 1 := by
        calc
          _ ≤ D.thickness^zeta/(64:ℝ)^3*(64:ℝ)^3 :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = D.thickness^zeta := by ring
          _ ≤ 1 := hdz
      have hcard : (1:ℝ) ≤ (backbone S 0 (2^ell) q).card := by
        exact_mod_cast card_pos.mpr hq
      exact hl.trans hcard
  · have hscale : ((2^ell:ℕ):ℝ)*S.thickness ≤ 1 := by
      rw [NativeLocalParentScales.relative_scale
        (source_thickness_dyadic h R E a level m hdy hm p) hell]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hu := NativeOriginalSlopeCubePacking.native_backbone_card_le hlocal 0
      (2^ell) (by positivity) hscale q
    have he : (1 / (((2^ell:ℕ):ℝ)*S.thickness)) =
        (1/((2^ell:ℕ):ℝ))/S.thickness := by ring
    rw [he] at hu
    calc
      _ ≤ (18:ℝ)^3*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 := by norm_num at hu ⊢; exact hu
      _ = (18:ℝ)^3*1*((1/((2^ell:ℕ):ℝ))/S.thickness)^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdz' (by positivity)) (by positivity)

/-- This single explicit budget yields native population powers at EVERY
local dyadic level, including all six extra contraction levels. -/
theorem source_all_dyadic_population_power {n : ℕ} {D : FiniteScaleSource n}
    {eta localExponent e : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (E : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (a zeta : ℝ) (hzeta : 0 ≤ zeta) (level : ℕ)
    (hdy : D.thickness = (2:ℝ)⁻¹^level)
    (H : ∀ k : Fin (level+1), ∀ z : Parent,
      (R.filter (fun i => parentLabel D a (2^k.val) i = z)).Nonempty →
        D.thickness^zeta*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^k.val) i = z)).card : ℝ) ≤
          D.thickness^(-zeta)*((1/((2^k.val:ℕ):ℝ))/D.thickness)^3)
    (m : ℕ) (hm : m ≤ level) (p : Parent)
    (hlocal : IsWangZakharovNativeFiniteInput (source h R E a m p) localExponent)
    (hbudget : (64:ℝ)^3*(source h R E a m p).thickness^e ≤ D.thickness^zeta)
    (ell : Fin (level-m+6+1)) (q : Parent)
    (hq : (backbone (source h R E a m p) 0 (2^ell.val) q).Nonempty) :
    let S := source h R E a m p
    S.thickness^e*((1/((2^ell.val:ℕ):ℝ))/S.thickness)^3 ≤
      ((backbone S 0 (2^ell.val) q).card : ℝ) ∧
    ((backbone S 0 (2^ell.val) q).card : ℝ) ≤
      S.thickness^(-e)*((1/((2^ell.val:ℕ):ℝ))/S.thickness)^3 := by
  let S := source h R E a m p
  have heps : 0 < S.thickness := hlocal.1.2.1
  obtain ⟨hl,hu⟩ := source_all_dyadic_population h R E a zeta hzeta level hdy H m hm p
    hlocal ell.val (Nat.le_of_lt_succ ell.isLt) q hq
  have hlo : S.thickness^e ≤ D.thickness^zeta/(64:ℝ)^3 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < (64:ℝ)^3)).mpr
    simpa only [mul_comm] using hbudget
  have hb18 : (18:ℝ)^3*S.thickness^e ≤ D.thickness^zeta := by
    exact (mul_le_mul_of_nonneg_right (by norm_num : (18:ℝ)^3 ≤ (64:ℝ)^3)
      (Real.rpow_pos_of_pos heps e).le).trans hbudget
  have hup := NativeActualLocalAdmission.negative_coefficient h.1.2.1 heps hb18
  exact ⟨(mul_le_mul_of_nonneg_right hlo (by positivity)).trans hl,
    hu.trans (mul_le_mul_of_nonneg_right hup (by positivity))⟩

end NativeRelativeParentTailProfiles
