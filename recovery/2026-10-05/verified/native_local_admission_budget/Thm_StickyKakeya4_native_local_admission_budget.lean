import Theorems.Thm_StickyKakeya4_native_original_parent_density_core
import Theorems.Thm_StickyKakeya4_native_local_parent_cw

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeLocalAdmissionBudget
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalPrunedMass NativeLocalPairUniformCore
open NativeOriginalParentSelection
open scoped ENNReal

/-- The absolute incidence constant comes from the actual tube upper volume,
the common half-thickness mesh, and original direction packing. -/
def incidenceConstant : ℝ := 16 * 373248 * volumeConstant

lemma incidenceConstant_pos : 0 < incidenceConstant := by
  dsimp [incidenceConstant]
  exact mul_pos (by norm_num) volumeConstant_pos

/-- A source-based polynomial bound for the literal original incidence set. -/
theorem original_incidence_card_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i) :
    ((incidences original).card : ℝ) ≤ incidenceConstant * D.thickness ^ (-4 : ℝ) := by
  have hd := h.1.2.1
  have hV := volumeConstant_pos
  have hmass := shadingMass_upper h (univ : Finset (Fin n))
  change wzTotalShadingVolume D ≤ _ at hmass
  rw [total_shading_eq_incidence_volume D (half_pos hd) original horiginal,
    card_univ, Fintype.card_fin] at hmass
  have hr := ENNReal.toReal_mono (by finiteness) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (half_pos hd).le,
    ENNReal.toReal_ofReal hd.le, ENNReal.toReal_ofReal volumeConstant_pos.le] at hr
  have hn := NativeLocalParentCW.original_card_upper h
  have hbound : ((incidences original).card : ℝ) * (D.thickness / 2)^4 ≤
      373248 * volumeConstant := by
    calc
      _ ≤ (n : ℝ) * (volumeConstant * D.thickness^3) := hr
      _ ≤ (373248 * (1 / D.thickness)^3) * (volumeConstant * D.thickness^3) :=
        mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by field_simp
  rw [Real.rpow_neg hd.le, Real.rpow_ofNat, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hd 4)).mpr
  change ((incidences original).card : ℝ) * D.thickness^4 ≤ incidenceConstant
  dsimp [incidenceConstant]
  nlinarith only [hbound]

/-- The radix estimate is proved from original source geometry, never assumed
as a subpower property of the eventual retained core. -/
theorem retained_radix_sq_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (A : Finset (Fin n × Index)) (hA : A ⊆ incidences original) (hAne : A.Nonempty)
    (L : ℕ) (hL : 0 < L) :
    (NativeSourceSizeBounds.radix A.card L : ℝ)^2 ≤
      16 * incidenceConstant^(2 / (L : ℝ)) * D.thickness^(-8 / (L : ℝ)) := by
  have hd := h.1.2.1
  have hC := incidenceConstant_pos
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hcard : (A.card : ℝ) ≤ incidenceConstant * D.thickness^(-4 : ℝ) :=
    (show (A.card : ℝ) ≤ (incidences original).card by exact_mod_cast card_le_card hA).trans
      (original_incidence_card_upper h original horiginal)
  have hroot := Real.rpow_le_rpow (Nat.cast_nonneg A.card) hcard
    (show 0 ≤ 1 / (L : ℝ) by positivity)
  have hQ := (NativeSourceSizeBounds.radix_le_four_root
    (L := L) (card_pos.mpr hAne)).trans (mul_le_mul_of_nonneg_left hroot (by norm_num))
  calc
    _ ≤ (4 * (incidenceConstant * D.thickness^(-4 : ℝ))^(1 / (L : ℝ)))^2 :=
      pow_le_pow_left₀ (by positivity) hQ 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
      rw [Real.mul_rpow incidenceConstant_pos.le (Real.rpow_nonneg hd.le _)]
      rw [← Real.rpow_mul hd.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (1 / (L : ℝ)) * (2 : ℝ) = 2 / (L : ℝ) by ring]
      rw [show (-4 : ℝ) * (2 / (L : ℝ)) = -8 / (L : ℝ) by ring]
      ring

/-- One absorbed positive power pays any smaller target exponent. -/
lemma pay_power {delta coefficient gap total target : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (habsorb : coefficient * delta^gap ≤ 1) (hexp : target + gap ≤ total) :
    coefficient * delta^total ≤ delta^target := by
  calc
    _ = (coefficient * delta^gap) * delta^(total - gap) := by
      rw [mul_assoc, ← Real.rpow_add hd]
      congr 2
      ring
    _ ≤ 1 * delta^(total - gap) :=
      mul_le_mul_of_nonneg_right habsorb (Real.rpow_pos_of_pos hd _).le
    _ ≤ delta^target := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)

/-- The fixed density coefficient includes the actual finite-menu retention
cost and the source-derived constant in the radix-square bound. -/
def densityCoefficient (d g L : ℕ) : ℝ :=
  (1024 * 175616 * volumeConstant) *
    (NativeOriginalParentDensityCore.factor d g L : ℝ) *
      16 * incidenceConstant^(2 / (L : ℝ))

lemma densityCoefficient_nonneg (d g L : ℕ) : 0 ≤ densityCoefficient d g L := by
  have hV := volumeConstant_pos
  have hC := incidenceConstant_pos
  dsimp [densityCoefficient]
  positivity

/-- Fix the target exponent, relative window, and finite old/menu counts first.
One choice of zeta, L, eta0, delta0 pays AD, CW, and density simultaneously
for EVERY original native source, retained original incidence set, and relative
scale in that window. The radix is computed from that actual retained set. -/
theorem exists_uniform_source_budget (e alpha : ℝ) (he : 0 < e) (halpha : 0 < alpha)
    (d g : ℕ) :
    ∃ (zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      zeta = alpha * e / 16 ∧ 0 < zeta ∧ 0 < L ∧
      256 / (alpha * e) < (L : ℝ) ∧
      0 < eta0 ∧ eta0 ≤ zeta / 16 ∧ 0 < delta0 ∧ delta0 ≤ 1 / 8 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∀ original : Fin n → Finset Index,
          (∀ i, D.shading i = wzCellShading (mesh D) original i) →
          ∀ A : Finset (Fin n × Index), A ⊆ incidences original → A.Nonempty →
            ∀ N : ℕ, 0 < N → (N : ℝ) * D.thickness ≤ D.thickness^alpha →
              let Q := NativeSourceSizeBounds.radix A.card L
              let F := NativeOriginalParentDensityCore.factor d g L
              let epsilon := (N : ℝ) * D.thickness / 64
              (2048 : ℝ)^3 * epsilon^e ≤ D.thickness^zeta ∧
              (373248 * 512^4 : ℝ) * epsilon^e ≤ D.thickness^(eta + zeta) ∧
              (1024 * 175616 * volumeConstant) * (F : ℝ) * (Q : ℝ)^2 * epsilon^e ≤
                D.thickness^(eta + 2 * zeta) := by
  let beta : ℝ := alpha * e
  have hb : 0 < beta := mul_pos halpha he
  obtain ⟨L, hlarge⟩ := exists_nat_gt (256 / beta)
  have hLp : (0 : ℝ) < L := lt_trans (by positivity) hlarge
  have hL : 0 < L := by exact_mod_cast hLp
  have hradixExponent : 8 / (L : ℝ) ≤ beta / 32 := by
    have hh := (div_lt_iff₀ hb).mp hlarge
    apply (div_le_iff₀ hLp).mpr
    nlinarith only [hh]
  obtain ⟨dAD, hdAD, _hdADone, H_AD⟩ :=
    exists_positive_rpow_absorption_threshold (gap := beta / 2)
      (coefficient := (2048 : ℝ)^3) (pointConstant := 1)
      (by positivity) (by positivity) (by norm_num)
  obtain ⟨dCW, hdCW, _hdCWone, H_CW⟩ :=
    exists_positive_rpow_absorption_threshold (gap := beta / 2)
      (coefficient := (373248 * 512^4 : ℝ)) (pointConstant := 1)
      (by positivity) (by positivity) (by norm_num)
  obtain ⟨dDen, hdDen, _hdDenone, H_Den⟩ :=
    exists_positive_rpow_absorption_threshold (gap := beta / 2)
      (coefficient := densityCoefficient d g L) (pointConstant := 1)
      (by positivity) (densityCoefficient_nonneg d g L) (by norm_num)
  let delta0 : ℝ := min (1 / 8) (min dAD (min dCW dDen))
  have hd0 : 0 < delta0 := lt_min (by norm_num) (lt_min hdAD (lt_min hdCW hdDen))
  refine ⟨beta / 16, L, beta / 256, delta0, rfl, by positivity, hL, hlarge,
    by positivity, by linarith, hd0, min_le_left _ _, ?_⟩
  intro n D eta h hsmall heta original horiginal A hA hAne N hN hwindow
  dsimp only
  have hd := h.1.2.1
  have hd1 : D.thickness ≤ 1 := by
    have hh := hsmall.trans (show delta0 ≤ 1 / 8 from min_le_left _ _)
    linarith
  have hsmallAD : D.thickness ≤ dAD :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallCW : D.thickness ≤ dCW :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallDen : D.thickness ≤ dDen :=
    hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hlocal : ((N : ℝ) * D.thickness / 64)^e ≤ D.thickness^beta := by
    have hbase : (N : ℝ) * D.thickness / 64 ≤ D.thickness^alpha := by
      have hp := Real.rpow_pos_of_pos hd alpha
      linarith
    calc
      _ ≤ (D.thickness^alpha)^e := Real.rpow_le_rpow (by positivity) hbase he.le
      _ = _ := (Real.rpow_mul hd.le alpha e).symm
  have hAD := pay_power hd hd1 (H_AD D.thickness hd hsmallAD)
    (show beta / 16 + beta / 2 ≤ beta by linarith)
  have hCW := pay_power hd hd1 (H_CW D.thickness hd hsmallCW)
    (show eta + beta / 16 + beta / 2 ≤ beta by linarith)
  have hDen := pay_power hd hd1 (H_Den D.thickness hd hsmallDen)
    (show eta + 2 * (beta / 16) + beta / 2 ≤ beta - 8 / (L : ℝ) by linarith)
  refine ⟨(mul_le_mul_of_nonneg_left hlocal (by positivity)).trans hAD,
    (mul_le_mul_of_nonneg_left hlocal (by positivity)).trans hCW, ?_⟩
  have hV := volumeConstant_pos
  have hC := incidenceConstant_pos
  have hQ := retained_radix_sq_upper h original horiginal A hA hAne L hL
  calc
    _ ≤ (1024 * 175616 * volumeConstant) *
        (NativeOriginalParentDensityCore.factor d g L : ℝ) *
        (16 * incidenceConstant^(2 / (L : ℝ)) * D.thickness^(-8 / (L : ℝ))) *
        D.thickness^beta := by gcongr
    _ = densityCoefficient d g L * D.thickness^(beta - 8 / (L : ℝ)) := by
      dsimp [densityCoefficient]
      rw [show beta - 8 / (L : ℝ) = -8 / (L : ℝ) + beta by ring,
        Real.rpow_add hd]
      ring
    _ ≤ _ := hDen

end NativeLocalAdmissionBudget
