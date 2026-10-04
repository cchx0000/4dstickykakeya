import Theorems.Thm_StickyKakeya4_native_euclidean_cover_input
import Theorems.Thm_StickyKakeya4_native_planar_cover_lemma53
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace NativeQuarterSquareCoverSource
open NativeEuclideanCoverInput NativePlanarCoverLemma53 NativeScalarCoverAD
open NativePaperAlignmentScales NativeDyadicTubeStopping FiniteVoronoiRealADCoarsening
noncomputable section

lemma fixed_factor_absorption {L a : ℝ} (hL : 1 ≤ L) (ha : 0 < a) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ d0 → L ≤ delta ^ (-a) := by
  let d0 := L ^ (-(1 / a))
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hd0 : 0 < d0 := Real.rpow_pos_of_pos hLp _
  have hd01 : d0 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr (one_div_nonneg.mpr ha.le))
  refine ⟨d0, hd0, hd01, ?_⟩
  intro delta hdelta hsmall
  have hpow : d0 ^ (-a) = L := by
    dsimp [d0]
    rw [← Real.rpow_mul hLp.le]
    have he : -(1 / a) * (-a) = 1 := by field_simp [ha.ne']
    rw [he, Real.rpow_one]
  rw [← hpow]
  exact Real.rpow_le_rpow_of_nonpos hdelta hsmall (by linarith)

lemma point_AD_mono_constant {X : Type*} [PseudoMetricSpace X] {A : Finset X} {delta C D t : ℝ}
    (hdelta : 0 < delta) (hC : 0 < C) (hCD : C ≤ D) (H : ADBounds A delta C t) :
    ADBounds A delta D t := by
  intro x hx r hrlo hrhi
  have hr := hdelta.trans_le hrlo
  have hp : 0 ≤ (r / delta) ^ t := by positivity
  exact ⟨(div_le_div_of_nonneg_left hp hC hCD).trans (H x hx r hrlo hrhi).1,
    ((H x hx r hrlo hrhi).2).trans (mul_le_mul_of_nonneg_right hCD hp)⟩

/-- Original Euclidean cover-AD input and scalar cover-AD output on unchanged
separated quarter-square points. Fixed occupancy/norm costs are absorbed into
the incoming exponent and its small-scale threshold. -/
theorem quarter_square_cover_source_alignment {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ eta0 chi : ℝ, 0 < eta0 ∧ 0 < chi ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ (A : Finset Plane) (delta t : ℝ),
          A.Nonempty → 0 < delta → delta ≤ delta0 → 0 ≤ t → t ≤ 2 →
          (∀ p ∈ A, ∀ i : Fin 2, |p i| ≤ 1 / 4) → EuclideanSeparated A delta →
          EuclideanCoverAD A delta (delta ^ (-eta)) t →
          ∃ rho tau s : ℝ, ∃ j : Fin 2, ∃ A' : Finset Plane,
            A' ⊆ A ∧ A'.Nonempty ∧ delta ≤ rho ∧ rho < tau ∧ tau ≤ 1 ∧
            0 ≤ s ∧ s ≤ min t 1 ∧
            (∃ ir it : ℕ, rho = scale delta ir ∧ tau = scale delta it) ∧
            (∃ n : ℕ, rho / tau = 1 / (2 : ℝ) ^ n) ∧
            delta ^ (-chi) ≤ tau / rho ∧
            (rho / tau) ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            delta ^ zeta * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            ∀ a ∈ A', NearlyCoverAligned
              ((localBall A' a tau).image (normalization j a tau))
              (rho / tau) t s ((rho / tau) ^ (-zeta)) := by
  obtain ⟨etaB, chi, hetaB, hchi, hmain⟩ := native_quarter_square_cover_lemma53 hzeta
  obtain ⟨dabs, hdabs, hdabs1, habs⟩ := fixed_factor_absorption inputConstant_ge_one (half_pos hetaB)
  obtain ⟨dout, hdout, hwork⟩ := hmain etaB hetaB le_rfl
  refine ⟨etaB / 2, chi, half_pos hetaB, hchi, ?_⟩
  intro eta _heta hetasmall
  refine ⟨min dout dabs, lt_min hdout hdabs, ?_⟩
  intro A delta t hne hdelta hdeltasmall ht ht2 hbox hsep hAD
  have hdout' : delta ≤ dout := hdeltasmall.trans (min_le_left _ _)
  have hdabs' : delta ≤ dabs := hdeltasmall.trans (min_le_right _ _)
  have hd1 : delta ≤ 1 := hdabs'.trans hdabs1
  have hCpos : 0 < delta ^ (-eta) := Real.rpow_pos_of_pos hdelta _
  have hnative := native_AD_of_euclidean_cover_AD hdelta hd1 hCpos ht ht2 hsep hbox hAD
  have hfixed := habs delta hdelta hdabs'
  have hpower : delta ^ (-eta) ≤ delta ^ (-(etaB / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hd1 (by linarith only [hetasmall])
  have hprod := mul_le_mul hfixed hpower hCpos.le (Real.rpow_nonneg hdelta.le _)
  have hexp : delta ^ (-(etaB / 2)) * delta ^ (-(etaB / 2)) = delta ^ (-etaB) := by
    rw [← Real.rpow_add hdelta]
    congr 1
    ring
  rw [hexp] at hprod
  have hinput : ADBounds A delta (delta ^ (-etaB)) t :=
    point_AD_mono_constant hdelta (mul_pos (zero_lt_one.trans_le inputConstant_ge_one) hCpos) hprod hnative
  exact hwork A delta t hne hdelta hdout' ht ht2 hbox hinput
end
end NativeQuarterSquareCoverSource
