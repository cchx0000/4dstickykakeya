import Theorems.Thm_StickyKakeya4_original_coefficient_normalization
import Theorems.Thm_StickyKakeya4_original_coefficient_profile_radius
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace OriginalFullCoefficientNormalization
open OriginalCoefficientRadius OriginalCoefficientDensityProfile OriginalCoefficientNormalization
open OriginalCoefficientProfileRadius GKZOriginalGapEnergy

/-- Full-mesh original weak caps supply both absolute normalized regularity
and the stronger radius loss needed by the later fixed polynomial degree. -/
theorem exists_original_full_profile_normalization (D : Finset ℝ)
    {delta kappa B K u : ℝ} (hD : D.Nonempty) (hdelta : 0 < delta)
    (hkappa : 0 ≤ kappa) (hkappa1 : kappa ≤ 1) (hdB : delta ≤ B)
    (hbox : ∀ x∈D, ∀ y∈D, |x-y| ≤ B)
    (hprofile : ScalarFrostman D delta K u) :
    ∃ (S : Finset ℝ) (c R : ℝ), S⊆D ∧ c∈S ∧ delta ≤ R ∧ R ≤ B ∧
      (S.image (fun x => (x-c)/R)).card=S.card ∧
      (∀ z∈S.image (fun x => (x-c)/R), |z| ≤ 1) ∧
      ScalarFrostman (S.image (fun x => (x-c)/R)) (delta/R) 2 kappa ∧
      (D.card:ℝ)*R^kappa ≤ B^kappa*S.card ∧
      (1 ≤ R ∨ 1 ≤ K*B^kappa*R^(u-kappa)) := by
  obtain ⟨S,hSD,hS,hmax⟩ := exists_original_maximal_density D hD hdelta (kappa:=kappa)
  obtain ⟨c,hc⟩ := hS
  let R := radius S delta
  have hR : 0 < R := hdelta.trans_le (mesh_le_radius S delta)
  have hDB : radius D delta ≤ B := radius_le D hdB hbox
  have hRB : R ≤ B := (radius_mono hSD).trans hDB
  refine ⟨S,c,R,hSD,hc,mesh_le_radius S delta,hRB,?_,?_,?_,?_,?_⟩
  · exact Finset.card_image_of_injective S (original_normalization_injective hR)
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    rw [abs_div,abs_of_pos hR]
    exact (div_le_one hR).mpr (pair_le_radius S delta hx hc)
  · exact original_normalized_profile D S hdelta hkappa hkappa1 hSD hmax c
  · exact original_retained_mass D S hdelta hkappa hDB hmax
  · by_cases hr : R ≤ 1
    · exact Or.inr (original_full_profile_radius D S hdelta hkappa ⟨c,hc⟩ hSD hDB hmax hr hprofile)
    · exact Or.inl (le_of_not_ge hr)

/-- A stated small-power profile/range budget gives an actual small-power
radius lower bound. Its exponent remains explicit before degree is chosen. -/
theorem original_full_radius_power {delta R H eta u kappa : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hR : 0 < R) (heta : 0 ≤ eta)
    (hgap : kappa < u) (hbudget : H ≤ delta^(-eta))
    (hradius : 1 ≤ R ∨ 1 ≤ H*R^(u-kappa)) :
    delta^(eta/(u-kappa)) ≤ R := by
  have he : 0 < u-kappa := sub_pos.mpr hgap
  have ha : 0 ≤ eta/(u-kappa) := div_nonneg heta he.le
  rcases hradius with hr | hr
  · exact (Real.rpow_le_one hd.le hd1 ha).trans hr
  · have hp := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hR.le (u-kappa))
    have hbase : 1 ≤ delta^(-eta)*R^(u-kappa) := hr.trans hp
    have hm := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hd.le eta)
    have hid : delta^eta*delta^(-eta)=1 := by
      rw [← Real.rpow_add hd]
      simp only [add_neg_cancel,Real.rpow_zero]
    have hpow : delta^eta ≤ R^(u-kappa) := by
      simpa only [mul_one,← mul_assoc,hid,one_mul] using hm
    have heq : (delta^(eta/(u-kappa)))^(u-kappa)=delta^eta := by
      rw [← Real.rpow_mul hd.le,div_mul_cancel₀ _ he.ne']
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hd.le _) hR.le he).mp
    simpa only [heq] using hpow

/-- Both normalized mesh constraints survive a FIXED final degree, with
exact loss d*alpha. The degree cannot be allowed to depend on delta. -/
theorem original_final_polynomial_mesh {delta R alpha : ℝ} (d : ℕ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (ha : 0 ≤ alpha)
    (hdim : 1 ≤ d) (hlower : delta^alpha ≤ R) :
    max (delta/R) (delta/R^d) ≤ delta^(1-(d:ℝ)*alpha) := by
  have hfirst : delta/R ≤ delta^(1-alpha) := by
    calc
      delta/R ≤ delta/delta^alpha := div_le_div_of_nonneg_left hd.le
        (Real.rpow_pos_of_pos hd alpha) hlower
      _ = delta^(1-alpha) := by rw [Real.rpow_sub hd,Real.rpow_one]
  have hpow : delta^((d:ℝ)*alpha) ≤ R^d := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hd.le alpha) hlower d
    simpa only [← Real.rpow_mul_natCast hd.le, mul_comm alpha (d:ℝ)] using hh
  have hsecond : delta/R^d ≤ delta^(1-(d:ℝ)*alpha) := by
    calc
      delta/R^d ≤ delta/delta^((d:ℝ)*alpha) := div_le_div_of_nonneg_left hd.le
        (Real.rpow_pos_of_pos hd _) hpow
      _ = delta^(1-(d:ℝ)*alpha) := by rw [Real.rpow_sub hd,Real.rpow_one]
  have hdreal : (1:ℝ) ≤ d := by exact_mod_cast hdim
  have hexp : 1-(d:ℝ)*alpha ≤ 1-alpha := by nlinarith only [hdreal,ha]
  exact max_le (hfirst.trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp)) hsecond

end OriginalFullCoefficientNormalization
