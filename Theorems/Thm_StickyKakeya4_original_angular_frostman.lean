import Theorems.Thm_StickyKakeya4_original_angular_alphabet_translation
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalAngularFrostman
open Classical FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open OriginalAngularAlphabetTranslation

/-- Source AD bounds imply the relative population law using the cardinality
 of that SAME original angular alphabet. -/
theorem AD_relative_point_bound (Phi : Finset ℝ) {mesh K kappa r : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (hK : 0 < K)
    (hAD : ADBounds Phi mesh K kappa) (p : ℝ) (hp : p ∈ Phi)
    (hr : mesh ≤ r) (hr1 : r ≤ 1) :
    ((carrierBall Phi p r).card : ℝ) ≤ K^2*r^kappa*(Phi.card : ℝ) := by
  have hs := scaled_bounds_of_ADBounds hm hK hAD
  have hu := (hs p hp r hr hr1).2
  have hl := (hs p hp 1 hm1 le_rfl).1
  have hcard : ((carrierBall Phi p 1).card : ℝ) ≤ (Phi.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  have hnorm : (1:ℝ) ≤ K*mesh^kappa*(Phi.card : ℝ) := by
    simpa only [Real.one_rpow] using hl.trans
      (mul_le_mul_of_nonneg_left hcard (by positivity))
  calc
    _ = 1*((carrierBall Phi p r).card : ℝ) := by ring
    _ ≤ (K*mesh^kappa*(Phi.card : ℝ))*((carrierBall Phi p r).card : ℝ) :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ = (K*(Phi.card : ℝ))*(mesh^kappa*((carrierBall Phi p r).card : ℝ)) := by ring
    _ ≤ (K*(Phi.card : ℝ))*(K*r^kappa) := mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by ring

/-- All-center/all-radius Frostman control, with its explicit factor2^kappa,
 follows from the source point-centered AD law. -/
theorem AD_relative_allcenter (Phi : Finset ℝ) {mesh K kappa : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (hK : 1 ≤ K) (hk : 0 ≤ kappa)
    (hAD : ADBounds Phi mesh K kappa) (center r : ℝ) (hr : mesh ≤ r) :
    ((carrierBall Phi center r).card : ℝ) ≤ (2:ℝ)^kappa*K^2*r^kappa*(Phi.card : ℝ) := by
  have hr0 : 0 < r := hm.trans_le hr
  have hK0 : 0 < K := by linarith
  by_cases hsmall : 2*r ≤ 1
  · by_cases hempty : (carrierBall Phi center r).Nonempty
    · obtain ⟨p,hpPhi,hpc⟩ := (show ∃ p, p ∈ Phi ∧ dist p center ≤ r from by
        obtain ⟨p,hp⟩ := hempty
        exact ⟨p,(mem_carrierBall _ _ _ _).mp hp⟩)
      have hsub : carrierBall Phi center r ⊆ carrierBall Phi p (2*r) := by
        intro q hq
        obtain ⟨hqPhi,hqc⟩ := (mem_carrierBall _ _ _ _).mp hq
        apply (mem_carrierBall _ _ _ _).mpr
        refine ⟨hqPhi,?_⟩
        have hd := dist_triangle q center p
        rw [dist_comm center p] at hd
        linarith
      have hb := AD_relative_point_bound Phi hm hm1 hK0 hAD p hpPhi (by linarith : mesh ≤ 2*r) hsmall
      have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hb
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hr0.le] at hc
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hc
    · have heq := Finset.not_nonempty_iff_eq_empty.mp hempty
      rw [heq,Finset.card_empty,Nat.cast_zero]
      positivity
  · have hpow : (1:ℝ) ≤ (2*r)^kappa := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) (by linarith : 1 ≤ 2*r) hk
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hr0.le] at hpow
    have hK2 : (1:ℝ) ≤ K^2 := by nlinarith
    have hfac : (1:ℝ) ≤ (2:ℝ)^kappa*K^2*r^kappa := by
      have hh := mul_le_mul hpow hK2 (by norm_num : (0:ℝ)≤1) (by positivity : 0 ≤ (2:ℝ)^kappa*r^kappa)
      nlinarith only [hh]
    calc
      _ ≤ (Phi.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg Phi.card : (0:ℝ)≤Phi.card)

/-- The translated source C may be used at a finer common ABC mesh, with the
 exact angular-mesh ratio charged in the Frostman constant. -/
theorem shifted_finer_mesh_frostman (Phi : Finset ℝ) (anchor : ℝ) {mesh abcMesh K kappa : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (habc : 0 < abcMesh) (hscale : abcMesh ≤ mesh)
    (hK : 1 ≤ K) (hk : 0 ≤ kappa) (hAD : ADBounds Phi mesh K kappa)
    (center r : ℝ) (hr : abcMesh ≤ r) :
    ((carrierBall (shifted Phi anchor) center r).card : ℝ) ≤
      ((2:ℝ)^kappa*K^2*(mesh/abcMesh)^kappa)*r^kappa*((shifted Phi anchor).card : ℝ) := by
  have hr0 : 0 < r := habc.trans_le hr
  have hratio : 1 ≤ mesh/abcMesh := (le_div_iff₀ habc).mpr (by simpa using hscale)
  have hmax : max r mesh ≤ (mesh/abcMesh)*r := by
    apply max_le
    · nlinarith
    · have hh := mul_le_mul_of_nonneg_left hr (div_pos hm habc).le
      have heq : (mesh/abcMesh)*abcMesh=mesh := by field_simp
      simpa only [heq] using hh
  have hsub : carrierBall (shifted Phi anchor) center r ⊆
      carrierBall (shifted Phi anchor) center (max r mesh) := by
    intro c hc
    obtain ⟨hcP,hcr⟩ := (mem_carrierBall _ _ _ _).mp hc
    exact (mem_carrierBall _ _ _ _).mpr ⟨hcP,hcr.trans (le_max_left _ _)⟩
  have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (AD_relative_allcenter (shifted Phi anchor) hm hm1 hK hk (shifted_ADBounds Phi anchor hAD)
      center (max r mesh) (le_max_right _ _))
  have hp := Real.rpow_le_rpow (le_trans hr0.le (le_max_left _ _)) hmax hk
  rw [Real.mul_rpow (div_pos hm habc).le hr0.le] at hp
  calc
    _ ≤ (2:ℝ)^kappa*K^2*(max r mesh)^kappa*((shifted Phi anchor).card : ℝ) := hc
    _ ≤ (2:ℝ)^kappa*K^2*((mesh/abcMesh)^kappa*r^kappa)*((shifted Phi anchor).card : ℝ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = _ := by ring

end OriginalAngularFrostman
