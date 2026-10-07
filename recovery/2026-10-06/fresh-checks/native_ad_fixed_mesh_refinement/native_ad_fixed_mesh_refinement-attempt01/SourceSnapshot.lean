import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeADFixedMeshRefinement
open Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

/-- Lowering the declared mesh by a bounded factor costs only C^s.
Below the original mesh the actual center gives the lower count, while
the original AD test at mu gives the upper count. No AD test is used
outside its original interval [mu,1]. -/
theorem refine_mesh {X : Type*} [PseudoMetricSpace X] (P : Finset X)
    {rho mu C K s : ℝ} (hrho : 0 < rho) (hrhomu : rho ≤ mu) (hmu1 : mu ≤ 1)
    (hscale : mu ≤ C*rho) (hC : 1 ≤ C) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (H : ADBounds P mu K s) : ADBounds P rho (C^s*K) s := by
  classical
  have hmu : 0 < mu := hrho.trans_le hrhomu
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hCp : 0 < C^s := Real.rpow_pos_of_pos hC0 s
  have hCp1 : 1 ≤ C^s := Real.one_le_rpow hC hs
  have hden : 0 < C^s*K := mul_pos hCp hK0
  have hKle : K ≤ C^s*K := le_mul_of_one_le_left hK0.le hCp1
  intro x hx r hrhor hr1
  have hr : 0 < r := hrho.trans_le hrhor
  have hpower : 0 ≤ (r/rho)^s := Real.rpow_nonneg (div_nonneg hr.le hrho.le) _
  by_cases hlarge : mu ≤ r
  · have hh := H x hx r hlarge hr1
    have hratio : r/rho ≤ C*(r/mu) := by
      have hm : mu/rho ≤ C := (div_le_iff₀ hrho).mpr hscale
      have hprod := mul_le_mul_of_nonneg_right hm (div_nonneg hr.le hmu.le)
      have heq : (mu/rho)*(r/mu)=r/rho := by field_simp
      simpa only [heq] using hprod
    have hp := Real.rpow_le_rpow (div_nonneg hr.le hrho.le) hratio hs
    rw [Real.mul_rpow hC0.le (div_nonneg hr.le hmu.le)] at hp
    have hlow : (r/rho)^s/(C^s*K) ≤ (r/mu)^s/K := by
      apply (div_le_div_iff₀ hden hK0).mpr
      have hm := mul_le_mul_of_nonneg_right hp hK0.le
      nlinarith only [hm]
    have hratios : r/mu ≤ r/rho := div_le_div_of_nonneg_left hr.le hrho hrhomu
    have hpup := Real.rpow_le_rpow (div_nonneg hr.le hmu.le) hratios hs
    refine ⟨hlow.trans hh.1,?_⟩
    exact hh.2.trans ((mul_le_mul_of_nonneg_left hpup hK0.le).trans
      (mul_le_mul_of_nonneg_right hKle hpower))
  · have hrmu : r ≤ mu := le_of_lt (lt_of_not_ge hlarge)
    have hratio : r/rho ≤ C := (div_le_iff₀ hrho).mpr (hrmu.trans hscale)
    have hp := Real.rpow_le_rpow (div_nonneg hr.le hrho.le) hratio hs
    have hlow1 : (r/rho)^s/(C^s*K) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      simpa only [one_mul] using hp.trans (le_mul_of_one_le_right hCp.le hK)
    have hpoint : x∈carrierBall P x r :=
      (mem_carrierBall P x x r).mpr ⟨hx,by simpa only [dist_self] using hr.le⟩
    have hone : (1:ℝ) ≤ (carrierBall P x r).card :=
      Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨x,hpoint⟩)
    have hsub : carrierBall P x r ⊆ carrierBall P x mu := by
      intro y hy
      obtain ⟨hyP,hyd⟩ := (mem_carrierBall P y x r).mp hy
      exact (mem_carrierBall P y x mu).mpr ⟨hyP,hyd.trans hrmu⟩
    have hcard : ((carrierBall P x r).card:ℝ) ≤ (carrierBall P x mu).card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hup : ((carrierBall P x mu).card:ℝ) ≤ K := by
      simpa only [div_self hmu.ne',Real.one_rpow,mul_one] using (H x hx mu le_rfl hmu1).2
    have hpow1 : 1 ≤ (r/rho)^s := Real.one_le_rpow
      ((le_div_iff₀ hrho).mpr (by simpa only [one_mul] using hrhor)) hs
    refine ⟨hlow1.trans hone,?_⟩
    exact (hcard.trans hup).trans (hKle.trans
      (le_mul_of_one_le_right hden.le hpow1))

end NativeADFixedMeshRefinement
