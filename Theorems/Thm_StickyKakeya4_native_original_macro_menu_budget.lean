import Theorems.Thm_StickyKakeya4_native_original_macro_printed_core
import Theorems.Thm_StickyKakeya4_native_original_macro_density_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeOriginalMacroMenuBudget
open OriginalMacroFullReferenceCore NativeOriginalMacroSourceDensity NativeOriginalMacroDensityBudget
open NativeOriginalMacroPrintedCore
/-- The persistent menu coefficient pays the original reference ratio three
 times. All numerator and denominator bounds stay on the same original data. -/
theorem menuCoefficient_power_lower {K lambda C imageLoss D U N : ℝ}
    (hK : 4 ≤ K) (hC : 0 < C) (hL : 0 < imageLoss) (hD : 0 < D)
    (hU : 0 < U) (hN : 0 < N)
    (hlambda : 1/K^18 ≤ lambda) (hCK : C ≤ K^4) (hLK : imageLoss ≤ K^7)
    (hR : U*N/D ≤ K^10) : 1/K^130 ≤ menuCoefficient lambda C imageLoss D U N := by
  have hK0 : 0 < K := by linarith
  have hR0 : 0 < U*N/D := by positivity
  have hnum : 1/K^72 ≤ lambda^4 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/K^18) hlambda 4
    simpa only [one_div_pow,←pow_mul,show (18:ℕ)*4=72 by norm_num] using hh
  have hden : 4*C^5*imageLoss*(U*N/D)^3 ≤ K^58 := by
    calc
      _ ≤ K*(K^4)^5*K^7*(K^10)^3 := by gcongr
      _ = _ := by ring
  have he : menuCoefficient lambda C imageLoss D U N=
      lambda^4/(4*C^5*imageLoss*(U*N/D)^3) := by
    unfold menuCoefficient OriginalScalarCollisionMass.collisionAlpha
    field_simp
  rw [he]
  apply (le_div_iff₀ (show 0 < 4*C^5*imageLoss*(U*N/D)^3 by positivity)).mpr
  calc
    _ ≤ (1/K^130)*K^58 := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 1/K^72 := by field_simp
    _ ≤ _ := hnum
/-- The actual selected Phi population bound from the raw constructor
 yields a fixed original-budget menu density, independent of kappa. -/
theorem rawMenuCoefficient_power_lower {delta q K kappa C0 DirErr Cxi L IncErr Nphi : ℝ}
    (hd : 0 < delta) (hq : 0 < q) (hK : 203956944896 ≤ K)
    (hC : 0 ≤ C0) (hCK : C0 ≤ K) (hD : 0 ≤ DirErr) (hDK : DirErr ≤ K)
    (hXi : 0 ≤ Cxi) (hXiK : Cxi ≤ K) (hL : 0 ≤ L) (hLK : L ≤ K)
    (hI : 0 ≤ IncErr) (hIK : IncErr ≤ K) (hNphi : 0 < Nphi)
    (hRatio : OriginalAngularSourcePopulation.ballCap delta q (192*K^2) kappa (2*C0)*Nphi/
      OriginalAngularSourcePopulation.degree delta (192*K^2) kappa C0 ≤
        512*(192*K^2)^3*(1+C0)^3) :
    1/K^130 ≤ rawMenuCoefficient delta q K kappa C0 DirErr Cxi L IncErr Nphi := by
  have hK0 : 0 < K := by linarith
  have hKg : 0 < 192*K^2 := by positivity
  obtain ⟨_hf,_hp,_ht,hOcc⟩ := source_cost_power_bounds hK hC hCK hD hDK hXi hXiK hL hLK hI hIK
  obtain ⟨hImage,hRef⟩ := source_collision_cost_power_bounds hK hC hCK hD hDK hXi hXiK hL hLK
  exact menuCoefficient_power_lower (show 4 ≤ K by linarith)
    (by positivity : 0 < (16*IncErr+2)^3)
    (by unfold directionCost jointError; positivity)
    (OriginalAngularSourcePopulation.degree_pos hd hKg hC)
    (OriginalAngularSourcePopulation.ballCap_pos hd hq hKg (show 0 ≤ 2*C0 by positivity))
    hNphi (source_density_power_lower hK hC hCK hD hDK hXi hXiK hL hLK hI hIK)
    hOcc hImage (hRatio.trans hRef)
/-- The source exponent selects the cutoff before all original sets and
 kappa; the genuine full-direction menus have density at least delta^(130 eta). -/
theorem exists_source_menu_power_cutoff {eta : ℝ} (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta q kappa C0 DirErr Cxi L IncErr Nphi : ℝ,
      0 < delta → delta ≤ delta0 → 0 < q →
      0 ≤ C0 → C0 ≤ delta^(-eta) → 0 ≤ DirErr → DirErr ≤ delta^(-eta) →
      0 ≤ Cxi → Cxi ≤ delta^(-eta) → 0 ≤ L → L ≤ delta^(-eta) →
      0 ≤ IncErr → IncErr ≤ delta^(-eta) → 0 < Nphi →
      OriginalAngularSourcePopulation.ballCap delta q (192*(delta^(-eta))^2) kappa (2*C0)*Nphi/
        OriginalAngularSourcePopulation.degree delta (192*(delta^(-eta))^2) kappa C0 ≤
          512*(192*(delta^(-eta))^2)^3*(1+C0)^3 →
      delta^(130*eta) ≤ rawMenuCoefficient delta q (delta^(-eta)) kappa C0 DirErr Cxi L IncErr Nphi := by
  obtain ⟨d0,hd0,hd01,hcut⟩ :=
    OriginalLiteralMacroHeightBudget.exists_original_macro_power_cutoff (L := 203956944896) heta
  refine ⟨d0,hd0,hd01,?_⟩
  intro delta q kappa C0 DirErr Cxi L IncErr Nphi hd hdd hq hC hCK hD hDK hXi hXiK hL hLK hI hIK hNphi hRatio
  have he : 1/(delta^(-eta))^130=delta^(130*eta) := by
    rw [←Real.rpow_mul_natCast hd.le]
    norm_num only [Nat.cast_ofNat]
    rw [show -eta*(130:ℝ)=-(130*eta) by ring,Real.rpow_neg hd.le]
    simp
  rw [←he]
  exact rawMenuCoefficient_power_lower hd hq (hcut delta hd hdd).2
    hC hCK hD hDK hXi hXiK hL hLK hI hIK hNphi hRatio
end NativeOriginalMacroMenuBudget
