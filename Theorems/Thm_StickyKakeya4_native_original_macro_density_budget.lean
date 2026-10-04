import Theorems.Thm_StickyKakeya4_native_original_macro_source_density
import Theorems.Thm_StickyKakeya4_original_literal_macro_height_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeOriginalMacroDensityBudget
open NativeOriginalMacroSourceDensity
/-- All four literal source costs fit fixed powers of the same original
 budget. The threshold is numerical and independent of the grain exponent. -/
theorem source_cost_power_bounds {K C0 DirErr Cxi L IncErr : ℝ}
    (hK : 203956944896 ≤ K)
    (hC : 0 ≤ C0) (hCK : C0 ≤ K) (hD : 0 ≤ DirErr) (hDK : DirErr ≤ K)
    (hXi : 0 ≤ Cxi) (hXiK : Cxi ≤ K) (hL : 0 ≤ L) (hLK : L ≤ K)
    (hI : 0 ≤ IncErr) (hIK : IncErr ≤ K) :
    (192*K^2)*(2*C0+2) ≤ K^4 ∧ pointCost K ≤ K^5 ∧
      tubeCost K C0 DirErr Cxi L ≤ K^5 ∧ (16*IncErr+2)^3 ≤ K^4 := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hDir0 : 0 ≤ directionCost C0 DirErr Cxi L := by
    unfold directionCost jointError
    positivity
  have hDirK : directionCost C0 DirErr Cxi L ≤ 146*K := by
    unfold directionCost jointError
    linarith
  refine ⟨?_,?_,?_,?_⟩
  · have hs : 2*C0+2 ≤ 4*K := by linarith
    have hc : (768:ℝ) ≤ K := by linarith
    calc
      _ ≤ (192*K^2)*(4*K) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 768*K^3 := by ring
      _ ≤ K*K^3 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  · exact (OriginalLiteralMacroHeightBudget.original_macro_cost_absorption
      (show 79626240000 ≤ K by linarith) hL hLK).1
  · unfold tubeCost
    calc
      _ ≤ 65536*K*(146*K)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hDir0 hDirK 3) (by positivity)
      _ = 203956944896*K^4 := by ring
      _ ≤ K*K^4 := mul_le_mul_of_nonneg_right hK (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (18*K)^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ = 5832*K^3 := by ring
      _ ≤ K*K^3 := mul_le_mul_of_nonneg_right (show (5832:ℝ)≤K by linarith) (by positivity)
      _ = _ := by ring
/-- The actual macro-cell incidence density has an explicit original-budget
 lower bound. This consumes no AD or density envelope for an output set. -/
theorem source_density_power_lower {K C0 DirErr Cxi L IncErr : ℝ}
    (hK : 203956944896 ≤ K)
    (hC : 0 ≤ C0) (hCK : C0 ≤ K) (hD : 0 ≤ DirErr) (hDK : DirErr ≤ K)
    (hXi : 0 ≤ Cxi) (hXiK : Cxi ≤ K) (hL : 0 ≤ L) (hLK : L ≤ K)
    (hI : 0 ≤ IncErr) (hIK : IncErr ≤ K) :
    1/K^18 ≤ densityCoefficient K C0 DirErr Cxi L IncErr := by
  have hK0 : 0 < K := by linarith
  obtain ⟨hf,hp,ht,ho⟩ := source_cost_power_bounds hK hC hCK hD hDK hXi hXiK hL hLK hI hIK
  have hp0 : 0 ≤ pointCost K := by unfold pointCost; positivity
  have ht0 : 0 ≤ tubeCost K C0 DirErr Cxi L := by
    unfold tubeCost directionCost jointError
    positivity
  have hden : ((192*K^2)*(2*C0+2))*(pointCost K*tubeCost K C0 DirErr Cxi L*(16*IncErr+2)^3) ≤ K^18 := by
    calc
      _ ≤ K^4*(K^5*K^5*K^4) := by gcongr
      _ = _ := by ring
  unfold densityCoefficient
  rw [div_div]
  exact one_div_le_one_div_of_le (by unfold pointCost tubeCost directionCost jointError; positivity) hden
/-- The actual full terminal alphabet loss and reference-angle population
 ratio are also controlled by the original source budget. -/
theorem source_collision_cost_power_bounds {K C0 DirErr Cxi L : ℝ}
    (hK : 203956944896 ≤ K)
    (hC : 0 ≤ C0) (hCK : C0 ≤ K) (hD : 0 ≤ DirErr) (hDK : DirErr ≤ K)
    (hXi : 0 ≤ Cxi) (hXiK : Cxi ≤ K) (hL : 0 ≤ L) (hLK : L ≤ K) :
    (2*K*(directionCost C0 DirErr Cxi L)^3)*(192*K^2) ≤ K^7 ∧
      512*(192*K^2)^3*(1+C0)^3 ≤ K^10 := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hDir0 : 0 ≤ directionCost C0 DirErr Cxi L := by
    unfold directionCost jointError
    positivity
  have hDirK : directionCost C0 DirErr Cxi L ≤ 146*K := by
    unfold directionCost jointError
    linarith
  constructor
  · calc
      _ ≤ (2*K*(146*K)^3)*(192*K^2) := by gcongr
      _ = 1195060224*K^6 := by ring
      _ ≤ K*K^6 := mul_le_mul_of_nonneg_right (show (1195060224:ℝ)≤K by linarith) (by positivity)
      _ = _ := by ring
  · have hs : 1+C0 ≤ 2*K := by linarith
    calc
      _ ≤ 512*(192*K^2)^3*(2*K)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs 3) (by positivity)
      _ = 28991029248*K^9 := by ring
      _ ≤ K*K^9 := mul_le_mul_of_nonneg_right (show (28991029248:ℝ)≤K by linarith) (by positivity)
      _ = _ := by ring
/-- The source exponent chooses its numerical cutoff before the sets and
 kappa. The resulting literal density is at least delta^(18 eta). -/
theorem exists_source_density_power_cutoff {eta : ℝ} (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta : ℝ,
      0 < delta → delta ≤ delta0 → ∀ C0 DirErr Cxi L IncErr : ℝ,
      0 ≤ C0 → C0 ≤ delta^(-eta) → 0 ≤ DirErr → DirErr ≤ delta^(-eta) →
      0 ≤ Cxi → Cxi ≤ delta^(-eta) → 0 ≤ L → L ≤ delta^(-eta) →
      0 ≤ IncErr → IncErr ≤ delta^(-eta) →
      delta^(18*eta) ≤ densityCoefficient (delta^(-eta)) C0 DirErr Cxi L IncErr := by
  obtain ⟨d0,hd0,hd01,hcut⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff heta
    (by norm_num : (0:ℝ) < 1/203956944896)
  refine ⟨d0,hd0,hd01,?_⟩
  intro delta hd hdd C0 DirErr Cxi L IncErr hC hCK hD hDK hXi hXiK hL hLK hI hIK
  have hp : 0 < delta^eta := Real.rpow_pos_of_pos hd _
  have hlarge : 203956944896 ≤ delta^(-eta) := by
    rw [Real.rpow_neg hd.le,inv_eq_one_div]
    apply (le_div_iff₀ hp).mpr
    have hs := hcut delta hd hdd
    linarith
  have he : 1/(delta^(-eta))^18=delta^(18*eta) := by
    rw [←Real.rpow_mul_natCast hd.le]
    norm_num only [Nat.cast_ofNat]
    rw [show -eta*(18:ℝ)=-(18*eta) by ring,Real.rpow_neg hd.le]
    simp
  rw [←he]
  exact source_density_power_lower hlarge hC hCK hD hDK hXi hXiK hL hLK hI hIK
end NativeOriginalMacroDensityBudget
