import Theorems.Thm_StickyKakeya4_native_grid_support_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeGridSupportLocal
open Classical Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeLiteralGridOverlap NativeLiteralGridCoverAD NativeRecodedGridUpper NativeGridSupportPopulation

lemma enlarge_AD {X : Type*} [PseudoMetricSpace X] (A : Finset X) {mu K C t : ℝ}
    (hmu : 0 < mu) (hK : 0 < K) (hKC : K ≤ C) (H : ADBounds A mu K t) : ADBounds A mu C t := by
  intro x hx r hr hr1
  obtain ⟨hlo,hhi⟩ := H x hx r hr hr1
  have hrp : 0 < r := hmu.trans_le hr
  constructor
  · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (div_nonneg hrp.le hmu.le) _) hK hKC).trans hlo
  · exact hhi.trans (mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (div_nonneg hrp.le hmu.le) _))

/-- Local coarse-cube upper from the original fine AD set and its genuine
bounded support. Test radii may exceed one; that range uses the derived
global coarse count, never an out-of-range source AD assertion. -/
theorem occupied_ball_upper {d : ℕ} (A : Finset (Fin d → ℝ))
    {mu rho K t : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho) (hrho1 : rho ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (H : ADBounds A mu K t) (hbox : ∀x∈A,dist x 0 ≤ 2)
    (x : Fin d → ℝ) (r : ℝ) (hr : rho ≤ r) :
    (((A.image (label rho)).filter (fun q => dist (center rho q) x ≤ r)).card:ℝ)  ≤ 
      ((9^d:ℕ):ℝ)*(((13^d:ℕ):ℝ))^2*K^2*(6:ℝ)^t*(r/rho)^t := by
  have hrho : 0 < rho := hmu.trans_le hmurho
  have hKp : 0 < K := zero_lt_one.trans_le hK
  let C : ℝ := ((13^d:ℕ):ℝ)
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact_mod_cast (show 1 ≤ (13:ℕ)^d from Nat.one_le_pow _ _ (by norm_num))
  have hCK : K ≤ C*K := le_mul_of_one_le_left hKp.le hC
  have hCK1 : 1 ≤ C*K := hK.trans hCK
  have HC : ADBounds A mu (C*K) t := enlarge_AD A hmu hKp hCK H
  have hglobal : (A.card:ℝ) ≤ (C*K)*mu^(-t) :=
    global_card_of_bounded_AD A hmu (hmurho.trans hrho1) hKp H hbox
  let B := A.image (label rho)
  by_cases hr1 : r ≤ 1
  · have hnear : ∀q∈B,∃a∈A,dist (center rho q) a ≤ (1:ℝ)*rho := by
      intro q hq
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hq
      refine ⟨a,ha,?_⟩
      have hh := center_label_close hrho a
      linarith only [hh,hrho]
    have hh := actual_grid_ball_upper A B hmu hmurho hCK1 ht HC hglobal hnear x r hr hr1
    rw [realized_ball_card B hrho x r] at hh
    norm_num only [Nat.ceil_one,Nat.cast_one] at hh
    convert hh using 1
    dsimp only [C]
    norm_num
    ring
  · have hrone : 1 ≤ r := (lt_of_not_ge hr1).le
    have hg := bounded_AD_occupied_keys A hmu hmurho hrho1 hKp H hbox
    have hpow : rho^(-t) ≤ (r/rho)^t := by
      have hrat : 1/rho ≤ r/rho := div_le_div_of_nonneg_right hrone hrho.le
      have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/rho) hrat ht
      have hunit : (1/rho)^t=rho^(-t) := by
        rw [Real.div_rpow (by norm_num) hrho.le,Real.one_rpow,Real.rpow_neg hrho.le,one_div]
      rwa [hunit] at hh
    have hC2 : C ≤ C^2 := by nlinarith only [hC]
    have h6 : 1 ≤ (6:ℝ)^t := Real.one_le_rpow (by norm_num) ht
    have hc : ((9^d:ℕ):ℝ)*C*K^2  ≤  ((9^d:ℕ):ℝ)*C^2*K^2*(6:ℝ)^t := by
      calc
        _  ≤  ((9^d:ℕ):ℝ)*C^2*K^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC2 (Nat.cast_nonneg _)) (sq_nonneg K)
        _  ≤  _ := le_mul_of_one_le_right (by positivity) h6
    have hsub : (((B.filter (fun q => dist (center rho q) x ≤ r)).card):ℝ) ≤ (B.card:ℝ) :=
      Nat.cast_le.mpr (card_filter_le _ _)
    exact hsub.trans (hg.trans (mul_le_mul hc hpow (Real.rpow_nonneg hrho.le _) (by positivity)))

end NativeGridSupportLocal
