import Theorems.Thm_StickyKakeya4_native_saturated_all_mesh_lower
import Theorems.Thm_StickyKakeya4_native_paid_mesh_angular_bounds
import Theorems.Thm_StickyKakeya4_native_fixed_coherence_cost
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5500000
noncomputable section
namespace NativeSourceCoherenceCost
open Classical Finset NativeActivePhasePopulation NativePaidMeshAngularUpper
open NativeFixedCompactKakeyaExponent NativeFixedCoherenceCost
open scoped BigOperators

def roundConstant (g ell : ℕ) : ℝ :=
  (4:ℝ)^(4-ell)*meshAngularConstant*(2744*rowConstant*((g:ℝ)+1))

def cost {K : ℕ} (g ell : ℕ) (r loss etaRank : ℝ) (depths : Fin K → ℕ) : ℕ :=
  ∏u,⌈((4:ℝ)^(4-ell)*(meshAngularConstant*r^(-loss)*(64/((2^(depths u):ℕ):ℝ))^(-extremalExponent)))/
    ((64/((2^(depths u):ℕ):ℝ))^(-extremalExponent)/
      ((2744*rowConstant*((g:ℝ)+1))*r^(-(9*etaRank))))⌉₊

lemma radius_cancel (g ell : ℕ) {r rho loss etaRank : ℝ} (hr : 0 < r) (hrho : 0 < rho) :
    ((4:ℝ)^(4-ell)*(meshAngularConstant*r^(-loss)*rho^(-extremalExponent)))/
      (rho^(-extremalExponent)/((2744*rowConstant*((g:ℝ)+1))*r^(-(9*etaRank))))=
      roundConstant g ell*r^(-(loss+9*etaRank)) := by
  have hRho : rho^(-extremalExponent)≠0 := (Real.rpow_pos_of_pos hrho _).ne'
  calc
    _ = roundConstant g ell*(r^(-loss)*r^(-(9*etaRank))) := by
      unfold roundConstant
      field_simp
    _ = _ := by rw [←Real.rpow_add hr]; congr 2; ring

/-- Only the fixed number of coherence rounds enters the exponent. The
actual spatial/angular mesh cancels from each ceiling ratio. -/
theorem cost_le_power {K : ℕ} (g ell : ℕ) (depths : Fin K → ℕ)
    {r loss etaRank : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hloss : 0 ≤ loss) (heta : 0 ≤ etaRank) :
    (cost g ell r loss etaRank depths:ℝ) ≤
      (2*max 1 (roundConstant g ell))^K*r^(-((K:ℝ)*(loss+9*etaRank))) := by
  let A := roundConstant g ell
  let nu := loss+9*etaRank
  let a : Fin K → ℝ := fun _ => A*r^(-nu)
  have hcost : cost g ell r loss etaRank depths=∏u : Fin K,⌈a u⌉₊ := by
    unfold cost
    apply prod_congr rfl
    intro u _hu
    rw [radius_cancel g ell hr (by positivity)]
  have hceil : ((∏u : Fin K,⌈a u⌉₊:ℕ):ℝ) ≤ ((∏u : Fin K,⌈max 1 (a u)⌉₊:ℕ):ℝ) := by
    exact_mod_cast prod_le_prod (fun _ _ => Nat.zero_le _) (fun u _ => Nat.ceil_mono (le_max_right _ _))
  have hPower : 1 ≤ r^(-nu) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1
    (by dsimp [nu]; linarith only [hloss,heta])
  have hmax (u : Fin K) : max 1 (a u) ≤ max 1 A*r^(-nu) := by
    apply max_le
    · have hA : 1 ≤ max 1 A := le_max_left _ _
      nlinarith only [hA,hPower]
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)
  rw [hcost]
  exact hceil.trans (fixed_round_power_cost K (fun u => max 1 (a u)) hr
    (fun _ => le_max_left _ _) hmax)

end NativeSourceCoherenceCost
