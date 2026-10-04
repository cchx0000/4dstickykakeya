import Theorems.Thm_StickyKakeya4_native_planar_abc_input
import Theorems.Thm_StickyKakeya4_original_angular_exponent_range
import Theorems.Thm_StickyKakeya4_native_quarter_balanced_mesh
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeABCOriginalLossBudget
open Classical FinitePlaneProjectionGrid FinitePlaneProjectionGraph
/-- Exact original KT, scale-menu, and inverse-density losses yield a
 fourth-power bound for the actual graph-aware projection threshold. -/
theorem graphLoss_le_fourth (J : ℕ) (rho : ℝ) {K beta T : ℝ}
    (hT : 6168 ≤ T) (hK0 : 0 ≤ K) (hb : 0 < beta)
    (hK : K ≤ T) (hN : ((dyadicScales J rho).card:ℝ) ≤ T) (hbInv : beta⁻¹ ≤ T) :
    graphLoss J rho K beta ≤ T^4 := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  unfold graphLoss allscaleLoss
  calc
    _ = 6168*K*((dyadicScales J rho).card:ℝ)*beta⁻¹ := by ring
    _ ≤ T*T*T*T := by gcongr
    _ = T^4 := by ring
/-- The actual graph quotient/color loss is bounded using BOTH original
 vertex KT constants; the density dependence is kept explicit. -/
theorem graphMassLoss_le_ninth (J : ℕ) (rho : ℝ) {KP KB beta T : ℝ}
    (hT : 6168 ≤ T) (hKP0 : 0 < KP) (hKB0 : 0 < KB) (hb : 0 < beta)
    (hKP : KP ≤ T) (hKB : KB ≤ T)
    (hN : ((dyadicScales J rho).card:ℝ) ≤ T) (hbInv : beta⁻¹ ≤ T) :
    graphMassLoss J rho KP KB beta ≤ T^9 := by
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hP := graphLoss_le_fourth J rho hT hKP0.le hb hKP hN hbInv
  have hB := graphLoss_le_fourth J rho hT hKB0.le hb hKB hN hbInv
  have h108 : (108:ℝ) ≤ T := by linarith only [hT]
  have hBP := (graphLoss_pos J rho hKB0 hb).le
  have hPP := (graphLoss_pos J rho hKP0 hb).le
  unfold graphMassLoss
  calc
    _ ≤ T*T^4*T^4 := by gcongr
    _ = T^9 := by ring
/-- Every output constant is bounded from ONE budget on the ORIGINAL
 spatial/angle populations, original graph density, original B lower mass,
 actual old-target error ratio, and the constructed finite scale menu. -/
theorem actual_constructor_loss_budget (J : ℕ) (rho : ℝ)
    {KP KB beta lambda angularK angleRatio exponent errorRatio T : ℝ}
    (hT : 6168 ≤ T) (hKP0 : 0 < KP) (hKB0 : 0 < KB) (hb : 0 < beta) (hlambda : 0 < lambda)
    (hKP : KP ≤ T) (hKB : KB ≤ T) (hN : ((dyadicScales J rho).card:ℝ) ≤ T)
    (hbInv : beta⁻¹ ≤ T) (hlambdaInv : lambda⁻¹ ≤ T)
    (hAng0 : 0 ≤ angularK) (hAng : angularK ≤ T)
    (hRatio1 : 1 ≤ angleRatio) (hRatio : angleRatio ≤ T) (hExponent : exponent ≤ 2)
    (hError0 : 0 ≤ errorRatio) (hError : errorRatio ≤ T) :
    let L := graphMassLoss J rho KP KB beta
    L/beta ≤ T^10 ∧ (T^10)⁻¹ ≤ beta/L ∧
      400*graphLoss J rho KB beta*L/(beta*lambda) ≤ T^16 ∧
      (2:ℝ)^exponent*((2:ℝ)^exponent*angularK^2*angleRatio^exponent) ≤ T^5 ∧
      (L/beta)*(4*errorRatio+8)^2 ≤ T^14 := by
  let L := graphMassLoss J rho KP KB beta
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hTpos : 0 < T := by linarith only [hT]
  have hL : 0 < L := graphMassLoss_pos J rho hKP0 hKB0 hb
  have hLcap : L ≤ T^9 := graphMassLoss_le_ninth J rho hT hKP0 hKB0 hb hKP hKB hN hbInv
  have hDcap := graphLoss_le_fourth J rho hT hKB0.le hb hKB hN hbInv
  have hD0 := (graphLoss_pos J rho hKB0 hb).le
  have hrate : L/beta ≤ T^10 := by
    calc
      _ = L*beta⁻¹ := div_eq_mul_inv _ _
      _ ≤ T^9*T := mul_le_mul hLcap hbInv (inv_nonneg.mpr hb.le) (by positivity)
      _ = T^10 := by ring
  have hinv : (T^10)⁻¹ ≤ beta/L := by
    have hh := (inv_le_inv₀ (by positivity : (0:ℝ)<T^10) (div_pos hL hb)).mpr hrate
    simpa only [inv_div] using hh
  have h400 : (400:ℝ) ≤ T := by linarith only [hT]
  have hBcost : 400*graphLoss J rho KB beta*L/(beta*lambda) ≤ T^16 := by
    calc
      _ = 400*graphLoss J rho KB beta*(L/beta)*lambda⁻¹ := by ring
      _ ≤ T*T^4*T^10*T := by gcongr
      _ = T^16 := by ring
  have h16 : (16:ℝ) ≤ T := by linarith only [hT]
  have hCcost : (2:ℝ)^exponent*((2:ℝ)^exponent*angularK^2*angleRatio^exponent) ≤ T^5 := by
    calc
      _ ≤ 16*angularK^2*angleRatio^2 := OriginalAngularExponentRange.uniform_angular_mesh_cost hRatio1 hExponent
      _ ≤ T*T^2*T^2 := by gcongr
      _ = T^5 := by ring
  have hE : 4*errorRatio+8 ≤ T^2 := by nlinarith only [hError,hT]
  have hE0 : 0 ≤ 4*errorRatio+8 := by positivity
  have hCover : (L/beta)*(4*errorRatio+8)^2 ≤ T^14 := by
    calc
      _ ≤ T^10*(T^2)^2 := mul_le_mul hrate (pow_le_pow_left₀ hE0 hE 2) (sq_nonneg _) (by positivity)
      _ = T^14 := by ring
  exact ⟨hrate,hinv,hBcost,hCcost,hCover⟩
/-- With the proved quarter-mesh relation, a sixteenth-power ORIGINAL
 budget delta^-a is a native ABC budget with exponent 64a. -/
theorem native_sixteenth_budget {delta mu a : ℝ}
    (hd : 0 < delta) (hmu : 0 < mu) (hmesh : mu ≤ NativeQuarterScaleParameters.quarterScale delta)
    (ha : 0 ≤ a) :
    (delta^(-a))^16 ≤ mu^(-64*a) ∧ mu^(64*a) ≤ ((delta^(-a))^16)⁻¹ := by
  have hh := NativeQuarterBalancedMesh.native_power_loss hd hmu hmesh (show 0 ≤ 16*a by positivity)
  have hid : (delta^(-a))^16=delta^(-(16*a)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hd.le]
    congr 1
    norm_num
    ring
  have hexp : (-4:ℝ)*(16*a) = -64*a := by ring
  have hexp' : 4*(16*a)=64*a := by ring
  rw [hid]
  constructor
  · simpa only [hexp] using hh.2
  · rw [Real.rpow_neg hd.le,inv_inv]
    simpa only [hexp'] using hh.1
end NativeABCOriginalLossBudget
