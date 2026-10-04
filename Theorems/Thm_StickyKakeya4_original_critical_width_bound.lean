import Theorems.Thm_StickyKakeya4_original_line_representative_charge
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000

noncomputable section
namespace OriginalCriticalWidthBound
open Classical OriginalPairStripGeometry NativeRadialClassPruning OriginalUnitLineGrid
open OriginalLineRepresentativeCharge

def criticalWidth (rho : ℝ) (S : Finset Pair) : ℝ :=
  3*rho*Real.sqrt (S.card : ℝ)

/-- The genuine original-pair family charge and original densest gain
control the actual critical width of the minimally thickened family.
No critical-width upper certificate or A.3 gain is an input. -/
theorem original_family_critical_width_bound
    (Pts : Finset Point) (G S : Finset Pair) (delta rho tau m gap sigma : ℝ)
    (hd : 0<delta) (hrho : 0<rho) (htau : 0<tau) (hm : 0 < m) (hsigma : sigma≤1)
    (hS : S⊆G) (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair))
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hrich : ∀ z∈G,
      tau^2*m≤((G.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      tau^2*m≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ))
    (hgain : delta^(-gap)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m) :
    criticalWidth rho S≤288*delta^gap*rho^(1-sigma)/tau^2 := by
  let k := tau^2*m/2
  have hk : 0≤k := by dsimp [k]; positivity
  have hclasses : ∀ z∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ) := by
    intro z hz
    have he : 2*k=tau^2*m := by dsimp [k]; ring
    rw [he]
    exact hrich z hz
  have hcharge := original_representative_pair_charge Pts G S rho k hrho hk hS hinj
    hGP hbox hdistinct hclasses
  have hGcard : (G.card : ℝ)≤(Pts.card : ℝ)^2 := by
    have hh := Finset.card_le_card hGP
    simp only [Finset.product_eq_sprod,Finset.card_product] at hh
    rw [pow_two]
    exact_mod_cast hh
  have hcharge' : (tau^2*m)^2*(S.card : ℝ)≤539*(Pts.card : ℝ)^2 := by
    dsimp [k] at hcharge
    nlinarith only [hcharge,hGcard]
  have hsqrt : 0≤Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
  have hroot : tau^2*m*Real.sqrt (S.card : ℝ)≤24*(Pts.card : ℝ) := by
    have hsq : (tau^2*m*Real.sqrt (S.card : ℝ))^2≤(24*(Pts.card : ℝ))^2 := by
      rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg S.card)]
      nlinarith only [hcharge',sq_nonneg (Pts.card : ℝ)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  let F := delta^gap*rho^(-sigma)
  have hF : 0<F := by dsimp [F]; positivity
  have hid : F*(delta^(-gap)*rho^sigma)=1 := by
    dsimp [F]
    calc
      _ = (delta^gap*delta^(-gap))*(rho^(-sigma)*rho^sigma) := by ring
      _ = 1 := by rw [← Real.rpow_add hd,← Real.rpow_add hrho]; simp
  have hgain' := mul_le_mul_of_nonneg_left hgain hF.le
  rw [← mul_assoc,hid,one_mul] at hgain'
  have htwo : (2:ℝ)^(sigma+1)≤4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show sigma+1≤2 by linarith only [hsigma])
    norm_num only [Real.rpow_two,show (2:ℝ)^2=4 by norm_num] at hh
    exact hh
  have hpopulation : (Pts.card : ℝ)≤4*F*m := by
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htwo hm.le) hF.le
    nlinarith only [hgain',hh]
  have hroot' : tau^2*Real.sqrt (S.card : ℝ)≤96*F := by
    apply (mul_le_mul_iff_of_pos_right hm).mp
    nlinarith only [hroot,hpopulation]
  have hwidth : criticalWidth rho S*tau^2≤288*rho*F := by
    have hh := mul_le_mul_of_nonneg_left hroot' (show 0≤3*rho by positivity)
    dsimp [criticalWidth]
    nlinarith only [hh]
  have hfactor : rho*F=delta^gap*rho^(1-sigma) := by
    dsimp [F]
    calc
      _ = delta^gap*(rho^(1:ℝ)*rho^(-sigma)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hrho]; congr 2
  rw [show 288*rho*F=288*(rho*F) by ring,hfactor] at hwidth
  exact (le_div_iff₀ (sq_pos_of_pos htau)).mpr (by nlinarith only [hwidth])

/-- Substitute the actual annular exclusion scale. The exponent margin
is explicit and must be made positive before choosing the small scale. -/
theorem original_family_native_critical_width_bound
    (Pts : Finset Point) (G S : Finset Pair) (delta rho eta' a gap sigma : ℝ)
    (hd : 0<delta) (hrho : 0<rho) (hrho1 : rho≤1) (_ha : 0<a)
    (hsigma : sigma≤1) (m : ℝ) (hm : 0 < m)
    (hS : S⊆G) (hinj : Set.InjOn (lineCell rho) (↑S : Set Pair))
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ z∈G, z.1≠z.2)
    (hrich : ∀ z∈G,
      (delta^(2*eta'/a))^2*m≤((G.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
      (delta^(2*eta'/a))^2*m≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ))
    (hgain : delta^(-gap)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m) :
    criticalWidth rho S≤288*delta^(gap-4*eta'/a) := by
  have htau : 0<delta^(2*eta'/a) := Real.rpow_pos_of_pos hd _
  have hh := original_family_critical_width_bound Pts G S delta rho (delta^(2*eta'/a)) m gap sigma
    hd hrho htau hm hsigma hS hinj hGP hbox hdistinct hrich hgain
  have hpow : rho^(1-sigma)≤1 := Real.rpow_le_one hrho.le hrho1 (by linarith only [hsigma])
  have hproduct : 288*delta^gap*rho^(1-sigma)/(delta^(2*eta'/a))^2≤
      288*delta^gap/(delta^(2*eta'/a))^2 :=
    div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have hid : delta^gap/(delta^(2*eta'/a))^2=delta^(gap-4*eta'/a) := by
    rw [← Real.rpow_mul_natCast hd.le (2*eta'/a) 2,← Real.rpow_sub hd]
    congr 1
    norm_num
    ring
  calc
    _ ≤ 288*delta^gap/(delta^(2*eta'/a))^2 := hh.trans hproduct
    _ = _ := by rw [mul_div_assoc,hid]

end OriginalCriticalWidthBound
