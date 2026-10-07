import Theorems.Thm_StickyKakeya4_native_conditional_grid_power_cost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

noncomputable section
namespace NativeConfigurationDyadicEta
open NativeCommonDirectionPhaseMenu

/-- K fixes the menu size before the source. The final existential eta is
chosen in [1/K,2/K] after the actual dyadic final-mesh depth m is known. -/
def step (m K : ℕ) : ℕ := ⌈(m:ℝ)/(K:ℝ)⌉₊
def eta (m K : ℕ) : ℝ := (step m K:ℝ)/(m:ℝ)
def depth (m K : ℕ) (j : Fin (K+1)) : ℕ := 6+min m (step m K*j.val)

lemma eta_bounds (m K : ℕ) (hK : 0< K) (hKm : K≤ m) :
    0< step m K ∧ 1/(K:ℝ)≤ eta m K ∧ eta m K≤ 2/(K:ℝ) := by
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  have hmR : (0:ℝ)<m := by exact_mod_cast (hK.trans_le hKm)
  have hKmR : (K:ℝ)≤ m := by exact_mod_cast hKm
  have hlo : (m:ℝ)/(K:ℝ)≤ step m K := Nat.le_ceil _
  have hhi : (step m K:ℝ)<(m:ℝ)/(K:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hmulLo : (m:ℝ)≤ (step m K:ℝ)*K := (div_le_iff₀ hKR).mp hlo
  have hmulHi : (step m K:ℝ)*K<(m:ℝ)+K := by
    have hh := mul_lt_mul_of_pos_right hhi hKR
    simpa only [add_mul,div_mul_cancel₀ _ hKR.ne',one_mul] using hh
  refine ⟨by exact_mod_cast ((div_pos hmR hKR).trans_le hlo),?_,?_⟩
  · exact (div_le_div_iff₀ hKR hmR).mpr (by simpa only [one_mul] using hmulLo)
  · exact (div_le_div_iff₀ hmR hKR).mpr (by linarith only [hmulHi,hKmR])

lemma mesh_eta_power (m K j : ℕ) (hm : 0< m) :
    ((2:ℝ)⁻¹^m)^(eta m K*(j:ℝ))=(2:ℝ)⁻¹^(step m K*j) := by
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have he : (-(m:ℝ))*(eta m K*(j:ℝ))= -((step m K*j:ℕ):ℝ) := by
    dsimp [eta]
    push_cast
    field_simp
  have hmu : (2:ℝ)⁻¹^m=(2:ℝ)^(-(m:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,inv_pow]
  rw [hmu,←Real.rpow_mul (by norm_num : (0:ℝ)≤2),he,
    Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,inv_pow]

/-- Every nonnegative eta-power inside [mu,1] occurs in the fixed K+1
menu, rather than in an assumed non-dyadic spatial partition. -/
lemma active_power_index (m K j : ℕ) (hK : 0< K) (hKm : K≤ m)
    (H : (2:ℝ)⁻¹^m≤ ((2:ℝ)⁻¹^m)^(eta m K*(j:ℝ))) :
    step m K*j≤ m ∧ j≤ K := by
  rw [mesh_eta_power m K j (hK.trans_le hKm)] at H
  have hj : step m K*j≤ m :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
      (by norm_num : (2:ℝ)⁻¹<1)).mp H
  have hLo := Nat.le_ceil ((m:ℝ)/(K:ℝ))
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  have hmul : m≤ step m K*K := by exact_mod_cast ((div_le_iff₀ hKR).mp hLo)
  have hstep := (eta_bounds m K hK hKm).1
  refine ⟨hj,?_⟩
  by_contra hnot
  have hKj : K+1≤ j := by omega
  have hh := Nat.mul_le_mul_left (step m K) hKj
  nlinarith only [hh,hj,hmul,hstep]

lemma depth_bounds (m K : ℕ) (j : Fin (K+1)) : 6≤ depth m K j ∧ depth m K j≤ m+6 := by
  dsimp [depth]
  omega

lemma active_depth_width (m K : ℕ) (hm : 0< m) (j : Fin (K+1))
    (hj : step m K*j.val≤ m) :
    (64:ℝ)/((2^(depth m K j):ℕ):ℝ)=((2:ℝ)⁻¹^m)^(eta m K*(j.val:ℝ)) := by
  rw [mesh_eta_power m K j.val hm,dyadic_sigma _ (depth_bounds m K j).1]
  have hd : depth m K j-6=step m K*j.val := by dsimp [depth]; omega
  rw [hd,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_pow]

end NativeConfigurationDyadicEta
