import Theorems.Thm_StickyKakeya4_native_pair_scale_budget
import Theorems.Thm_StickyKakeya4_native_local_menu_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeTwoAxisPowerInterpolation

/-- The extremal relative power written in exact dyadic depth coordinates. -/
def depthPower (kappa : ℝ) (m f : ℕ) : ℝ :=
  (2:ℝ)^(((f:ℝ)-(m:ℝ))*kappa)

lemma depthPower_pos (kappa : ℝ) (m f : ℕ) : 0 < depthPower kappa m f := by
  unfold depthPower
  positivity

lemma depthPower_eq_relative (kappa : ℝ) (m f : ℕ) :
    depthPower kappa m f = ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa) := by
  have he : (64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)) =
      (2:ℝ)^((m:ℝ)-(f:ℝ)) := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_natCast,Real.rpow_natCast]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  rw [he,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  unfold depthPower
  congr 1
  ring

lemma depthPower_eq_nat {m f : ℕ} (hmf : m ≤ f) (kappa : ℝ) :
    depthPower kappa m f = ((2^(f-m):ℕ):ℝ)^kappa := by
  rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  unfold depthPower
  rw [Nat.cast_sub hmf]

lemma delta_power {delta : ℝ} {level : ℕ} (hdy : delta=(2:ℝ)⁻¹^level) (x : ℝ) :
    delta^x=(2:ℝ)^(-(level:ℝ)*x) := by
  have hd : delta=(2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  rw [hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- Replacing the outer parent by a nearby scheduled ancestor costs only
its depth gap; replacing the inner projection by a predecessor helps. -/
lemma upper_menu_power {delta s kappa : ℝ} {level c m b f : ℕ}
    (hdy : delta=(2:ℝ)⁻¹^level) (hk : 0 ≤ kappa) (hcm : c ≤ m) (hbf : b ≤ f)
    (hgap : ((m-c:ℕ):ℝ) ≤ s*level) :
    depthPower kappa c b ≤ delta^(-s*kappa)*depthPower kappa m f := by
  rw [Nat.cast_sub hcm] at hgap
  rw [delta_power hdy,depthPower,depthPower,←Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have hbfR : (b:ℝ) ≤ f := by exact_mod_cast hbf
  nlinarith

/-- The two nearby scheduled depths together cost at most two mesh gaps in
the lower extremal relative power. -/
lemma lower_menu_power {delta s kappa : ℝ} {level m d b f : ℕ}
    (hdy : delta=(2:ℝ)⁻¹^level) (hk : 0 ≤ kappa) (hmd : m ≤ d) (hbf : b ≤ f)
    (hgapD : ((d-m:ℕ):ℝ) ≤ s*level) (hgapF : ((f-b:ℕ):ℝ) ≤ s*level) :
    delta^(2*s*kappa)*depthPower kappa m f ≤ depthPower kappa d b := by
  rw [Nat.cast_sub hmd] at hgapD
  rw [Nat.cast_sub hbf] at hgapF
  rw [delta_power hdy,depthPower,depthPower,←Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  nlinarith

lemma nat_power_cost {delta s r : ℝ} (hd : 0 < delta) (hr : 0 ≤ r)
    (hgap : r ≤ delta^(-s)) (k : ℕ) : r^k ≤ delta^(-s*(k:ℝ)) := by
  have hh := pow_le_pow_left₀ hr hgap k
  rw [←Real.rpow_natCast (delta^(-s)) k,←Real.rpow_mul hd.le] at hh
  exact hh

/-- Upper interpolation on both axes, with the actual geometric coefficient
and the scheduled outer-parent subset loss already combined in C. -/
theorem upper_transfer {delta s kappa loss C r menuPower targetPower Mmenu M : ℝ}
    (hd : 0 < delta) (hr : 0 ≤ r) (hgap : r ≤ delta^(-s))
    (hC : 0 ≤ C) (hcost : C ≤ delta^(-loss)) (hP : 0 ≤ targetPower)
    (hpower : menuPower ≤ delta^(-s*kappa)*targetPower)
    (hmenu : Mmenu ≤ delta^(-loss)*menuPower)
    (htransfer : M ≤ C*r^10*Mmenu) :
    M ≤ delta^(-(2*loss+s*(10+kappa)))*targetPower := by
  have hrpow := nat_power_cost hd hr hgap 10
  have hmenu' : Mmenu ≤ delta^(-(loss+s*kappa))*targetPower := by
    calc
      _ ≤ delta^(-loss)*menuPower := hmenu
      _ ≤ delta^(-loss)*(delta^(-s*kappa)*targetPower) :=
        mul_le_mul_of_nonneg_left hpower (Real.rpow_pos_of_pos hd _).le
      _ = _ := by rw [←mul_assoc,←Real.rpow_add hd]; congr 2; ring
  calc
    _ ≤ C*r^10*Mmenu := htransfer
    _ ≤ C*r^10*(delta^(-(loss+s*kappa))*targetPower) :=
      mul_le_mul_of_nonneg_left hmenu' (mul_nonneg hC (pow_nonneg hr 10))
    _ ≤ (delta^(-loss)*delta^(-s*(10:ℝ)))*(delta^(-(loss+s*kappa))*targetPower) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hcost hrpow (pow_nonneg hr 10) (Real.rpow_pos_of_pos hd _).le)
        (mul_nonneg (Real.rpow_pos_of_pos hd _).le hP)
    _ = _ := by rw [mul_assoc,←mul_assoc (delta^(-s*(10:ℝ))),←Real.rpow_add hd,
      ←mul_assoc,←Real.rpow_add hd]; congr 2; ring

/-- Lower interpolation uses the physical forward estimate and the exact
outer-parent partition. Both mesh gaps are paid explicitly. -/
theorem lower_transfer {delta s kappa loss C r menuPower targetPower Mmenu M : ℝ}
    (hd : 0 < delta) (hr : 0 ≤ r) (hgap : r ≤ delta^(-s))
    (hcost : C ≤ delta^(-loss)) (hM : 0 ≤ M)
    (hpower : delta^(2*s*kappa)*targetPower ≤ menuPower)
    (hmenu : delta^loss*menuPower ≤ Mmenu)
    (htransfer : Mmenu ≤ C*r^4*M) :
    delta^(2*loss+s*(4+2*kappa))*targetPower ≤ M := by
  have hrpow := nat_power_cost hd hr hgap 4
  have hcross : delta^(loss+2*s*kappa)*targetPower ≤ C*r^4*M := by
    calc
      _ = delta^loss*(delta^(2*s*kappa)*targetPower) := by rw [Real.rpow_add hd]; ring
      _ ≤ delta^loss*menuPower :=
        mul_le_mul_of_nonneg_left hpower (Real.rpow_pos_of_pos hd _).le
      _ ≤ _ := hmenu.trans htransfer
  have hcoefficient : C*r^4 ≤ delta^(-(loss+4*s)) := by
    calc
      _ ≤ delta^(-loss)*delta^(-s*(4:ℝ)) :=
        mul_le_mul hcost hrpow (pow_nonneg hr 4) (Real.rpow_pos_of_pos hd _).le
      _ = _ := by rw [←Real.rpow_add hd]; congr 1; ring
  have hh := NativeSameSourceBalanceAbsorption.absorb_balance_cost
    (power:=loss+2*s*kappa) (loss:=loss+4*s) (X:=targetPower) hd hM hcross hcoefficient
  simpa only [show loss+2*s*kappa+(loss+4*s)=2*loss+s*(4+2*kappa) by ring] using hh

end NativeTwoAxisPowerInterpolation
