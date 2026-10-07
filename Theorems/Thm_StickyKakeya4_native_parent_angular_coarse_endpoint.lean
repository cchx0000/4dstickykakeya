import Theorems.Thm_StickyKakeya4_native_reference_parent_angular_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000

noncomputable section
namespace NativeParentAngularCoarseEndpoint
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentGeometry NativeNormalizedCellAngularMenu

/-- The genuine normalized parent slope box gives an exact finite grid
bound at every dyadic resolution. This is used only at the coarse endpoint. -/
theorem angular_image_box {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N s : ℕ) (hs : 3≤ s) (p : Parent) (E : Finset (Fin n × Index))
    (hparent : ∀z∈E,parentLabel D a N z.1=p) :
    ((E.image (fun z => angularCell D N (2^s) p z.1)).card:ℝ)≤ 
      512*(64/((2^s:ℕ):ℝ))^(-3:ℝ) := by
  let R := 2^(s-3)
  have hR : (0:ℝ)< R := by dsimp [R]; positivity
  have hpow : ((2^s:ℕ):ℝ)=8*(R:ℝ) := by
    have he : s=3+(s-3) := by omega
    calc
      _ = ((2^(3+(s-3)):ℕ):ℝ) := by rw [←he]
      _ = _ := by rw [pow_add]; norm_num [R]
  let C : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => Ico (0:ℤ) (R:ℤ))
  have hsub : E.image (fun z => angularCell D N (2^s) p z.1)⊆ C := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro j
    have hb := (parameter_box D a N p z.1 (hparent z hz)).1 j
    have hid : angularCell D N (2^s) p z.1 j=⌊(R:ℝ)*localSlope D N p z.1 j⌋ := by
      unfold angularCell
      rw [hpow]
      congr 1
      ring
    rw [hid]
    apply mem_Ico.mpr
    constructor
    · exact Int.floor_nonneg.mpr (mul_nonneg hR.le hb.1)
    · apply Int.floor_lt.mpr
      simpa only [Int.cast_natCast,mul_one] using mul_lt_mul_of_pos_left hb.2 hR
  have hC : C.card=R^3 := by
    simp [C,Fintype.card_piFinset]
  have hcount : ((E.image (fun z => angularCell D N (2^s) p z.1)).card:ℝ)≤ (R:ℝ)^3 := by
    exact_mod_cast (card_le_card hsub).trans_eq hC
  have hid : (R:ℝ)^3=512*(64/((2^s:ℕ):ℝ))^(-3:ℝ) := by
    rw [hpow,Real.rpow_neg (by positivity : (0:ℝ)≤ 64/(8*(R:ℝ))),Real.rpow_ofNat]
    field_simp
    ring
  exact hcount.trans_eq hid

theorem angular_menu_box {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m s : ℕ) (hs : 3≤ s) (p : Parent) (E : Finset (Fin n × Index))
    (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) (q : Index) :
    ((angularMenu D a m (2^s) p E q).card:ℝ)≤ 512*(64/((2^s:ℕ):ℝ))^(-3:ℝ) :=
  angular_image_box D a (2^m) s hs p _ (fun z hz => hparent z (mem_filter.mp hz).1)

/-- Failure of the relative coarse-window inequality costs only three
window powers. This is paid explicitly, rather than extending the native
relative theorem beyond its proved window. -/
theorem coarse_endpoint_cost {eps window budget kappa slack count : ℝ}
    (heps : 0< eps) (heps1 : eps≤ 1) (hk : 0≤ kappa) (hslack : 0≤ slack)
    (hbudget : 3*window≤ budget) (s : ℕ) (hs : 6≤ s)
    (hcoarse : ¬1/((2^s:ℕ):ℝ)≤ eps^window)
    (H : count≤ 512*(64/((2^s:ℕ):ℝ))^(-3:ℝ)) :
    count≤ 512*eps^(-budget)*(64/((2^s:ℕ):ℝ))^(-kappa-slack) := by
  let rho : ℝ := 64/((2^s:ℕ):ℝ)
  have hrho : 0< rho := by dsimp [rho]; positivity
  have hrho1 : rho≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (show (64:ℕ)≤ 2^s by
      simpa only [show (2:ℕ)^6=64 by norm_num] using Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hs)
  have hWindow : eps^window≤ rho := (lt_of_not_ge hcoarse).le.trans
    (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤ 64) (by positivity))
  have hp : rho^(-3:ℝ)≤ eps^(-budget) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos heps window) hWindow
      (by norm_num : (-3:ℝ)≤ 0)
    rw [←Real.rpow_mul heps.le] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_ge heps heps1 (by linarith only [hbudget]))
  have hExtra : 1≤ rho^(-kappa-slack) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hrho hrho1
    (by linarith only [hk,hslack])
  exact H.trans ((mul_le_mul_of_nonneg_left hp (by norm_num)).trans
    (le_mul_of_one_le_right (by positivity) hExtra))

end NativeParentAngularCoarseEndpoint
