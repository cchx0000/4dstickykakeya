import Theorems.Thm_StickyKakeya4_native_window_menu_interpolation
import Theorems.Thm_StickyKakeya4_native_window_interpolation_cost
import Theorems.Thm_StickyKakeya4_native_grid_center_contraction

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeWindowMiddleContraction
open Classical Finset NativeWindowXYLabels NativeWindowNesting NativeWindowRealInterpolation
open NativeWindowMenuInterpolation NativeWindowInterpolationCost NativeGridCenterContraction
open NativeWindowIntegerInterpolation NativeWindowQuotientTransport NativeReferenceXYGridPoints
open NativeSquaredGrainQueries FiniteVoronoiRealADCoarsening

/-- Every middle dyadic time window has all-radius AD after the final
fixed contraction, with one uniform explicit constant for the finite menu.
Its global count is derived from the genuine coarser prepared ancestor. -/
theorem middle_contracted_AD {k l J : ℕ} (S : Finset (XY k l))
    (m : ℕ) (hm : 6 ≤ m) (hJ : 0 < J) (hl : l ≤ 2) {K s : ℝ}
    (hK : 1 ≤ K) (hs : 0 ≤ s) (hs2 : s ≤ 2)
    (H : ∀i : Fin (J+1),∀z∈S,
      ADBounds (points S (factor m (NativeFixedHorizontalMenu.depths J m i))
        (mu m*(factor m (NativeFixedHorizontalMenu.depths J m i):ℝ)) z)
        (mu m*(factor m (NativeFixedHorizontalMenu.depths J m i):ℝ)) K s)
    (Hglobal : ∀i : Fin (J+1),∀z∈S,
      ((atPoint S (factor m (NativeFixedHorizontalMenu.depths J m i)) z).card:ℝ) ≤
        K*(windowHalfWidth m (NativeFixedHorizontalMenu.depths J m i):ℝ)^s)
    (f : ℕ) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m) (z : XY k l) (hz : z∈S) :
    let B : ℝ := ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let rho := mu m*(factor m f:ℝ)/512
    ADBounds (points S (factor m f) rho z) rho ((512:ℝ)^s*(36*K*B^2)) s ∧
      ((atPoint S (factor m f) z).card:ℝ) ≤ ((512:ℝ)^s*(36*K*B^2))*rho^(-s) := by
  intro B rho
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  obtain ⟨lo,hi,hlo,hhi,hDsB,hDbB,HAD,HG⟩ :=
    middle_window_AD S m hm hJ hKp hKp.le hs H Hglobal f hmf hfb z hz
  let fl := NativeFixedHorizontalMenu.depths J m lo
  let fh := NativeFixedHorizontalMenu.depths J m hi
  let Ds := (2:ℕ)^(fh-f)
  let Db := (2:ℕ)^(f-fl)
  let rawmu := mu m*(factor m f:ℝ)
  let Cmid := 36*K*B^2
  let Craw := NativeHalfScaleInterpolation.constant ((1/K)/(Ds:ℝ)^l)
    (upperConstant l Db K s) ((Db:ℝ)^l*K) s
  have hDs : 0 < Ds := by dsimp [Ds]; positivity
  have hDb : 0 < Db := by dsimp [Db]; positivity
  have hDb1 : (1:ℝ) ≤ Db := by exact_mod_cast hDb
  have hB1 : (1:ℝ) ≤ B := by dsimp [B]; exact_mod_cast (by positivity : 0 < (2:ℕ)^((phaseDepth m-m)/J+1))
  have hraw : 0 < rawmu := mul_pos (mu_pos m) (by unfold factor; positivity)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hmid : 0 < Cmid := by dsimp [Cmid]; positivity
  have hcost : Craw ≤ Cmid := low_dim_constant_le l Ds Db (2^((phaseDepth m-m)/J+1))
    hl hDs hDsB hDbB hK hs2
  have hCraw : 0 < Craw := lt_of_lt_of_le (by norm_num) (NativeHalfScaleInterpolation.constant_one_le _ _ _ _)
  have HADmid : ADBounds (points S (factor m f) rawmu z) rawmu Cmid s :=
    AD_mono _ hraw hCraw hcost HAD
  have hfl := NativeFixedHorizontalMenu.depths_bounds J m hm lo
  have hmult : factor m f*Db=factor m fl := by
    unfold factor
    dsimp only [Db]
    rw [←pow_add]
    congr 1
    omega
  have hNprod : rawmu*(windowHalfWidth m fl:ℝ) ≤ 1/2 := by
    have hscale := window_mesh_halfWidth m fl hm hfl.1 hfl.2
    have hmesh : rawmu*(Db:ℝ)=mu m*(factor m fl:ℝ) := by
      dsimp [rawmu]
      rw [mul_assoc,←Nat.cast_mul,hmult]
    calc
      _ ≤ (rawmu*(Db:ℝ))*(windowHalfWidth m fl:ℝ) :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hraw.le hDb1) (Nat.cast_nonneg _)
      _ = 1/2 := by rw [hmesh]; exact hscale
  have hNcap : (windowHalfWidth m fl:ℝ) ≤ 1/rawmu :=
    (le_div_iff₀ hraw).mpr (by nlinarith only [hNprod])
  have hpower := Real.rpow_le_rpow (Nat.cast_nonneg (windowHalfWidth m fl)) hNcap hs
  have hunit : (1/rawmu)^s=rawmu^(-s) := by
    rw [Real.div_rpow (by norm_num) hraw.le,Real.one_rpow,Real.rpow_neg hraw.le,one_div]
  rw [hunit] at hpower
  have hDbpow : (Db:ℝ)^l ≤ B^2 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg Db) (Nat.cast_le.mpr hDbB) l).trans
      (pow_le_pow_right₀ hB1 hl)
  have hGmid : (Db:ℝ)^l*K ≤ Cmid := by
    have hh := mul_le_mul_of_nonneg_right hDbpow hKp.le
    dsimp [Cmid]
    have hKB : 0 ≤ K*B^2 := mul_nonneg hKp.le (sq_nonneg _)
    nlinarith only [hh,hKB]
  have HGmid : ((atPoint S (factor m f) z).card:ℝ) ≤ Cmid*rawmu^(-s) := by
    calc
      _ ≤ (Db:ℝ)^l*K*(windowHalfWidth m fl:ℝ)^s := HG
      _ ≤ (Db:ℝ)^l*K*rawmu^(-s) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hGmid (by positivity)
  have hraw1 : rawmu ≤ 1 := by
    have hscale := window_mesh_halfWidth m f hm hmf hfb
    have hn : (1:ℝ) ≤ windowHalfWidth m f := by
      unfold windowHalfWidth
      exact_mod_cast (by positivity : 0 < (2:ℕ)^(f-m+5))
    have hh := le_mul_of_one_le_right hraw.le hn
    change rawmu*(windowHalfWidth m f:ℝ)=1/2 at hscale
    linarith only [hscale,hh]
  have HH := contracted_grid_AD (atPoint S (factor m f) z) hraw hraw1
    (by norm_num : (1:ℝ) ≤ 512) hmid hs HADmid HGmid
  refine ⟨by simpa only [max_self] using HH,?_⟩
  have hsmall : rho ≤ rawmu := by dsimp [rho,rawmu]; exact div_le_self (by positivity) (by norm_num)
  have hp := Real.rpow_le_rpow_of_nonpos hrho hsmall (neg_nonpos.mpr hs)
  have hc : Cmid ≤ (512:ℝ)^s*Cmid :=
    le_mul_of_one_le_left hmid.le (Real.one_le_rpow (by norm_num) hs)
  exact HGmid.trans ((mul_le_mul_of_nonneg_left hp hmid.le).trans
    (mul_le_mul_of_nonneg_right hc (by positivity)))

end NativeWindowMiddleContraction
