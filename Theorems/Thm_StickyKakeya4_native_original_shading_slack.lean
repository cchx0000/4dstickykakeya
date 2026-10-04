import Theorems.Thm_StickyKakeya4_original_source_log_budgets
import Theorems.Thm_StickyKakeya4_original_shading_center_profile
import Theorems.Thm_StickyKakeya4_original_shading_grid_geometry
import Theorems.Thm_StickyKakeya4_original_clipped_unit_tube
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeOriginalShadingSlack
open Classical OriginalPairStripGeometry PlanarFrostmanBallConversion OriginalSourceLogBudgets
open OriginalPhysicalTubeScaleSelection DyadicOriginalFiberSelection OriginalShadingCenterProfile
open OriginalShadingGridGeometry

/-- The coefficient produced by the actual original-to-coarse shading
selection, after taking the radius power outside the coefficient. -/
def coarseCoefficient (Pts : Finset Point) (n : ℕ)
    (delta eta' a b : ℝ) : ℝ :=
  18*(levelCount Pts : ℝ)*(8*shadingCoefficient n delta eta' (delta^(2*eta'/a)))*2^b

/-- This estimate retains the actual source occupancy and scale-menu
factors; the power loss is exactly eta'*(1+4/a). -/
theorem original_coarse_coefficient_bound (Pts : Finset Point) (n : ℕ)
    (delta eta' a b : ℝ) (hd : 0<delta) (hb : b≤1) :
    coarseCoefficient Pts n delta eta' a b≤
      288*((n:ℝ)+5)*(levelCount Pts : ℝ)*delta^(-(eta'*(1+4/a))) := by
  have htwo : (2:ℝ)^b≤2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hb
  have hid : delta^(-eta')/(delta^(2*eta'/a))^2=delta^(-(eta'*(1+4/a))) := by
    rw [← Real.rpow_mul_natCast hd.le (2*eta'/a) 2,← Real.rpow_sub hd]
    congr 1
    ring
  unfold coarseCoefficient shadingCoefficient
  calc
    _ ≤ 18*(levelCount Pts : ℝ)*(8*(((n:ℝ)+5)*delta^(-eta')/(delta^(2*eta'/a))^2))*2 :=
      mul_le_mul_of_nonneg_left htwo (by positivity)
    _ = 288*((n:ℝ)+5)*(levelCount Pts : ℝ)*(delta^(-eta')/(delta^(2*eta'/a))^2) := by ring
    _ = _ := by rw [hid]

/-- A fixed target shading loss determines the internal-eta ceiling before
mesh and source selection. The cutoff is uniform in every etaI below that
ceiling. Only the original bounded square, Euclidean separation and actual
rho power decay pay the logarithmic and fixed constants. -/
theorem exists_original_coarse_shading_slack (t a kappa e : ℝ)
    (ht : 0<t) (ha : 0<a) (hkappa : 0<kappa) (he : 0<e) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ etaI : ℝ, 0≤etaI → etaI≤kappa*e/(4*(4+12/t)*(1+4/a)) →
      ∀ delta : ℝ, 0<delta → delta≤delta0 → ∀ n : ℕ,
        delta≤dyadicRadius n → dyadicRadius n≤2*delta →
        ∀ Pts : Finset Point,
          (∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1) →
          (∀ x∈Pts, ∀ y∈Pts, x≠y → delta≤euclideanDistance x y) →
          ∀ rho : ℝ, delta≤rho → rho≤delta^kappa → ∀ b : ℝ, b≤1 →
            coarseCoefficient Pts n delta ((4+12/t)*etaI) a b≤(3*rho)^(-e) := by
  have hC : 0<4+12/t := by positivity
  have hA : 0<1+4/a := by positivity
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_original_logarithmic_power_cutoff
    (288*3^e) (by positivity) 1 1 (kappa*e/2) (by positivity)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro etaI hI hIupper delta hd hsmall n hmesh hbottom Pts hbox hsep rho hquery hdecay b hb
  have hd1 : delta≤1 := hsmall.trans hd01
  have hrho : 0<rho := hd.trans_le hquery
  have hr : 0<3*rho := by positivity
  let E := ((4+12/t)*etaI)*(1+4/a)
  have hE : E≤kappa*e/4 := by
    have hh := (le_div_iff₀ (show 0<4*(4+12/t)*(1+4/a) by positivity)).mp hIupper
    dsimp [E]
    nlinarith only [hh]
  have hpower : delta^(-E)*(3*rho)^e≤3^e*delta^(kappa*e/2) := by
    have hrpow : (3*rho)^e≤3^e*delta^(kappa*e) := by
      have hh := Real.rpow_le_rpow hr.le
        (mul_le_mul_of_nonneg_left hdecay (by norm_num : (0:ℝ)≤3)) he.le
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) (Real.rpow_nonneg hd.le kappa),
        ← Real.rpow_mul hd.le] at hh
      exact hh
    have hexp : kappa*e/2≤-E+kappa*e := by
      have hke : 0<kappa*e := mul_pos hkappa he
      linarith only [hE,hke]
    have hdp := Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp
    calc
      _ ≤ delta^(-E)*(3^e*delta^(kappa*e)) :=
        mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg hd.le (-E))
      _ = 3^e*delta^(-E+kappa*e) := by rw [Real.rpow_add hd]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdp (by positivity)
  have hcoeff := original_coarse_coefficient_bound Pts n delta ((4+12/t)*etaI) a b hd hb
  have hpoly : 0≤288*((n:ℝ)+5)*(levelCount Pts : ℝ) := by positivity
  have hbudget := hcut delta hd hsmall n hmesh hbottom Pts hbox hsep
  simp only [pow_one] at hbudget
  have hproduct : coarseCoefficient Pts n delta ((4+12/t)*etaI) a b*(3*rho)^e≤1 := by
    have hh := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hr.le e)
    have hh' := mul_le_mul_of_nonneg_left hpower hpoly
    dsimp [E] at hh'
    nlinarith only [hh,hh',hbudget]
  rw [Real.rpow_neg hr.le,← one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hr e)).mpr hproduct

/-- The actual box profile supplied by coarse selection therefore has the
fixed requested coefficient at the physical width 3rho. -/
theorem original_coarse_profile_with_slack
    (Pts R : Finset Point) (n : ℕ) (delta eta' a b rho e : ℝ)
    (hcoeff : coarseCoefficient Pts n delta eta' a b≤(3*rho)^(-e))
    (hrho : 0<rho)
    (hprofile : ∀ (x : Point) (r : ℝ), 3*rho≤r →
      ((R.filter (fun p => InBox (OriginalClippedUnitTube.halfPoint p) x r)).card : ℝ)≤
        18*(levelCount Pts : ℝ)*
          ((8*shadingCoefficient n delta eta' (delta^(2*eta'/a)))*(2*r)^b)*R.card) :
    ∀ (x : Point) (r : ℝ), 3*rho≤r →
      ((R.filter (fun p => InBox (OriginalClippedUnitTube.halfPoint p) x r)).card : ℝ)≤
        (3*rho)^(-e)*r^b*R.card := by
  intro x r hr
  have hrpos : 0<r := (show 0<3*rho by positivity).trans_le hr
  have hh := hprofile x r hr
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hrpos.le] at hh
  have heq : 18*(levelCount Pts : ℝ)*
      ((8*shadingCoefficient n delta eta' (delta^(2*eta'/a)))*(2^b*r^b))*R.card=
      coarseCoefficient Pts n delta eta' a b*r^b*R.card := by
    unfold coarseCoefficient
    ring
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hrpos.le b)) (Nat.cast_nonneg R.card))

end NativeOriginalShadingSlack
