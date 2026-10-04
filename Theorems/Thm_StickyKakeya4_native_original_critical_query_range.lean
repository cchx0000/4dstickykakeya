import Theorems.Thm_StickyKakeya4_original_critical_width_bound
import Theorems.Thm_StickyKakeya4_native_original_shading_width_cutoff
import Theorems.Thm_StickyKakeya4_original_thickening_color_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeOriginalCriticalQueryRange
open OriginalPairStripGeometry NativeRadialClassPruning OriginalUnitLineGrid
open OriginalCriticalWidthBound NativeQuarterScaleParameters OriginalThickeningColorBudget

/-- The concrete minimal physical thickening uses a fixed residue modulus. -/
theorem minimal_thickening_modulus (rho : ℝ) (hrho : 0<rho) :
    thickeningModulus rho (3*rho)=110 := by
  unfold thickeningModulus
  have he : 36*(3*rho)/rho=108 := by field_simp; norm_num
  rw [he]
  norm_num

/-- A nonempty actual family has critical width above its original mesh. -/
theorem original_critical_width_ge_base (rho : ℝ) (S : Finset Pair)
    (hrho : 0<rho) (hS : S.Nonempty) : 3*rho≤criticalWidth rho S := by
  have hcard : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hroot : 1≤Real.sqrt (S.card : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hcard
  exact (by simpa only [criticalWidth,mul_one] using
    mul_le_mul_of_nonneg_left hroot (show 0≤3*rho by positivity))

/-- The actual A.1 parameter order leaves a strict gap above the A.2
query exponent. This is stronger than only eta'+eta≤zeta-gamma. -/
theorem original_A1_critical_exponent_margin
    (zeta gamma a eta' eps1 : ℝ) (hzeta : 0<zeta) (ha : 0<a)
    (hgamma : gamma≤zeta/100) (heps : eps1≤zeta/8) (heta' : eta'≤a*zeta/32) :
    4*eps1<(zeta-gamma)-4*eta'/a := by
  have htax : 4*eta'/a≤zeta/8 := (div_le_iff₀ ha).mpr (by nlinarith only [heta'])
  linarith only [hgamma,heps,htax,hzeta]

/-- At an actual positive cutoff, the critical external-strip query is
legal both for the original dense profile and for the fixed-dilation
A.2 radial cap. The critical width is derived from the original family
charge and densest gain, not supplied as a scale certificate. -/
theorem exists_original_critical_query_threshold
    (gap eta' a eps1 C0 : ℝ) (ha : 0<a) (heps : 0<eps1) (hC0 : 0<C0)
    (hmargin : 4*eps1<gap-4*eta'/a) :
    ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 →
      ∀ (Pts : Finset Point) (G S : Finset Pair) (rho sigma m : ℝ),
        0<rho → rho≤1 → sigma≤1 → 0 < m → S.Nonempty →
        S⊆G → Set.InjOn (lineCell rho) (↑S : Set Pair) → G⊆Pts.product Pts →
        (∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1) → (∀ z∈G, z.1≠z.2) →
        (∀ z∈G,
          (delta^(2*eta'/a))^2*m≤((G.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
          (delta^(2*eta'/a))^2*m≤((G.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ)) →
        delta^(-gap)*rho^sigma*(Pts.card : ℝ)≤2^(sigma+1)*m →
        criticalWidth rho S≤1/448 ∧
        rho≤432*criticalWidth rho S+16*rho ∧
        432*criticalWidth rho S+16*rho≤1 ∧
        432*criticalWidth rho S+16*rho≤C0*delta^(4*eps1) := by
  let beta := gap-4*eta'/a
  have hbeta : 0<beta := by dsimp [beta]; linarith only [heps,hmargin]
  have hgap : 0<beta-4*eps1 := by dsimp [beta]; linarith only [hmargin]
  obtain ⟨d1,hd1,hd11,hcut1⟩ := exists_small_power_cutoff hbeta
    (by norm_num : (0:ℝ)<1/(448*288))
  obtain ⟨d2,hd2,_hd21,hcut2⟩ := exists_small_power_cutoff hgap
    (show 0<C0/(448*288) by positivity)
  refine ⟨min d1 d2,lt_min hd1 hd2,(min_le_left _ _).trans hd11,?_⟩
  intro delta hd hsmall Pts G S rho sigma m hrho hrho1 hsigma hm hSn hS hinj hGP hbox hdistinct hrich hgain
  have hwidth := original_family_native_critical_width_bound Pts G S delta rho eta' a gap sigma
    hd hrho hrho1 ha hsigma m hm hS hinj hGP hbox hdistinct hrich hgain
  change criticalWidth rho S≤288*delta^beta at hwidth
  have hlo := original_critical_width_ge_base rho S hrho hSn
  have hrhoW : rho≤criticalWidth rho S := by linarith only [hlo,hrho]
  have hpower1 := hcut1 delta hd (hsmall.trans (min_le_left _ _))
  have hWsmall : criticalWidth rho S≤1/448 := by linarith only [hwidth,hpower1]
  have hRupper : 432*criticalWidth rho S+16*rho≤448*criticalWidth rho S := by
    linarith only [hrhoW]
  have hpower2 := hcut2 delta hd (hsmall.trans (min_le_right _ _))
  have hproduct : (448*288)*delta^beta≤C0*delta^(4*eps1) := by
    have hh := mul_le_mul_of_nonneg_right hpower2 (Real.rpow_nonneg hd.le (4*eps1))
    rw [← Real.rpow_add hd,sub_add_cancel] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤448*288)
    have he : (448*288)*(C0/(448*288)*delta^(4*eps1))=C0*delta^(4*eps1) := by ring
    rw [he] at hh'
    exact hh'
  refine ⟨hWsmall,by linarith only [hrhoW,hrho],by linarith only [hRupper,hWsmall],?_⟩
  have hh : 432*criticalWidth rho S+16*rho≤(448*288)*delta^beta := by
    linarith only [hRupper,hwidth]
  exact hh.trans hproduct

end NativeOriginalCriticalQueryRange
