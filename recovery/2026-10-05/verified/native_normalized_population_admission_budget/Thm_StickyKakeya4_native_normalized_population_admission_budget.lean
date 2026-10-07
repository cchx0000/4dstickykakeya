import Theorems.Thm_StickyKakeya4_native_normalized_cell_source_upper
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeNormalizedPopulationAdmissionBudget
open NativeQuarterScaleParameters NativeLocalAdmissionBudget

def populationValue (delta r eta b : ℝ) (g : ℕ) (mass count cost : ℝ) : ℝ :=
  (r^b/(4*((g:ℝ)+1)))*(mass/count)*delta^eta/(2*cost)

/-- The literal lambda, retained grain mass and accumulated refinement cost
give a source population power. No population lower is supplied separately. -/
theorem population_from_original_mass {delta r eta a b c mass count cost : ℝ}
    (hd : 0<delta) (hr : delta≤r) (ha : 0≤a) (hb : 0≤b)
    (hcount : 0<count) (hcost : 0<cost) (g : ℕ)
    (hmass : r^a*count ≤ mass) (hcostUpper : cost≤delta^(-c)) :
    delta^(eta+a+b+c)/(8*((g:ℝ)+1))≤populationValue delta r eta b g mass count cost := by
  have hrpos := hd.trans_le hr
  have hmassRatio : r^a ≤ mass/count := (le_div_iff₀ hcount).mpr hmass
  have hA := (Real.rpow_le_rpow hd.le hr ha).trans hmassRatio
  have hB := Real.rpow_le_rpow hd.le hr hb
  have hright : delta^(eta+a+b)≤r^b*(mass/count)*delta^eta := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul hB hA (Real.rpow_nonneg hd.le a) (Real.rpow_nonneg hrpos.le b))
      (Real.rpow_nonneg hd.le eta)
    have hi : delta^b*delta^a*delta^eta=delta^(eta+a+b) := by
      rw [←Real.rpow_add hd,←Real.rpow_add hd]
      congr 1
      ring
    rwa [hi] at hh
  have hleft : delta^(eta+a+b+c)*cost≤delta^(eta+a+b) := by
    calc
      _ ≤ delta^(eta+a+b+c)*delta^(-c) :=
        mul_le_mul_of_nonneg_left hcostUpper (Real.rpow_nonneg hd.le _)
      _ = _ := by rw [←Real.rpow_add hd]; congr 1; ring
  have hC : 0<8*((g:ℝ)+1) := by positivity
  have he : populationValue delta r eta b g mass count cost=
      (r^b*(mass/count)*delta^eta)/(8*((g:ℝ)+1)*cost) := by
    unfold populationValue
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ hC (mul_pos hC hcost)).mpr
  have hh := mul_le_mul_of_nonneg_left (hleft.trans hright) hC.le
  convert hh using 1 <;> ring

/-- At the actual squared grain, epsilon=delta/Delta is at mostsqrt(delta). -/
theorem local_scale_root {delta Delta : ℝ} (hd : 0<delta) (hDelta : 0<Delta)
    (hsquare : delta≤Delta^2) : delta/Delta≤delta^(1/2:ℝ) := by
  have hroot : delta^(1/2:ℝ)≤Delta := by
    have hh := Real.rpow_le_rpow hd.le hsquare (by norm_num : (0:ℝ)≤1/2)
    rw [←Real.rpow_natCast,←Real.rpow_mul hDelta.le] at hh
    norm_num at hh
    exact hh
  have hid : delta^(1/2:ℝ)*delta^(1/2:ℝ)=delta := by
    rw [←Real.rpow_add hd]
    norm_num
  apply (div_le_iff₀ hDelta).mpr
  have hh := mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hd.le (1/2:ℝ))
  rwa [hid] at hh

lemma pay_local_root {delta epsilon e target C : ℝ}
    (hd : 0<delta) (hd1 : delta≤1) (heps : 0≤epsilon) (he : 0≤e) (hC : 0≤C)
    (hroot : epsilon≤delta^(1/2:ℝ)) (htarget : target≤e/4)
    (habsorb : C*delta^(e/4)≤1) : C*epsilon^e≤delta^target := by
  have hp : epsilon^e≤delta^(e/2) := by
    have hh := Real.rpow_le_rpow heps hroot he
    rw [←Real.rpow_mul hd.le] at hh
    convert hh using 1
    congr 1
    ring
  exact (mul_le_mul_of_nonneg_left hp hC).trans
    (pay_power hd hd1 habsorb (by linarith only [htarget] : target+e/4≤e/2))

/-- Fixed local exponents and finite menu size precede delta. The original
mass/cost formulas and squared-scale geometry pay AD,CW,density and relative
profile admission together; none of these four budgets is an input. -/
theorem exists_original_population_admission_cutoff (localEta profileExp : ℝ)
    (he : 0<localEta) (hp : 0<profileExp) (g : ℕ) :
    ∃delta0 : ℝ,0<delta0 ∧ delta0≤1/8 ∧
      ∀delta Delta r eta zeta a b c mass count cost : ℝ,
        0<delta → delta≤delta0 → 0<Delta → delta≤Delta^2 → delta≤r →
        0≤eta → 0≤a → 0≤b → eta+a+b+c≤localEta/4 → eta+zeta≤localEta/4 → zeta≤profileExp/4 →
        0<count → 0<cost → r^a*count ≤ mass → cost≤delta^(-c) →
        let epsilon := delta/Delta
        let population := populationValue delta r eta b g mass count cost
        (2048:ℝ)^3*epsilon^localEta≤delta^zeta ∧
        (373248*512^4:ℝ)*epsilon^localEta≤delta^(eta+zeta) ∧
        (1024*175616*NativeOriginalPrunedMass.volumeConstant)*epsilon^localEta≤population ∧
        (64:ℝ)^3*epsilon^profileExp≤delta^zeta := by
  let Cad : ℝ := 2048^3
  let Ccw : ℝ := 373248*512^4
  let Cden : ℝ := 1024*175616*NativeOriginalPrunedMass.volumeConstant
  let Cpop : ℝ := 8*((g:ℝ)+1)
  have hdenPos : 0<Cden := by dsimp [Cden]; exact mul_pos (by norm_num) NativeOriginalPrunedMass.volumeConstant_pos
  have hpopPos : 0<Cpop := by dsimp [Cpop]; positivity
  obtain ⟨dA,hdA,_hdA1,hA⟩ := exists_small_power_cutoff (show 0<localEta/4 by positivity)
    (show 0<1/Cad by norm_num [Cad])
  obtain ⟨dC,hdC,_hdC1,hC⟩ := exists_small_power_cutoff (show 0<localEta/4 by positivity)
    (show 0<1/Ccw by norm_num [Ccw])
  obtain ⟨dD,hdD,_hdD1,hD⟩ := exists_small_power_cutoff (show 0<localEta/4 by positivity)
    (show 0<1/(Cden*Cpop) by positivity)
  obtain ⟨dP,hdP,_hdP1,hP⟩ := exists_small_power_cutoff (show 0<profileExp/4 by positivity)
    (by norm_num : (0:ℝ)<1/(64:ℝ)^3)
  refine ⟨min (1/8) (min dA (min dC (min dD dP))),
    lt_min (by norm_num) (lt_min hdA (lt_min hdC (lt_min hdD hdP))),min_le_left _ _,?_⟩
  intro delta Delta r eta zeta a b c mass count cost hd hsmall hDelta hsquare hr heta ha hb htotal hcw hprofile
    hcount hcost hmass hcostUpper
  have hd1 : delta≤1 := (hsmall.trans (min_le_left _ _)).trans (by norm_num)
  have hsmallA := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallC := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallD := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsmallP := hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hroot := local_scale_root hd hDelta hsquare
  have hAbsorb (C e : ℝ) (hC : 0<C) (hh : delta^e≤1/C) : C*delta^e≤1 := by
    have hm := mul_le_mul_of_nonneg_left hh hC.le
    simpa only [mul_one_div_cancel hC.ne'] using hm
  have hAd := pay_local_root hd hd1 (div_nonneg hd.le hDelta.le) he.le (by norm_num : (0:ℝ)≤Cad)
    hroot (by linarith only [heta,hcw] : zeta≤localEta/4)
    (hAbsorb Cad (localEta/4) (by norm_num [Cad]) (hA delta hd hsmallA))
  have hCw := pay_local_root hd hd1 (div_nonneg hd.le hDelta.le) he.le (by norm_num : (0:ℝ)≤Ccw)
    hroot hcw (hAbsorb Ccw (localEta/4) (by norm_num [Ccw]) (hC delta hd hsmallC))
  have hDen := pay_local_root hd hd1 (div_nonneg hd.le hDelta.le) he.le (mul_pos hdenPos hpopPos).le
    hroot htotal (hAbsorb (Cden*Cpop) (localEta/4) (mul_pos hdenPos hpopPos) (hD delta hd hsmallD))
  have hPop := population_from_original_mass (eta:=eta) hd hr ha hb hcount hcost g hmass hcostUpper
  have hDen' : Cden*(delta/Delta)^localEta≤populationValue delta r eta b g mass count cost := by
    apply le_trans _ hPop
    apply (le_div_iff₀ hpopPos).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hDen
  have hProf := pay_local_root hd hd1 (div_nonneg hd.le hDelta.le) hp.le (by norm_num : (0:ℝ)≤(64:ℝ)^3)
    hroot hprofile (hAbsorb ((64:ℝ)^3) (profileExp/4) (by norm_num) (hP delta hd hsmallP))
  exact ⟨hAd,hCw,hDen',hProf⟩

end NativeNormalizedPopulationAdmissionBudget
