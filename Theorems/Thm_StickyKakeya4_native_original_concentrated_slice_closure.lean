import Theorems.Thm_StickyKakeya4_native_three_dimensional_small_slice
import Theorems.Thm_StickyKakeya4_native_original_log_budget
import Theorems.Thm_StickyKakeya4_native_original_concentrated_pair_graph
import Theorems.Thm_StickyKakeya4_original_three_dimensional_source_hairbrush_slab
import Theorems.Thm_StickyKakeya4_original_three_dimensional_literal_slab_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators

/- Source component: OriginalThreeDimensionalSliceParameterChoice -/

namespace OriginalThreeDimensionalSliceParameterChoice
open NativeOriginalLogBudget OriginalPhysicalTubeScaleSelection NativeQuarterScaleParameters

/-- The literal selected physical enlargement determines its slicing
exponent after the fixed source parameters have been chosen. -/
def sliceExponent (delta D epsilon : ℝ) : ℝ :=
  ((51/50:ℝ)*epsilon)*Real.log delta/Real.log D

/-- The actual scale relation gives the source identity (248), uniformly
in all selected enlargements in the permitted physical range. -/
theorem original_slice_exponent_spec (delta D epsilon : ℝ)
    (hd : 0 < delta) (hd1 : delta < 1) (he : 0 < epsilon)
    (hquery : delta ≤ D) (hscale : D ≤ delta^((51/50:ℝ)*epsilon)) :
    epsilon ≤ sliceExponent delta D epsilon ∧ sliceExponent delta D epsilon ≤ 1 ∧
      D^(sliceExponent delta D epsilon)=delta^((51/50:ℝ)*epsilon) := by
  have hD : 0 < D := hd.trans_le hquery
  have ha : 0 < (51/50:ℝ)*epsilon := by positivity
  have hD1 : D < 1 := hscale.trans_lt (Real.rpow_lt_one hd.le hd1 ha)
  have hlD : Real.log D < 0 := Real.log_neg hD hD1
  have hlog := Real.log_le_log hd hquery
  have hlogscale := Real.log_le_log hD hscale
  rw [Real.log_rpow hd] at hlogscale
  have hlower : (51/50:ℝ)*epsilon ≤ sliceExponent delta D epsilon := by
    unfold sliceExponent
    apply (le_div_iff_of_neg hlD).mpr
    exact mul_le_mul_of_nonneg_left hlog ha.le
  have hupper : sliceExponent delta D epsilon ≤ 1 := by
    unfold sliceExponent
    apply (div_le_iff_of_neg hlD).mpr
    simpa only [one_mul] using hlogscale
  refine ⟨(by linarith only [hlower,he]),hupper,?_⟩
  rw [Real.rpow_def_of_pos hD,Real.rpow_def_of_pos hd]
  congr 1
  unfold sliceExponent
  field_simp [ne_of_lt hlD]

/-- The upper radius keeps the literal 149/10000 epsilon margin after the
native maximizing-radius rounding factor two. -/
lemma original_selected_slice_width_power (delta D epsilon tau : ℝ)
    (hd : 0 < delta) (hD : 0 < D)
    (hidentity : D^(sliceExponent delta D epsilon)=delta^((51/50:ℝ)*epsilon))
    (hupper : tau ≤ 2*D^((199/200:ℝ)*sliceExponent delta D epsilon)) :
    tau ≤ 2*delta^(epsilon+(149/10000:ℝ)*epsilon) := by
  have hp : D^((199/200:ℝ)*sliceExponent delta D epsilon)=
      delta^(epsilon+(149/10000:ℝ)*epsilon) := by
    rw [mul_comm (199/200:ℝ),Real.rpow_mul hD.le,hidentity,← Real.rpow_mul hd.le]
    congr 1
    ring
  simpa only [hp] using hupper

/-- A coarser selected dyadic menu is bounded by the ORIGINAL fine mesh.
It is not necessary that the selected radius be comparable to delta. -/
lemma original_coarse_menu_log_bound (delta : ℝ) (n : ℕ)
    (hd : 0 < delta) (hquery : delta ≤ dyadicRadius n) :
    (n:ℝ)+1 ≤ 1+(1/Real.log 2)*(-Real.log delta) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log hd hquery
  have hid : Real.log (dyadicRadius n)=-(n:ℝ)*Real.log 2 := by
    unfold dyadicRadius
    rw [Real.log_pow,Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0),Real.log_one]
    ring
  rw [hid] at hlog
  have hn : (n:ℝ) ≤ (-Real.log delta)/Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by linarith only [hlog])
  have heq : (-Real.log delta)/Real.log 2=(1/Real.log 2)*(-Real.log delta) := by ring
  rw [heq] at hn
  linarith only [hn]

theorem exists_original_coarse_menu_cutoff (eta : ℝ) (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 → ∀ n : ℕ,
        delta ≤ dyadicRadius n → (n:ℝ)+1 ≤ delta^(-eta) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_logarithmic_budget_cutoff heta
    (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ 1/Real.log 2)
  exact ⟨delta0,hd0,hd01,fun delta hd hsmall n hquery =>
    (original_coarse_menu_log_bound delta n hd hquery).trans (hcut delta hd hsmall)⟩

end OriginalThreeDimensionalSliceParameterChoice


/- Source component: OriginalThreeDimensionalNativeSliceScale -/

namespace OriginalThreeDimensionalNativeSliceScale
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeFrostman
open OriginalThreeDimensionalSliceParameterChoice NativeQuarterScaleParameters

/-- Original rich-tube gain and original 2-Frostman control place the
actual enlarged slice in the range needed to define the variable exponent.
The cutoff is fixed before the original point source and selected radius. -/
theorem exists_original_slice_parameter_cutoff (zeta gamma A epsilon eta : ℝ)
    (hgap : gamma < zeta) (hgamma : gamma < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetagain : eta ≤ (zeta-gamma)/2)
    (hmargin : 2*eta+(51/50:ℝ)*epsilon < (zeta-gamma)/(4*(1-gamma))) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1/2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ (P : Finset Point3) (z : Pair3) (rho : ℝ),
        P.Nonempty → delta ≤ rho → rho ≤ 1 →
        (∀ p∈P, ∀ i, |p i| ≤ 1) →
        (∀ p∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
          ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card) →
        delta^(-(zeta-gamma))*rho^(2-gamma)*P.card ≤ A*(physicalPairTube3 P rho z).card →
        let D := 54*rho/delta^(2*eta)
        delta ≤ D ∧ D ≤ delta^((51/50:ℝ)*epsilon) ∧
          epsilon ≤ sliceExponent delta D epsilon ∧ sliceExponent delta D epsilon ≤ 1 ∧
          D^(sliceExponent delta D epsilon)=delta^((51/50:ℝ)*epsilon) := by
  let kappa := (zeta-gamma)/(4*(1-gamma))
  let a := (51/50:ℝ)*epsilon
  have hexp : 0 < kappa-2*eta-a := by dsimp [kappa,a]; linarith only [hmargin]
  obtain ⟨dS,hdS,hdS1,hscale⟩ := exists_original_rich_tube_scale_cutoff zeta gamma A hgap hgamma hA
  obtain ⟨dD,hdD,_hdD1,hDcut⟩ := exists_small_power_cutoff hexp (by norm_num : (0:ℝ) < 1/54)
  refine ⟨min (1/2) (min dS dD),lt_min (by norm_num) (lt_min hdS hdD),min_le_left _ _,?_⟩
  intro delta hd hsmall P z rho hP hquery hrho1 hbox hfrostman hgain
  have hdhalf : delta ≤ 1/2 := hsmall.trans (min_le_left _ _)
  have hd1 : delta < 1 := by linarith only [hdhalf]
  have hsmallS := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallD := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdecay := hscale delta hd hsmallS eta heta.le hetagain P z rho hP hquery hrho1 hbox hfrostman hgain
  change rho ≤ delta^kappa at hdecay
  let r := delta^(2*eta)
  let D := 54*rho/r
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := Real.rpow_le_one hd.le hd1.le (by positivity : 0 ≤ 2*eta)
  have hD : 0 < D := by dsimp [D]; exact div_pos (by linarith only [hd,hquery]) hr
  have hDr : D*r=54*rho := by dsimp [D]; field_simp
  have hqueryD : delta ≤ D := by
    have hh := mul_le_mul_of_nonneg_left hr1 hD.le
    rw [hDr,mul_one] at hh
    linarith only [hh,hquery,hd]
  have hDpower : D ≤ 54*delta^(kappa-2*eta) := by
    rw [Real.rpow_sub hd]
    dsimp [D,r]
    have hh := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hdecay (Real.rpow_nonneg hd.le (2*eta)))
      (by norm_num : (0:ℝ) ≤ 54)
    simpa only [mul_div_assoc] using hh
  have hprod := mul_le_mul_of_nonneg_right (hDcut delta hd hsmallD) (Real.rpow_nonneg hd.le a)
  have hid : delta^(kappa-2*eta-a)*delta^a=delta^(kappa-2*eta) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  rw [hid] at hprod
  have hDa : D ≤ delta^a := by nlinarith only [hDpower,hprod]
  have hspec := original_slice_exponent_spec delta D epsilon hd hd1 hepsilon hqueryD hDa
  exact ⟨hqueryD,hDa,hspec⟩

end OriginalThreeDimensionalNativeSliceScale


/- Source component: OriginalThreeDimensionalConcentratedBudget -/

namespace OriginalThreeDimensionalConcentratedBudget
open OriginalPhysicalTubeScaleSelection

lemma original_concentrated_effective_exponent (epsilon e1 e2 : ℝ)
    (hepsilon : 0 < epsilon) (he1 : epsilon ≤ e1) (he11 : e1 ≤ 1)
    (he2 : 0 < e2) (hsmall : 200*e2 ≤ epsilon) :
    0 < 200*e2/e1 ∧ 200*e2/e1 ≤ 1 ∧
      0 ≤ e2+(200*e2/e1)*(1-e1) ∧
      e2+(200*e2/e1)*(1-e1) ≤ (1+200/epsilon)*e2 := by
  have he1pos : 0 < e1 := hepsilon.trans_le he1
  have ha : 0 < 200*e2/e1 := by positivity
  have ha1 : 200*e2/e1 ≤ 1 := (div_le_one he1pos).mpr (hsmall.trans he1)
  have hE : 0 ≤ e2+(200*e2/e1)*(1-e1) :=
    add_nonneg he2.le (mul_nonneg ha.le (sub_nonneg.mpr he11))
  have hden : 200*e2/e1 ≤ 200*e2/epsilon :=
    div_le_div_of_nonneg_left (by positivity) hepsilon he1
  have hprod := mul_le_mul_of_nonneg_left (show 1-e1 ≤ 1 by linarith only [he1pos]) ha.le
  refine ⟨ha,ha1,hE,?_⟩
  have heq : (1+200/epsilon)*e2=e2+200*e2/epsilon := by ring
  rw [heq]
  nlinarith only [hden,hprod]

/-- The actual direction-menu density retains both r powers, the original
heavy-slice exponent, the effective concentration loss, and the literal
menu denominator. Fixed constants and the menu are paid at true cutoffs. -/
theorem original_concentrated_density_lower (delta rho Delta eta D E E0 c : ℝ) (n : ℕ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 < eta) (hD : 0 ≤ D)
    (hquery : delta ≤ rho) (hqueryD : delta ≤ Delta) (hE : 0 ≤ E) (hEE : E ≤ E0)
    (hmenu : (n:ℝ)+1 ≤ delta^(-eta))
    (hconstant : delta^eta ≤ c/(4*4665600000)) :
    delta^((6+D)*eta+E0) ≤
      ((1/4:ℝ)/((n:ℝ)+1))*(c*(delta^(2*eta))^2/4665600000*rho^(D*eta)*Delta^E) := by
  let Q : ℝ := (n:ℝ)+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hdp : 0 < delta^eta := Real.rpow_pos_of_pos hd _
  have hmenu' : delta^eta ≤ 1/Q := by
    apply (le_div_iff₀ hQ).mpr
    have hh := mul_le_mul_of_nonneg_right hmenu hdp.le
    have hid : delta^(-eta)*delta^eta=1 := by
      rw [← Real.rpow_add hd,neg_add_cancel,Real.rpow_zero]
    rw [hid] at hh
    simpa only [Q,mul_comm] using hh
  have hc : 0 ≤ c/(4*4665600000) := hdp.le.trans hconstant
  have hconst := mul_le_mul hconstant hmenu' hdp.le hc
  have hrho : delta^(D*eta) ≤ rho^(D*eta) :=
    Real.rpow_le_rpow hd.le hquery (mul_nonneg hD heta.le)
  have hDelta : delta^E0 ≤ Delta^E :=
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 hEE).trans
      (Real.rpow_le_rpow hd.le hqueryD hE)
  have hr2 : (delta^(2*eta))^2=delta^(4*eta) := by
    rw [← Real.rpow_mul_natCast hd.le]
    congr 1
    ring
  have hprod := mul_le_mul
    (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hd.le (4*eta)))
    (mul_le_mul hrho hDelta (Real.rpow_nonneg hd.le E0)
      (Real.rpow_nonneg (hd.le.trans hquery) (D*eta)))
    (mul_nonneg (Real.rpow_nonneg hd.le (D*eta)) (Real.rpow_nonneg hd.le E0))
    (by positivity : 0 ≤ (c/(4*4665600000)*(1/Q))*delta^(4*eta))
  have hid : (delta^eta*delta^eta*delta^(4*eta))*(delta^(D*eta)*delta^E0)=
      delta^((6+D)*eta+E0) := by
    rw [← Real.rpow_add hd,← Real.rpow_add hd,← Real.rpow_add hd,← Real.rpow_add hd]
    congr 1
    ring
  rw [hid] at hprod
  have hnorm : ((1/4:ℝ)/((n:ℝ)+1))*(c*delta^(4*eta)/4665600000*rho^(D*eta)*Delta^E)=
      (c/(4*4665600000)*(1/Q))*delta^(4*eta)*(rho^(D*eta)*Delta^E) := by
    change ((1/4:ℝ)/((n:ℝ)+1))*(c*delta^(4*eta)/4665600000*rho^(D*eta)*Delta^E)=
      (c/(4*4665600000)*(1/((n:ℝ)+1)))*delta^(4*eta)*(rho^(D*eta)*Delta^E)
    ring
  rw [hr2,hnorm]
  exact hprod

/-- Fix epsilon2-star before eta and before the source/mesh. The explicit
149/10000 width margin pays the actual native losses; the mass margin
includes the literal two menus and all exponents of the direct hairbrush. -/
theorem exists_original_concentrated_parameter_budget (zeta epsilon eps2 D L etaUpper : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hepsilon : 0 < epsilon)
    (hepsmall : epsilon ≤ zeta/100) (heps2 : 0 < eps2)
    (hD : 0 ≤ D) (hL : 0 < L) (hupper : 0 < etaUpper) :
    ∃ e2 : ℝ, 0 < e2 ∧ 200*e2 ≤ epsilon ∧
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ etaUpper ∧ eta ≤ (zeta-zeta/100)/2 ∧
        2*eta+(51/50:ℝ)*epsilon < (zeta-zeta/100)/(4*(1-zeta/100)) ∧
        (L+10+D)*eta+(1+200/epsilon)*e2 ≤ (149/10000:ℝ)*epsilon ∧
        (10*L+119+14*D)*eta+14*((1+200/epsilon)*e2) ≤ eps2 := by
  let a := (51/50:ℝ)*epsilon
  let kappa := (zeta-zeta/100)/(4*(1-zeta/100))
  let S := (149/10000:ℝ)*epsilon
  let E := 1+200/epsilon
  let W := L+10+D
  let V := 10*L+119+14*D
  have ha : 0 < a := by dsimp [a]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hgap : 0 < zeta-zeta/100 := by linarith only [hzeta]
  have hden : 0 < 4*(1-zeta/100) := by linarith only [hzeta1]
  have hk : zeta/5 ≤ kappa := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [sq_nonneg zeta,hzeta]
  have hak : a < kappa := by dsimp [a]; linarith only [hk,hepsmall,hzeta]
  have hkdiff : 0 < kappa-a := sub_pos.mpr hak
  let e2 := min (epsilon/400) (min (S/(4*E)) (eps2/(56*E)))
  have he2 : 0 < e2 := by dsimp [e2]; positivity
  have he2small : 200*e2 ≤ epsilon := by
    have hh : e2 ≤ epsilon/400 := min_le_left _ _
    linarith only [hh,hepsilon]
  have hES : E*e2 ≤ S/4 := by
    have hh : e2 ≤ S/(4*E) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (show 0 < 4*E by positivity)).mp hh
    nlinarith only [hh']
  have hE2 : 14*(E*e2) ≤ eps2/4 := by
    have hh : e2 ≤ eps2/(56*E) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (show 0 < 56*E by positivity)).mp hh
    nlinarith only [hh']
  let eta := min etaUpper (min ((zeta-zeta/100)/4)
    (min ((kappa-a)/4) (min (S/(4*W)) (eps2/(4*V)))))
  have heta : 0 < eta := by dsimp [eta]; exact lt_min hupper (lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hηu : eta ≤ etaUpper := min_le_left _ _
  have hηg : eta ≤ (zeta-zeta/100)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηk : eta ≤ (kappa-a)/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηW : W*eta ≤ S/4 := by
    have hh : eta ≤ S/(4*W) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hh' := (le_div_iff₀ (show 0 < 4*W by positivity)).mp hh
    nlinarith only [hh']
  have hηV : V*eta ≤ eps2/4 := by
    have hh : eta ≤ eps2/(4*V) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hh' := (le_div_iff₀ (show 0 < 4*V by positivity)).mp hh
    nlinarith only [hh']
  refine ⟨e2,he2,he2small,eta,heta,hηu,?_,?_,?_,?_⟩
  · linarith only [hηg,hgap]
  · change 2*eta+a < kappa
    linarith only [hηk,hak]
  · change W*eta+E*e2 ≤ S
    linarith only [hηW,hES,hS]
  · change V*eta+14*(E*e2) ≤ eps2
    linarith only [hηV,hE2,heps2]

end OriginalThreeDimensionalConcentratedBudget


/- Source component: NativeOriginalConcentratedSlabExclusion -/

namespace NativeOriginalConcentratedSlabExclusion
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalPhysicalTubeScaleSelection
open NativeQuarterScaleParameters NativeThreeDimensionalSmallSlice
open OriginalThreeDimensionalSliceParameterChoice OriginalThreeDimensionalNativeSliceScale
open OriginalThreeDimensionalConcentratedBudget NativeOriginalConcentratedPairGraph
open OriginalThreeDimensionalSourceHairbrushSlab

private lemma width_power_budget (delta eta epsilon D L E tau : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hwidth : (L+10+D)*eta+E ≤ (149/10000:ℝ)*epsilon)
    (htau : tau ≤ 2*delta^(epsilon+(149/10000:ℝ)*epsilon))
    (hc : 4000000000000*delta^eta ≤ 1) :
    1000000000000*(delta^(-eta))^2*tau/
      (delta^((L+1)*eta)*delta^((6+D)*eta+E)) ≤ delta^epsilon/2 := by
  let A := epsilon+(L+7+D)*eta+E
  have hpow : (delta^(-eta))^2=delta^(-2*eta) := by
    rw [← Real.rpow_mul_natCast hd.le]
    congr 1
    ring
  have hden : delta^((L+1)*eta)*delta^((6+D)*eta+E)=delta^((L+7+D)*eta+E) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hp : delta^(epsilon+(149/10000:ℝ)*epsilon-2*eta) ≤ delta^(A+eta) := by
    apply Real.rpow_le_rpow_of_exponent_ge hd hd1
    dsimp [A]
    linarith only [hwidth]
  have hleft : 1000000000000*(delta^(-eta))^2*tau ≤ 2000000000000*delta^(A+eta) := by
    have hh := mul_le_mul_of_nonneg_left htau
      (show 0 ≤ 1000000000000*(delta^(-eta))^2 by positivity)
    have heq : 1000000000000*(delta^(-eta))^2*(2*delta^(epsilon+(149/10000:ℝ)*epsilon))=
        2000000000000*delta^(epsilon+(149/10000:ℝ)*epsilon-2*eta) := by
      rw [hpow]
      calc
        _ = 2000000000000*(delta^(-2*eta)*delta^(epsilon+(149/10000:ℝ)*epsilon)) := by ring
        _ = _ := by rw [← Real.rpow_add hd]; congr 2; ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
  have hright : 2000000000000*delta^(A+eta) ≤ delta^A/2 := by
    rw [Real.rpow_add hd]
    have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hd.le A)
    nlinarith only [hh]
  apply (div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hd _) (Real.rpow_pos_of_pos hd _))).mpr
  have heq : delta^epsilon/2*(delta^((L+1)*eta)*delta^((6+D)*eta+E))=delta^A/2 := by
    rw [hden]
    calc
      _ = (delta^epsilon*delta^((L+7+D)*eta+E))/2 := by ring
      _ = _ := by
        rw [← Real.rpow_add hd]
        exact congrArg (fun x : ℝ => delta^x/2) (by
          change epsilon+((L+7+D)*eta+E)=epsilon+(L+7+D)*eta+E
          ring)
  rw [heq]
  exact hleft.trans hright

private lemma mass_power_contradiction (delta eta eps2 D L E C p q Q : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hp : 0 < p) (hq : 0 ≤ q)
    (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hmenu : Q ≤ delta^(-eta))
    (hbudget : (10*L+119+14*D)*eta+14*E ≤ eps2)
    (hc : 2*(10:ℝ)^140*(C+1)*delta^eta ≤ 1)
    (hsource : (delta^((L+1)*eta))^10*(delta^((6+D)*eta+E))^14*p ≤
      (10:ℝ)^140*(delta^(-eta))^21*Q^3*q)
    (hcap : q ≤ C*delta^eps2*p) : False := by
  let A := 10*((L+1)*eta)+14*((6+D)*eta+E)
  have hnum : (delta^((L+1)*eta))^10*(delta^((6+D)*eta+E))^14=delta^A := by
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
    congr 1
    dsimp [A]
    ring
  have hden : (delta^(-eta))^21*(delta^(-eta))^3=delta^(-24*eta) := by
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
    congr 1
    ring
  have hQpow := pow_le_pow_left₀ hQ hmenu 3
  have hupper : (10:ℝ)^140*(delta^(-eta))^21*Q^3*q ≤
      (10:ℝ)^140*C*delta^(eps2-24*eta)*p := by
    calc
      _ ≤ (10:ℝ)^140*(delta^(-eta))^21*(delta^(-eta))^3*(C*delta^eps2*p) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQpow (by positivity)) hcap hq (by positivity)
      _ = _ := by
        calc
          _ = (10:ℝ)^140*C*((delta^(-eta))^21*(delta^(-eta))^3*delta^eps2)*p := by ring
          _ = _ := by rw [hden,← Real.rpow_add hd]; congr 3; ring
  rw [hnum] at hsource
  have hineq : delta^A ≤ (10:ℝ)^140*C*delta^(eps2-24*eta) :=
    (mul_le_mul_iff_of_pos_right hp).mp (hsource.trans hupper)
  have hpow : delta^(eps2-24*eta) ≤ delta^(A+eta) := by
    apply Real.rpow_le_rpow_of_exponent_ge hd hd1
    dsimp [A]
    linarith only [hbudget]
  have hineq' := hineq.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg (pow_nonneg (by norm_num) 140) hC))
  rw [Real.rpow_add hd A eta] at hineq'
  have hone : 1 ≤ (10:ℝ)^140*C*delta^eta := by
    apply (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hd A)).mp
    nlinarith only [hineq']
  have hextra : 0 ≤ (10:ℝ)^140*delta^eta := by positivity
  nlinarith only [hone,hc,hextra]

/-- Literal original concentrated pairs are excluded using the proved
original-source hairbrush theorem. The selected radius, both menus,
original heavy populations, actual original ball law, and original slab
cap all remain explicit. The cap coefficient allows the separate fixed
cover by finite length-one slabs; its normal half-width is delta^epsilon/2. -/
theorem exists_original_concentrated_graph_cutoff
    (zeta gamma A epsilon eps2 D L eta e2 Cslab : ℝ)
    (hgap : gamma < zeta) (hgamma : gamma < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (_heps2 : 0 < eps2) (hD : 0 ≤ D) (hL : 0 < L)
    (heta : 0 < eta) (he2 : 0 < e2) (he2small : 200*e2 ≤ epsilon) (hCslab : 0 ≤ Cslab)
    (hetagain : eta ≤ (zeta-gamma)/2)
    (hscale : 2*eta+(51/50:ℝ)*epsilon < (zeta-gamma)/(4*(1-gamma)))
    (hwidth : (L+10+D)*eta+(1+200/epsilon)*e2 ≤ (149/10000:ℝ)*epsilon)
    (hmass : (10*L+119+14*D)*eta+14*((1+200/epsilon)*e2) ≤ eps2) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1/2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ) (n : ℕ),
        P.Nonempty → delta ≤ rho → rho ≤ 1 → rho=dyadicRadius n →
        G⊆P.product P →
        (∀ p∈P, ∀ j, |p j| ≤ 1) →
        (∀ z∈G, delta^(2*eta) ≤ distance3 z.1 z.2) →
        (∀ p∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
          ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card) →
        (∀ z∈G, delta^(-(zeta-gamma))*rho^(2-gamma)*P.card ≤
          A*(physicalPairTube3 P rho z).card) →
        (∀ normal : Point3, ∀ c : ℝ, (∑ j, normal j^2)=1 →
          ((P.filter (fun x => |(∑ j, normal j*x j)-c| ≤ delta^epsilon/2)).card : ℝ) ≤
            Cslab*delta^eps2*P.card) →
        let r := delta^(2*eta)
        let Delta := 54*rho/r
        let e1 := sliceExponent delta Delta epsilon
        ((concentratedPairGraph P G rho r (D*eta) e1 e2 (1/4)).card : ℝ) <
          delta^(L*eta)*(P.card : ℝ)^2 := by
  obtain ⟨M,hcontract⟩ := exists_uniform_original_slice_contraction e2 1 he2 (by norm_num)
  have hcM : 0 < dyadicRadius M := by dsimp [dyadicRadius]; positivity
  obtain ⟨dS,hdS,hdS1,hscut⟩ := exists_original_slice_parameter_cutoff
    zeta gamma A epsilon eta hgap hgamma hA hepsilon heta hetagain hscale
  obtain ⟨dQ,hdQ,_hdQ1,hqcut⟩ := exists_original_coarse_menu_cutoff eta heta
  let C := min (dyadicRadius M/(4*4665600000))
    (min (1/4000000000000) (1/(2*(10:ℝ)^140*(Cslab+1))))
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨dC,hdC,_hdC1,hccut⟩ := exists_small_power_cutoff heta hC
  refine ⟨min dS (min dQ dC),lt_min hdS (lt_min hdQ hdC),(min_le_left _ _).trans hdS1,?_⟩
  intro delta hd hsmall P G rho n hP hquery hrho1 hmesh hGP hbox hsep hfrostman hgain hslab
  let r := delta^(2*eta)
  let Delta := 54*rho/r
  let e1 := sliceExponent delta Delta epsilon
  let E0 := (1+200/epsilon)*e2
  let B := concentratedPairGraph P G rho r (D*eta) e1 e2 (1/4)
  have hdhalf : delta ≤ 1/2 := hsmall.trans ((min_le_left _ _).trans hdS1)
  have hd1 : delta < 1 := by linarith only [hdhalf]
  have hrho : 0 < rho := hd.trans_le hquery
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := Real.rpow_le_one hd.le hd1.le (by positivity : 0 ≤ 2*eta)
  have hPpos : 0 < (P.card : ℝ) := by exact_mod_cast hP.card_pos
  have hsmallS := hsmall.trans (min_le_left _ _)
  have hsmallQ := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallC := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmenu : (n:ℝ)+1 ≤ delta^(-eta) := hqcut delta hd hsmallQ n (by simpa only [← hmesh] using hquery)
  have hconst := hccut delta hd hsmallC
  have hconstnu : delta^eta ≤ dyadicRadius M/(4*4665600000) := hconst.trans (min_le_left _ _)
  have hconstW : 4000000000000*delta^eta ≤ 1 := by
    have hh := hconst.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hh]
  have hconstM : 2*(10:ℝ)^140*(Cslab+1)*delta^eta ≤ 1 := by
    have hh := hconst.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hp : 0 < 2*(10:ℝ)^140*(Cslab+1) := by positivity
    have hh' := (le_div_iff₀ hp).mp hh
    nlinarith only [hh']
  change (B.card : ℝ) < delta^(L*eta)*(P.card : ℝ)^2
  by_contra! hlarge
  have hBn : B.Nonempty := Finset.card_pos.mp (by
    have hh : 0 < (B.card : ℝ) := (by positivity : 0 < delta^(L*eta)*(P.card : ℝ)^2).trans_le hlarge
    exact_mod_cast hh)
  obtain ⟨z₀,hz₀⟩ := hBn
  have hBG : B⊆G := Finset.filter_subset _ _
  obtain ⟨hqueryD,hDscale,he1lo,he11,hidentity⟩ := hscut delta hd hsmallS P z₀ rho hP
    hquery hrho1 hbox hfrostman (hgain z₀ (hBG hz₀))
  change delta ≤ Delta at hqueryD
  change Delta ≤ delta^((51/50:ℝ)*epsilon) at hDscale
  change epsilon ≤ e1 at he1lo
  change e1 ≤ 1 at he11
  change Delta^e1=delta^((51/50:ℝ)*epsilon) at hidentity
  have hDpos : 0 < Delta := hd.trans_le hqueryD
  have hD1 : Delta ≤ 1 := hDscale.trans (Real.rpow_le_one hd.le hd1.le (by positivity))
  have he1 : 0 < e1 := hepsilon.trans_le he1lo
  obtain ⟨_ha,ha1,hE,hEE⟩ := original_concentrated_effective_exponent epsilon e1 e2
    hepsilon he1lo he11 he2 he2small
  have hnuLower := original_concentrated_density_lower delta rho Delta eta D
    (e2+(200*e2/e1)*(1-e1)) E0 (dyadicRadius M) n hd hd1.le heta hD hquery hqueryD hE hEE hmenu hconstnu
  have hselected := original_concentrated_graph_rich_radius P G rho r (D*eta) e1 e2 (1/4) n M
    hrho hr hr1 he1 he11 he2 ha1 (by norm_num) (by norm_num) hmesh
    (hcontract e1 he1 he11) hD1 hGP hbox hsep
  rcases hselected with hzero | ⟨_hnu,j,hj,htau,H,hHB,_hHn,hHcard,hdata⟩
  · change B=∅ at hzero
    rw [hzero] at hz₀
    exact Finset.notMem_empty _ hz₀
  let tau := dyadicRadius j
  let lam := delta^((L+1)*eta)
  let nu := delta^((6+D)*eta+E0)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have hE0 : 0 < E0 := by dsimp [E0]; positivity
  have hlam1 : lam ≤ 1 := Real.rpow_le_one hd.le hd1.le (by positivity)
  have hnu1 : nu ≤ 1 := Real.rpow_le_one hd.le hd1.le (by positivity)
  have hHGP : H⊆P.product P := hHB.trans (hBG.trans hGP)
  have hHne : ∀ z∈H, z.1≠z.2 := by
    intro z hz heq
    have hh := hsep z (hBG (hHB hz))
    rw [heq] at hh
    simp only [distance3,sub_self,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_zero] at hh
    exact (not_le_of_gt hr) hh
  have hQprod : ((n:ℝ)+1)*delta^eta ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hmenu (Real.rpow_nonneg hd.le eta)
    rw [← Real.rpow_add hd,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  have hHdense : lam*(P.card : ℝ)^2 ≤ H.card := by
    have hc : (B.card : ℝ) ≤ ((n:ℝ)+1)*H.card := by exact_mod_cast hHcard
    have hh := mul_le_mul_of_nonneg_left (hlarge.trans hc) (Real.rpow_nonneg hd.le eta)
    have hh2 := mul_le_mul_of_nonneg_right hQprod (Nat.cast_nonneg H.card)
    have hid : delta^eta*delta^(L*eta)=lam := by
      rw [← Real.rpow_add hd]
      dsimp [lam]
      congr 1
      ring
    have hh' : lam*(P.card : ℝ)^2 ≤ delta^eta*(((n:ℝ)+1)*H.card) := by
      simpa only [← mul_assoc,hid] using hh
    nlinarith only [hh',hh2]
  have htaurho : rho ≤ tau := by
    rw [hmesh]
    exact pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num) hj
  have htaup : 0 < tau := hrho.trans_le htaurho
  have htau1 : tau ≤ 1 := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hterminal : 1 ≤ 2*OriginalThreeDimensionalPairEnergy.dyadicRadius tau n := by
    have hid : (2:ℝ)^n*dyadicRadius n=1 := by
      unfold dyadicRadius
      rw [← mul_pow]
      norm_num
    have hh := mul_le_mul_of_nonneg_left htaurho (show 0 ≤ (2:ℝ)^n by positivity)
    rw [hmesh,hid] at hh
    change 1 ≤ 2*((2:ℝ)^n*tau)
    linarith only [hh]
  have hrich : ∀ z∈H, nu*tau*P.card ≤ ((physicalPairTube3 P tau z).card : ℝ) := by
    intro z hz
    have hh := mul_le_mul_of_nonneg_right hnuLower (show 0 ≤ tau*P.card by positivity)
    apply le_trans ?_ (hdata z hz).1
    simpa only [mul_assoc] using hh
  obtain ⟨normal,c,hunit,hsource⟩ := exists_original_source_hairbrush_slab P H delta eta tau lam nu n
    hd hd1.le heta.le (hquery.trans htaurho) htau1 hlam hlam1 hnu hnu1 hP hHGP hHne
    hHdense hterminal hbox hfrostman hrich
  have htaupower := original_selected_slice_width_power delta Delta epsilon tau hd hDpos hidentity htau
  have hW := width_power_budget delta eta epsilon D L E0 tau hd hd1.le hwidth htaupower hconstW
  let Q := P.filter (fun x => |(∑ j,normal j*x j)-c| ≤
    1000000000000*(delta^(-eta))^2*tau/(lam*nu))
  have hsub : Q⊆P.filter (fun x => |(∑ j,normal j*x j)-c| ≤ delta^epsilon/2) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2.trans hW⟩
  have hcap : (Q.card : ℝ) ≤ Cslab*delta^eps2*P.card :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hslab normal c hunit)
  exact mass_power_contradiction delta eta eps2 D L E0 Cslab (P.card : ℝ) (Q.card : ℝ)
    ((n:ℝ)+1) hd hd1.le hPpos (Nat.cast_nonneg _) (by positivity) hCslab hmenu hmass
    hconstM hsource hcap

end NativeOriginalConcentratedSlabExclusion


/- Source component: NativeOriginalNonconcentratedSliceGraph -/

namespace NativeOriginalNonconcentratedSliceGraph
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalPhysicalTubeScaleSelection OriginalThreeDimensionalSliceParameterChoice
open NativeOriginalConcentratedPairGraph NativeOriginalConcentratedSlabExclusion

/-- Original heavy-slice deletion and the proved original-source
concentrated-graph contradiction construct the actual surviving graph.
Every surviving pair has many literal original heavy nonconcentrated slices. -/
theorem exists_original_nonconcentrated_slice_graph_cutoff
    (zeta gamma A epsilon eps2 D L eta e2 Cslab : ℝ)
    (hgap : gamma < zeta) (hgamma : gamma < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (_heps2 : 0 < eps2) (hD : 0 ≤ D) (hL : 0 < L)
    (heta : 0 < eta) (he2 : 0 < e2) (he2small : 200*e2 ≤ epsilon) (hCslab : 0 ≤ Cslab)
    (hetagain : eta ≤ (zeta-gamma)/2)
    (hscale : 2*eta+(51/50:ℝ)*epsilon < (zeta-gamma)/(4*(1-gamma)))
    (hwidth : (L+10+D)*eta+(1+200/epsilon)*e2 ≤ (149/10000:ℝ)*epsilon)
    (hmass : (10*L+119+14*D)*eta+14*((1+200/epsilon)*e2) ≤ eps2) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1/2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ) (n : ℕ),
        P.Nonempty → delta ≤ rho → rho ≤ 1 → rho=dyadicRadius n →
        G⊆P.product P →
        (∀ p∈P, ∀ j, |p j| ≤ 1) →
        (∀ z∈G, delta^(2*eta) ≤ distance3 z.1 z.2) →
        (∀ p∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
          ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card) →
        (∀ z∈G, delta^(-(zeta-gamma))*rho^(2-gamma)*P.card ≤
          A*(physicalPairTube3 P rho z).card) →
        (∀ normal : Point3, ∀ c : ℝ, (∑ j, normal j^2)=1 →
          ((P.filter (fun x => |(∑ j, normal j*x j)-c| ≤ delta^epsilon/2)).card : ℝ) ≤
            Cslab*delta^eps2*P.card) →
        let r := delta^(2*eta)
        let Delta := 54*rho/r
        let e1 := sliceExponent delta Delta epsilon
        let G2 := retainedPairs P G rho (rho^(1+D*eta)*P.card)
        let C := concentratedPairGraph P G2 rho r (D*eta) e1 e2 (1/4)
        let G4 := G2\C
        G4⊆G ∧
          (G.card : ℝ) ≤ G4.card+(216*rho^(D*eta)+delta^(L*eta))*(P.card : ℝ)^2 ∧
          ∀ z∈G4,
            let F := concentratedDirections P rho r (D*eta) e1 e2 z
            let U := goodDirections P rho (rho^(1+D*eta)*P.card) z\F
            let k := chosenHeavySlabCode P rho (rho^(1+D*eta)*P.card) z
            1 ≤ 4*rho*(U.card : ℝ) ∧
              ∀ d∈U, k d∈P.image (slabCode rho d) ∧
                rho^(1+D*eta)*(P.card : ℝ) ≤ (slabPoints P rho d (k d)).card ∧
                z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d) ∧
                ((physicalPairTube3 (enlargedSlice P rho d (k d) Delta) (Delta^e1) z).card : ℝ) ≤
                  Delta^e2*(enlargedSlice P rho d (k d) Delta).card := by
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_original_concentrated_graph_cutoff
    zeta gamma A epsilon eps2 D L eta e2 Cslab hgap hgamma hA hepsilon _heps2 hD hL
    heta he2 he2small hCslab hetagain hscale hwidth hmass
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall P G rho n hP hquery hrho1 hmesh hGP hbox hsep hfrostman hgain hslab
  let r := delta^(2*eta)
  let Delta := 54*rho/r
  let e1 := sliceExponent delta Delta epsilon
  let G2 := retainedPairs P G rho (rho^(1+D*eta)*P.card)
  let C := concentratedPairGraph P G2 rho r (D*eta) e1 e2 (1/4)
  let G4 := G2\C
  have hrho : 0 < rho := hd.trans_le hquery
  have hr : 0 < r := by dsimp [r]; positivity
  have hne : ∀ z∈G,z.1≠z.2 := by
    intro z hz heq
    have hh := hsep z hz
    rw [heq] at hh
    simp only [distance3,sub_self,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_zero] at hh
    exact (not_le_of_gt hr) hh
  obtain ⟨hG2,hheavy,_hgood⟩ := original_heavy_slice_graph P G rho (rho^(1+D*eta)*P.card)
    hrho hrho1 (by positivity) hGP hbox hne
  have hheavy' : (G.card : ℝ) ≤ G2.card+216*rho^(D*eta)*(P.card : ℝ)^2 := by
    have hid : 216*(rho^(1+D*eta)*(P.card : ℝ))*P.card/rho=
        216*rho^(D*eta)*(P.card : ℝ)^2 := by
      rw [Real.rpow_add hrho,Real.rpow_one]
      field_simp
    simpa only [hid] using hheavy
  have hC : (C.card : ℝ) < delta^(L*eta)*(P.card : ℝ)^2 := hcut delta hd hsmall P G2 rho n
    hP hquery hrho1 hmesh (hG2.trans hGP) hbox (fun z hz => hsep z (hG2 hz))
    hfrostman (fun z hz => hgain z (hG2 hz)) hslab
  have hCG2 : C⊆G2 := Finset.filter_subset _ _
  have hpartition : (G4.card : ℝ)+C.card=G2.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hCG2
  refine ⟨(Finset.sdiff_subset).trans hG2,?_,?_⟩
  · change (G.card : ℝ) ≤ G4.card+(216*rho^(D*eta)+delta^(L*eta))*(P.card : ℝ)^2
    nlinarith only [hheavy',hC.le,hpartition]
  · intro z hz
    obtain ⟨hz2,hzC⟩ := Finset.mem_sdiff.mp hz
    exact retained_unconcentrated_direction_population P G rho r (D*eta) e1 e2 z hz2 hzC

end NativeOriginalNonconcentratedSliceGraph


namespace NativeOriginalNonconcentratedSliceGraph
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalPhysicalTubeScaleSelection OriginalThreeDimensionalSliceParameterChoice
open OriginalThreeDimensionalConcentratedBudget NativeOriginalConcentratedPairGraph

/-- All internal exponents and cutoffs are selected before the original
mesh and source. The endpoint constructs the actual Steps 1--2 graph
from original ball, rich-tube, separation, and finite-cover slab data. -/
theorem exists_native_original_two_ends_threshold
    (zeta A epsilon eps2 D L etaUpper Cslab : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100) (heps2 : 0 < eps2)
    (hD : 0 ≤ D) (hL : 0 < L) (hupper : 0 < etaUpper) (hCslab : 0 ≤ Cslab) :
    ∃ e2 : ℝ, 0 < e2 ∧ 200*e2 ≤ epsilon ∧ ∃ eta : ℝ, 0 < eta ∧ eta ≤ etaUpper ∧
      ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1/2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ) (n : ℕ),
        P.Nonempty → delta ≤ rho → rho ≤ 1 → rho=dyadicRadius n →
        G⊆P.product P →
        (∀ p∈P, ∀ j, |p j| ≤ 1) →
        (∀ z∈G, delta^(2*eta) ≤ distance3 z.1 z.2) →
        (∀ p∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
          ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card) →
        (∀ z∈G, delta^(-(zeta-zeta/100))*rho^(2-zeta/100)*P.card ≤
          A*(physicalPairTube3 P rho z).card) →
        (∀ normal : Point3, ∀ c : ℝ, (∑ j, normal j^2)=1 →
          ((P.filter (fun x => |(∑ j, normal j*x j)-c| ≤ delta^epsilon/2)).card : ℝ) ≤
            Cslab*delta^eps2*P.card) →
        let r := delta^(2*eta)
        let Delta := 54*rho/r
        let e1 := sliceExponent delta Delta epsilon
        let G2 := retainedPairs P G rho (rho^(1+D*eta)*P.card)
        let C := concentratedPairGraph P G2 rho r (D*eta) e1 e2 (1/4)
        let G4 := G2\C
        G4⊆G ∧
          (G.card : ℝ) ≤ G4.card+(216*rho^(D*eta)+delta^(L*eta))*(P.card : ℝ)^2 ∧
          ∀ z∈G4,
            let F := concentratedDirections P rho r (D*eta) e1 e2 z
            let U := goodDirections P rho (rho^(1+D*eta)*P.card) z\F
            let k := chosenHeavySlabCode P rho (rho^(1+D*eta)*P.card) z
            1 ≤ 4*rho*(U.card : ℝ) ∧
              ∀ d∈U, k d∈P.image (slabCode rho d) ∧
                rho^(1+D*eta)*(P.card : ℝ) ≤ (slabPoints P rho d (k d)).card ∧
                z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d) ∧
                ((physicalPairTube3 (enlargedSlice P rho d (k d) Delta) (Delta^e1) z).card : ℝ) ≤
                  Delta^e2*(enlargedSlice P rho d (k d) Delta).card := by
  obtain ⟨e2,he2,he2small,eta,heta,hetaup,hetagain,hscale,hwidth,hmass⟩ :=
    exists_original_concentrated_parameter_budget zeta epsilon eps2 D L etaUpper
      hzeta hzeta1 hepsilon hepsmall heps2 hD hL hupper
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_original_nonconcentrated_slice_graph_cutoff
    zeta (zeta/100) A epsilon eps2 D L eta e2 Cslab
    (by linarith only [hzeta]) (by linarith only [hzeta1]) hA hepsilon heps2 hD hL
    heta he2 he2small hCslab hetagain hscale hwidth hmass
  exact ⟨e2,he2,he2small,eta,heta,hetaup,delta0,hd0,hd01,hcut⟩

end NativeOriginalNonconcentratedSliceGraph


namespace NativeOriginalNonconcentratedSliceGraph
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalSliceMaximizer
open OriginalPhysicalTubeScaleSelection OriginalThreeDimensionalSliceParameterChoice
open NativeOriginalConcentratedPairGraph OriginalThreeDimensionalLiteralSlabCover

/-- The literal finite oriented epsilon-width by one by one slab premise
supplies the original source cap through a proved 49-rectangle cover.
Every internal exponent and cutoff still precedes the original source. -/
theorem exists_literal_original_two_ends_threshold
    (zeta A epsilon eps2 D L etaUpper : ℝ)
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hA : 0 < A)
    (hepsilon : 0 < epsilon) (hepsmall : epsilon ≤ zeta/100) (heps2 : 0 < eps2)
    (hD : 0 ≤ D) (hL : 0 < L) (hupper : 0 < etaUpper) :
    ∃ e2 : ℝ, 0 < e2 ∧ 200*e2 ≤ epsilon ∧ ∃ eta : ℝ, 0 < eta ∧ eta ≤ etaUpper ∧
      ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1/2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ (P : Finset Point3) (G : Finset Pair3) (rho : ℝ) (n : ℕ),
        P.Nonempty → delta ≤ rho → rho ≤ 1 → rho=dyadicRadius n →
        G⊆P.product P →
        (∀ p∈P, ∀ j, |p j| ≤ 1) →
        (∀ z∈G, delta^(2*eta) ≤ distance3 z.1 z.2) →
        (∀ p∈P, ∀ R : ℝ, delta ≤ R → R ≤ 1 →
          ((P.filter (fun q => distance3 p q ≤ R)).card : ℝ) ≤ delta^(-eta)*R^2*P.card) →
        (∀ z∈G, delta^(-(zeta-zeta/100))*rho^(2-zeta/100)*P.card ≤
          A*(physicalPairTube3 P rho z).card) →
        (∀ frame : OriginalThreeDimensionalLiteralSlabCover.Frame3, ∀ c : ℝ, ∀ k : ℤ×ℤ,
          ((P.filter (fun x => x∈OriginalThreeDimensionalLiteralSlabCover.rectangle
            frame c (delta^epsilon/2) k)).card : ℝ) ≤ delta^eps2*P.card) →
        let r := delta^(2*eta)
        let Delta := 54*rho/r
        let e1 := sliceExponent delta Delta epsilon
        let G2 := retainedPairs P G rho (rho^(1+D*eta)*P.card)
        let C := concentratedPairGraph P G2 rho r (D*eta) e1 e2 (1/4)
        let G4 := G2\C
        G4⊆G ∧
          (G.card : ℝ) ≤ G4.card+(216*rho^(D*eta)+delta^(L*eta))*(P.card : ℝ)^2 ∧
          ∀ z∈G4,
            let F := concentratedDirections P rho r (D*eta) e1 e2 z
            let U := goodDirections P rho (rho^(1+D*eta)*P.card) z\F
            let k := chosenHeavySlabCode P rho (rho^(1+D*eta)*P.card) z
            1 ≤ 4*rho*(U.card : ℝ) ∧
              ∀ d∈U, k d∈P.image (slabCode rho d) ∧
                rho^(1+D*eta)*(P.card : ℝ) ≤ (slabPoints P rho d (k d)).card ∧
                z.1∈slabPoints P rho d (k d) ∧ z.2∈slabPoints P rho d (k d) ∧
                ((physicalPairTube3 (enlargedSlice P rho d (k d) Delta) (Delta^e1) z).card : ℝ) ≤
                  Delta^e2*(enlargedSlice P rho d (k d) Delta).card := by
  obtain ⟨e2,he2,he2small,eta,heta,hetaup,delta0,hd0,hd01,hcut⟩ :=
    exists_native_original_two_ends_threshold zeta A epsilon eps2 D L etaUpper 49
      hzeta hzeta1 hA hepsilon hepsmall heps2 hD hL hupper (by norm_num)
  refine ⟨e2,he2,he2small,eta,heta,hetaup,delta0,hd0,hd01,?_⟩
  intro delta hd hsmall P G rho n hP hquery hrho1 hmesh hGP hbox hsep hfrostman hgain hrect
  apply hcut delta hd hsmall P G rho n hP hquery hrho1 hmesh hGP hbox hsep hfrostman hgain
  intro normal c hunit
  have hh := original_unit_slab_from_literal_rectangles P (delta^epsilon/2)
    (delta^eps2*P.card) hbox hrect normal hunit c
  simpa only [mul_assoc] using hh

end NativeOriginalNonconcentratedSliceGraph
