import Theorems.Thm_StickyKakeya4_original_three_dimensional_small_slice_branch
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_frostman
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeThreeDimensionalSmallSlice
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSliceMaximizer OriginalThreeDimensionalSmallSliceBranch
open OriginalThreeDimensionalTubeFrostman OriginalPhysicalTubeScaleSelection NativeQuarterScaleParameters

/-- One contraction index is fixed before the source and works throughout
the permitted range of the subsequently selected slicing exponent. -/
theorem exists_uniform_original_slice_contraction (e2 e1hi : ℝ)
    (he2 : 0<e2) (hhi : 0<e1hi) :
    ∃ M : ℕ, ∀ e1 : ℝ, 0<e1 → e1≤e1hi →
      (dyadicRadius M)^(200*e2/e1)≤1/2 := by
  let a := 200*e2/e1hi
  have ha : 0<a := by dsimp [a]; positivity
  let M := Nat.ceil (1/a)
  have hM : 1/a≤(M:ℝ) := Nat.le_ceil _
  have hMa : 1≤(M:ℝ)*a := by
    have hh := mul_le_mul_of_nonneg_right hM ha.le
    have he : (1/a)*a=1 := by field_simp
    rw [he] at hh
    exact hh
  have hp : 0<dyadicRadius M := by dsimp [dyadicRadius]; positivity
  have hp1 : dyadicRadius M≤1 := by dsimp [dyadicRadius]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hc : (dyadicRadius M)^a≤1/2 := by
    dsimp [dyadicRadius]
    rw [← Real.rpow_natCast (1/2:ℝ) M,← Real.rpow_mul (by norm_num : (0:ℝ)≤1/2)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)≤1) hMa
  refine ⟨M,?_⟩
  intro e1 he1 he1hi
  have hexp : a≤200*e2/e1 := div_le_div_of_nonneg_left (by positivity) he1 he1hi
  exact (Real.rpow_le_rpow_of_exponent_ge hp hp1 hexp).trans hc

/-- The original 2-Frostman rich-tube input supplies the upper physical
slice width at a genuine cutoff. All contraction and width cutoffs are
fixed before the actual source, radius and variable slicing exponent.
The selected small-tau branch has an actual original tube population;
the large-tau branch retains its original annular half-mass for geometry. -/
theorem exists_native_original_small_slice_threshold
    (zeta gamma A eta e1lo e1hi e2 : ℝ)
    (hgap : gamma<zeta) (hgamma : gamma<1) (hA : 0<A)
    (heta : 0<eta) (hetagain : eta≤(zeta-gamma)/2)
    (hetascale : eta≤(zeta-gamma)/(16*(1-gamma)))
    (hlo : 0<e1lo) (hlohi : e1lo≤e1hi) (hhi1 : e1hi≤1)
    (he2 : 0<e2) (he2small : 200*e2≤e1lo) :
    ∃ M : ℕ, ∃ delta0 : ℝ, 0<delta0 ∧ delta0≤1 ∧
      ∀ delta : ℝ, 0<delta → delta≤delta0 →
      ∀ e1 : ℝ, e1lo≤e1 → e1≤e1hi →
      ∀ (P : Finset Point3) (z : Pair3) (rho eta1 : ℝ) (d : DirectionLabel) (k : ℤ) (n : ℕ),
        P.Nonempty → delta≤rho → rho≤1 → rho=dyadicRadius n →
        (∀ p∈P, ∀ i, |p i|≤1) →
        (∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
          ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) →
        delta^(-(zeta-gamma))*rho^(2-gamma)*P.card≤A*(physicalPairTube3 P rho z).card →
        rho^(1+eta1)*(P.card : ℝ)≤(slabPoints P rho d k).card →
        (54*rho/delta^(2*eta))^e2*((enlargedSlice P rho d k (54*rho/delta^(2*eta))).card : ℝ)≤
          (physicalPairTube3 (enlargedSlice P rho d k (54*rho/delta^(2*eta)))
            ((54*rho/delta^(2*eta))^e1) z).card →
        let r := delta^(2*eta)
        let D := 54*rho/r
        let Q := enlargedSlice P rho d k D
        let alpha := 200*e2/e1
        let nu := r^2/108*rho^eta1*D^(e2+alpha*(1-e1))
        rho≤delta^((zeta-gamma)/(4*(1-gamma))) ∧ 0<D ∧ D≤1 ∧
        0<alpha ∧ alpha≤1 ∧ 0<nu ∧
        ∃ j : ℕ, j≤n ∧
          (∀ i≤n, sliceScore Q z alpha (dyadicRadius i)≤ sliceScore Q z alpha (dyadicRadius j)) ∧
          D^e2*(dyadicRadius j)^alpha≤(2*D^e1)^alpha ∧
          (dyadicRadius j≤D → nu*dyadicRadius j*P.card≤(physicalPairTube3 P (dyadicRadius j) z).card) ∧
          (D<dyadicRadius j → j+M≤n ∧
            ((physicalPairTube3 Q (dyadicRadius j) z).card : ℝ)/2≤
              ((physicalPairTube3 Q (dyadicRadius j) z\physicalPairTube3 Q (dyadicRadius (j+M)) z).card : ℝ)) := by
  let kappa := (zeta-gamma)/(4*(1-gamma))
  have hg : 0<zeta-gamma := sub_pos.mpr hgap
  have hb : 0<1-gamma := sub_pos.mpr hgamma
  have hkappa : 0<kappa := by dsimp [kappa]; positivity
  have hetaK : eta≤kappa/4 := by
    have he : (zeta-gamma)/(16*(1-gamma))=kappa/4 := by dsimp [kappa]; field_simp; ring
    simpa only [he] using hetascale
  have hexp : 0<kappa-2*eta := by linarith only [hetaK,hkappa]
  obtain ⟨M,hcontract⟩ := exists_uniform_original_slice_contraction e2 e1hi he2 (hlo.trans_le hlohi)
  have hc : 0<dyadicRadius M := by dsimp [dyadicRadius]; positivity
  obtain ⟨dS,hdS,hdS1,hscale⟩ := exists_original_rich_tube_scale_cutoff zeta gamma A hgap hgamma hA
  obtain ⟨dR,hdR,_hdR1,hrcut⟩ := exists_small_power_cutoff
    (show 0<2*eta by positivity) (show 0<54*dyadicRadius M by positivity)
  obtain ⟨dD,hdD,_hdD1,hDcut⟩ := exists_small_power_cutoff hexp (by norm_num : (0:ℝ)<1/54)
  refine ⟨M,min dS (min dR dD),lt_min hdS (lt_min hdR hdD),(min_le_left _ _).trans hdS1,?_⟩
  intro delta hd hsmall e1 he1lo he1hi P z rho eta1 d k n hP hquery hrho1 hmesh hbox hfrostman hgain hheavy hconcentration
  have hsmallS := hsmall.trans (min_le_left _ _)
  have hsmallR := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallD := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 := hsmallS.trans hdS1
  have hrho : 0<rho := hd.trans_le hquery
  have he1 : 0<e1 := hlo.trans_le he1lo
  have he11 : e1≤1 := he1hi.trans hhi1
  have ha : 0<200*e2/e1 := by positivity
  have ha1 : 200*e2/e1≤1 := (div_le_one he1).mpr (he2small.trans he1lo)
  have hdecay := hscale delta hd hsmallS eta heta.le hetagain P z rho hP hquery hrho1 hbox hfrostman hgain
  change rho≤delta^kappa at hdecay
  let r := delta^(2*eta)
  let D := 54*rho/r
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r≤1 := Real.rpow_le_one hd.le hd1 (by positivity : 0≤2*eta)
  have hD : 0<D := by dsimp [D]; positivity
  have hDpower : D≤54*delta^(kappa-2*eta) := by
    rw [Real.rpow_sub hd]
    dsimp [D,r]
    have hh := div_le_div_of_nonneg_right hdecay (Real.rpow_nonneg hd.le (2*eta))
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤54)
    simpa only [mul_div_assoc] using hh'
  have hD1 : D≤1 := by
    have hh := mul_le_mul_of_nonneg_left (hDcut delta hd hsmallD) (by norm_num : (0:ℝ)≤54)
    norm_num only [mul_one_div,div_self (by norm_num : (54:ℝ)≠0)] at hh
    exact hDpower.trans hh
  have hnu : 0<r^2/108*rho^eta1*D^(e2+(200*e2/e1)*(1-e1)) := by positivity
  refine ⟨hdecay,hD,hD1,ha,ha1,hnu,?_⟩
  exact exists_original_concentrated_slice_radius P z rho r eta1 e1 e2 d k n M
    hrho hr hr1 he1 he11 he2 ha1 hmesh (hcontract e1 he1 he1hi)
    (hrcut delta hd hsmallR) hD1 hP hheavy hconcentration

end NativeThreeDimensionalSmallSlice
