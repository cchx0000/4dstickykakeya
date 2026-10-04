import Theorems.Thm_StickyKakeya4_original_angular_frostman
import Theorems.Thm_StickyKakeya4_planar_abc_balanced_normalization
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalAngularBalancedFrostman
open Classical FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open OriginalAngularAlphabetTranslation OriginalAngularFrostman
open PlanarABCBalancedNormalization
/-- The only final C normalization is its explicit fixed factor2, after
 retaining and translating the whole original source angular alphabet. -/
def balancedC (Phi : Finset ℝ) (anchor : ℝ) : Finset ℝ := (shifted Phi anchor).image scalar
lemma balancedC_card (Phi : Finset ℝ) (anchor : ℝ) : (balancedC Phi anchor).card=Phi.card := by
  rw [balancedC,Finset.card_image_of_injective _ scalar_injective,shifted_card]
lemma balancedC_box (Phi : Finset ℝ) (anchor : ℝ) (ha : anchor ∈ Phi)
    (hbox : ∀ phi ∈ Phi, |phi| ≤ 1) : ∀ c ∈ balancedC Phi anchor, |c| ≤ 1 := by
  intro c hc
  obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp hc
  exact scalar_box old (shifted_box Phi anchor ha hbox old hold)
lemma balancedC_separated (Phi : Finset ℝ) (anchor : ℝ) {mesh : ℝ} (hsep : Separated Phi mesh) :
    Separated (balancedC Phi anchor) (mesh/2) := by
  intro x hx y hy hxy
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
  have hpq : p ≠ q := by intro h; subst q; exact hxy rfl
  have hh := shifted_separated Phi anchor hsep p hp q hq hpq
  change mesh/2 ≤ |p/2-q/2|
  rw [← sub_div,abs_div]
  change mesh ≤ |p-q| at hh
  norm_num
  linarith
lemma balancedC_ball_card (Phi : Finset ℝ) (anchor center r : ℝ) :
    (carrierBall (balancedC Phi anchor) center r).card=(carrierBall (shifted Phi anchor) (2*center) (2*r)).card := by
  have hiff (p : ℝ) : dist (scalar p) center ≤ r ↔ dist p (2*center) ≤ 2*r := by
    change |p/2-center| ≤ r ↔ |p-2*center| ≤ 2*r
    have hid : p/2-center=(p-2*center)/2 := by ring
    rw [hid,abs_div]
    norm_num
    constructor <;> intro h <;> linarith
  have hid : carrierBall (balancedC Phi anchor) center r=
      (carrierBall (shifted Phi anchor) (2*center) (2*r)).image scalar := by
    ext c
    constructor
    · intro hc
      obtain ⟨hcC,hcd⟩ := (mem_carrierBall _ _ _ _).mp hc
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hcC
      exact Finset.mem_image.mpr ⟨p,(mem_carrierBall _ _ _ _).mpr ⟨hp,(hiff p).mp hcd⟩,rfl⟩
    · intro hc
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hpC,hpd⟩ := (mem_carrierBall _ _ _ _).mp hp
      exact (mem_carrierBall _ _ _ _).mpr ⟨Finset.mem_image_of_mem _ hpC,(hiff p).mpr hpd⟩
  rw [hid]
  exact Finset.card_image_of_injective _ scalar_injective
/-- Final unit-box C has its derived relative Frostman law at the COMMON
 finer ABC mesh. The original/coarse mesh ratio remains explicit. -/
theorem balancedC_frostman (Phi : Finset ℝ) (anchor : ℝ) {mesh abcMesh K kappa : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (habc : 0 < abcMesh) (hscale : 2*abcMesh ≤ mesh)
    (hK : 1 ≤ K) (hk : 0 ≤ kappa) (hAD : ADBounds Phi mesh K kappa)
    (center r : ℝ) (hr : abcMesh ≤ r) :
    ((carrierBall (balancedC Phi anchor) center r).card : ℝ) ≤
      ((2:ℝ)^kappa*((2:ℝ)^kappa*K^2*(mesh/(2*abcMesh))^kappa))*r^kappa*((balancedC Phi anchor).card : ℝ) := by
  rw [balancedC_ball_card]
  have hc := shifted_finer_mesh_frostman Phi anchor hm hm1 (by positivity : 0 < 2*abcMesh)
    hscale hK hk hAD (2*center) (2*r) (by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (habc.le.trans hr)] at hc
  rw [balancedC_card,shifted_card] at *
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hc
/-- Only the upper Frostman exponent is weakened for a uniform ABC cutoff;
 the original C cardinality and its original exponent are not changed. -/
theorem weaken_upper_exponent {count population constant r kappa fixedExponent : ℝ}
    (hpopulation : 0 ≤ population) (hconstant : 0 ≤ constant) (hr : 0 < r) (hr1 : r ≤ 1)
    (hexponent : fixedExponent ≤ kappa) (hbound : count ≤ constant*r^kappa*population) :
    count ≤ constant*r^fixedExponent*population := by
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1 hexponent) hconstant) hpopulation)
end OriginalAngularBalancedFrostman
