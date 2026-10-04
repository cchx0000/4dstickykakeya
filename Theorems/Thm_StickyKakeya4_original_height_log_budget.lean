import Theorems.Thm_StickyKakeya4_original_angular_exponent_range
import Theorems.Thm_StickyKakeya4_native_original_log_budget
import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
namespace OriginalHeightLogBudget
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening DyadicOriginalFiberSelection
open OriginalAngularExponentRange NativeOriginalLogBudget NativeQuarterScaleParameters

/-- The actual original graph-height level count has a logarithmic envelope,
derived from one-dimensional separation and the original bounded source. -/
theorem original_height_level_count_log_envelope (Z : Finset ℝ) (hZ : Z.Nonempty)
    {delta : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hsep : Separated Z delta) (hbox : ∀ z ∈ Z, |z| ≤ 1) :
    (levelCount Z : ℝ) ≤ 3+(1/Real.log 2)*(-Real.log delta) := by
  have hcard : 0 < (Z.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hZ
  have hpack := original_angular_card_upper Z hd hd1 hsep hbox
  have hlog := Real.log_le_log hcard hpack
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 2
    norm_num at hh
    exact hh
  rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hd.ne', hlog4] at hlog
  have hnat : (Nat.log 2 Z.card : ℝ) ≤ Real.log (Z.card : ℝ)/Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb Z.card 2
  have hreal := div_le_div_of_nonneg_right hlog hlog2.le
  have hid : (2*Real.log 2-Real.log delta)/Real.log 2+1 =
      3+(1/Real.log 2)*(-Real.log delta) := by
    field_simp
    ring
  calc
    (levelCount Z : ℝ) = (Nat.log 2 Z.card : ℝ)+1 := by
      simp only [levelCount, Nat.cast_add, Nat.cast_one]
    _ ≤ (2*Real.log 2-Real.log delta)/Real.log 2+1 := by linarith only [hnat,hreal]
    _ = _ := hid

/-- A cutoff selected before the original height source absorbs its actual
dyadic level count. Neither AD bounds nor a population conclusion is a premise. -/
theorem exists_original_height_budget_cutoff {eta : ℝ} (heta : 0 < eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta : ℝ,
      0 < delta → delta ≤ delta0 → ∀ Z : Finset ℝ, Z.Nonempty →
      Separated Z delta → (∀ z ∈ Z, |z| ≤ 1) →
      (levelCount Z : ℝ) ≤ delta^(-eta) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨d0,hd0,hd01,hcut⟩ := exists_logarithmic_budget_cutoff heta
    (by norm_num : (0 : ℝ) ≤ 3) (by positivity : (0 : ℝ) ≤ 1/Real.log 2)
  refine ⟨d0,hd0,hd01,?_⟩
  intro delta hd hsmall Z hZ hsep hbox
  exact (original_height_level_count_log_envelope Z hZ hd
    (hsmall.trans hd01) hsep hbox).trans (hcut delta hd hsmall)

/-- One original cutoff absorbs both fixed coefficients, the actual height
level count, and the constructed projection menu, before any source or radius
is chosen. The projection premise is its finite construction's log estimate. -/
theorem exists_original_source_budget_cutoff {eta C0 : ℝ}
    (heta : 0 < eta) (hC0 : 1 ≤ C0) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ ∀ delta : ℝ,
      0 < delta → delta ≤ delta0 →
      C0 ≤ delta^(-eta) ∧ (5101248 : ℝ) ≤ delta^(-eta) ∧
      (∀ Z : Finset ℝ, Z.Nonempty → Separated Z delta →
        (∀ z ∈ Z, |z| ≤ 1) → (levelCount Z : ℝ) ≤ delta^(-eta)) ∧
      (∀ rho N : ℝ, delta^(1/2 : ℝ) ≤ rho →
        N ≤ Real.log (2/rho)/Real.log 2+2 → N ≤ delta^(-eta)) := by
  let C : ℝ := C0+5101248
  have hC : 0 < C := by dsimp [C]; linarith only [hC0]
  obtain ⟨dC,hdC,hdC1,hfixed⟩ := exists_small_power_cutoff heta
    (div_pos (by norm_num : (0 : ℝ) < 1) hC)
  obtain ⟨dH,hdH,_hdH1,hheight⟩ := exists_original_height_budget_cutoff heta
  obtain ⟨dP,hdP,_hdP1,hprojection⟩ := exists_projection_menu_budget_cutoff heta
  refine ⟨min dC (min dH dP),lt_min hdC (lt_min hdH hdP),
    (min_le_left _ _).trans hdC1,?_⟩
  intro delta hd hsmall
  have hsmallC : delta ≤ dC := hsmall.trans (min_le_left _ _)
  have hsmallH : delta ≤ dH :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallP : delta ≤ dP :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpower := hfixed delta hd hsmallC
  have hproduct : delta^eta*C ≤ 1 := (le_div_iff₀ hC).mp hpower
  have hreciprocal : C ≤ 1/delta^eta :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hd eta)).mpr (by nlinarith only [hproduct])
  have hbound : C ≤ delta^(-eta) := by
    simpa only [Real.rpow_neg hd.le,one_div] using hreciprocal
  have hC0C : C0 ≤ C := by dsimp [C]; linarith
  have hconstantC : (5101248 : ℝ) ≤ C := by dsimp [C]; linarith only [hC0]
  exact ⟨hC0C.trans hbound,hconstantC.trans hbound,
    hheight delta hd hsmallH,fun rho N hrho hN =>
      hprojection delta rho N hd hsmallP hrho hN⟩

end OriginalHeightLogBudget
