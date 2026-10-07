import Theorems.Thm_StickyKakeya4_native_slice_menu_ball_join
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

noncomputable section
namespace NativeSliceADConstant
open Classical Finset NativeSliceRadiusInterpolation FiniteVoronoiRealADCoarsening

/-- One AD constant retaining both independently derived class coefficients. -/
def constant (lower upper B s : ℝ) : ℝ :=
  max 1 (max (B^s/lower) (729*upper*B^s))

lemma one_le_constant (lower upper B s : ℝ) : 1 ≤ constant lower upper B s := le_max_left _ _

/-- Turn actual asymmetric closed-ball populations into the existing
real-dimensional ADBounds API. No regularity property is an input. -/
theorem ADBounds_of_asymmetric_counts {X : Type*} [PseudoMetricSpace X]
    (P : Finset X) (mesh lower upper B s : ℝ) (hmesh : 0 < mesh) (hlower : 0 < lower)
    (H : ∀x∈P,∀r : ℝ,mesh ≤ r → r ≤ 1 →
      lower*(r/mesh)^s ≤ B^s*ballCount P x r ∧
        ballCount P x r ≤ 729*upper*B^s*(r/mesh)^s) :
    ADBounds P mesh (constant lower upper B s) s := by
  intro x hx r hr hr1
  have hh := H x hx r hr hr1
  have hK : 0 < constant lower upper B s := lt_of_lt_of_le (by norm_num) (one_le_constant _ _ _ _)
  have hlo : B^s/lower ≤ constant lower upper B s :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hhi : 729*upper*B^s ≤ constant lower upper B s :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hmass : 0 ≤ ballCount P x r := Nat.cast_nonneg _
  have hpower : 0 ≤ (r/mesh)^s := by have hrpos := hmesh.trans_le hr; positivity
  have hlow : (r/mesh)^s ≤ (B^s/lower)*ballCount P x r := by
    calc
      _ ≤ (B^s*ballCount P x r)/lower := (le_div_iff₀ hlower).mpr (by simpa only [mul_comm] using hh.1)
      _ = _ := by ring
  have hlow' : (r/mesh)^s/(constant lower upper B s) ≤ ballCount P x r :=
    (div_le_iff₀ hK).mpr (by
      simpa only [mul_comm] using hlow.trans (mul_le_mul_of_nonneg_right hlo hmass))
  have hhigh : ballCount P x r ≤ constant lower upper B s*(r/mesh)^s :=
    hh.2.trans (mul_le_mul_of_nonneg_right hhi hpower)
  exact ⟨hlow',hhigh⟩

end NativeSliceADConstant
