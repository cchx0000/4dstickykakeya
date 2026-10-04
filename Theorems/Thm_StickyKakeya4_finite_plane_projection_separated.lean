import Theorems.Thm_StickyKakeya4_finite_plane_projection_native_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- A fixed nine-color partition of literal planar integer cells. -/
def cellColor (k : ℤ × ℤ) : ℤ × ℤ := (k.1 % 3, k.2 % 3)

def nineColors : Finset (ℤ × ℤ) := Finset.Icc 0 2 ×ˢ Finset.Icc 0 2

lemma cellColor_mem (k : ℤ × ℤ) : cellColor k ∈ nineColors := by
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_Icc.mpr
  · have hlo := Int.emod_nonneg k.1 (by norm_num : (3 : ℤ) ≠ 0)
    have hhi := Int.emod_lt_of_pos k.1 (by norm_num : (0 : ℤ) < 3)
    dsimp [cellColor]
    omega
  · have hlo := Int.emod_nonneg k.2 (by norm_num : (3 : ℤ) ≠ 0)
    have hhi := Int.emod_lt_of_pos k.2 (by norm_num : (0 : ℤ) < 3)
    dsimp [cellColor]
    omega

lemma nineColors_card : nineColors.card = 9 := by
  simp only [nineColors, Finset.card_product, Int.card_Icc]
  rfl

/-- An actual color class retains at least a ninth of the original labels. -/
lemma exists_cell_color {X : Type*} (P : Finset X) (cell : X → ℤ × ℤ) :
    ∃ color ∈ nineColors, ∃ Q : Finset X, Q ⊆ P ∧ P.card ≤ 9 * Q.card ∧
      ∀ i ∈ Q, cellColor (cell i) = color := by
  let population := fun c => (P.filter (fun i => cellColor (cell i) = c)).card
  have hnon : nineColors.Nonempty := ⟨cellColor (0, 0), cellColor_mem _⟩
  obtain ⟨color, hcolor, hmax⟩ := Finset.exists_max_image nineColors population hnon
  have hsum : P.card = ∑ c ∈ nineColors, population c :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => cellColor_mem (cell i))
  have hcard : P.card ≤ 9 * population color := by
    calc
      _ = ∑ c ∈ nineColors, population c := hsum
      _ ≤ ∑ _c ∈ nineColors, population color := Finset.sum_le_sum (fun c hc => hmax c hc)
      _ = _ := by simp [nineColors_card]
  exact ⟨color, hcolor, P.filter (fun i => cellColor (cell i) = color),
    Finset.filter_subset _ _, hcard, fun i hi => (Finset.mem_filter.mp hi).2⟩

lemma same_residue_floor_separation {x y rho : ℝ} (hrho : 0 < rho)
    (hmod : ⌊x / rho⌋ % 3 = ⌊y / rho⌋ % 3) (hne : ⌊x / rho⌋ ≠ ⌊y / rho⌋) :
    2 * rho < |x - y| := by
  have hxlo := (le_div_iff₀ hrho).mp (Int.floor_le (x / rho))
  have hxhi := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one (x / rho))
  have hylo := (le_div_iff₀ hrho).mp (Int.floor_le (y / rho))
  have hyhi := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one (y / rho))
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hgap : ⌊x / rho⌋ + 3 ≤ ⌊y / rho⌋ := by omega
    have hgap' : (⌊x / rho⌋ : ℝ) + 3 ≤ (⌊y / rho⌋ : ℝ) := by exact_mod_cast hgap
    have hmul := mul_le_mul_of_nonneg_right hgap' hrho.le
    have hd : 2 * rho < y - x := by nlinarith
    exact hd.trans_le (by simpa only [abs_sub_comm] using le_abs_self (y - x))
  · have hgap : ⌊y / rho⌋ + 3 ≤ ⌊x / rho⌋ := by omega
    have hgap' : (⌊y / rho⌋ : ℝ) + 3 ≤ (⌊x / rho⌋ : ℝ) := by exact_mod_cast hgap
    have hmul := mul_le_mul_of_nonneg_right hgap' hrho.le
    have hd : 2 * rho < x - y := by nlinarith
    exact hd.trans_le (le_abs_self (x - y))

/-- Deterministic thinning separates actual projected positions; no point is
moved to a cell center and no projection is changed. -/
theorem exists_separated_projection_subset {X : Type*} (P : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) {rho : ℝ} (hrho : 0 < rho)
    (hinj : Set.InjOn (fun i => projectedCell uv rho (p i)) (↑P)) :
    ∃ Q : Finset X, Q ⊆ P ∧ P.card ≤ 9 * Q.card ∧
      ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j →
        2 * rho < ‖projectionLinear uv (p i) - projectionLinear uv (p j)‖ := by
  obtain ⟨color, _hcolor, Q, hQP, hcard, hcolorQ⟩ := exists_cell_color P
    (fun i => projectedCell uv rho (p i))
  refine ⟨Q, hQP, hcard, ?_⟩
  intro i hi j hj hij
  have hcell : projectedCell uv rho (p i) ≠ projectedCell uv rho (p j) :=
    fun he => hij (hinj (hQP hi) (hQP hj) he)
  have hmod := (hcolorQ i hi).trans (hcolorQ j hj).symm
  have hfst := congrArg Prod.fst hmod
  have hsnd := congrArg Prod.snd hmod
  change 2 * rho < max |(project uv (p i)).1 - (project uv (p j)).1|
    |(project uv (p i)).2 - (project uv (p j)).2|
  by_cases hfirst : ⌊(project uv (p i)).1 / rho⌋ = ⌊(project uv (p j)).1 / rho⌋
  · have hsecond : ⌊(project uv (p i)).2 / rho⌋ ≠ ⌊(project uv (p j)).2 / rho⌋ := by
      intro he
      exact hcell (Prod.ext hfirst he)
    exact (same_residue_floor_separation hrho hsnd hsecond).trans_le (le_max_right _ _)
  · exact (same_residue_floor_separation hrho hfst hfirst).trans_le (le_max_left _ _)

lemma projectedBall_mono {X : Type*} (P Q : Finset X) (p : X → Point3)
    (uv c : ℝ × ℝ) (R : ℝ) (hQP : Q ⊆ P) :
    projectedBall Q p uv c R ⊆ projectedBall P p uv c R := Finset.filter_subset_filter _ hQP

end FinitePlaneProjectionGrid
