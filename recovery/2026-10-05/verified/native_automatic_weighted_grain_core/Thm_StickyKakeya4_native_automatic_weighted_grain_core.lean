import Theorems.Thm_StickyKakeya4_native_simultaneous_weighted_grain_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeAutomaticWeightedGrainCore
open Classical Finset RichDirectionalLayers WeightedRichDirectionalLayers
open NativeSimultaneousWeightedGrainCore
open scoped BigOperators

/-- Floor of the original mass divided by THIS level's class count, plus one.
Different levels keep their own class counts; no maximum is substituted. -/
def threshold (M J C : ℕ) : ℕ := M/(2*J*C)+1

lemma threshold_pos (M J C : ℕ) : 0 < threshold M J C := by
  unfold threshold
  exact Nat.zero_lt_succ _

/-- Computing the thresholds pays the entire simultaneous deletion budget.
Zero class counts contribute zero and need no division-positivity premise. -/
theorem threshold_budget (M J : ℕ) (hJ : 0 < J) (C : Fin J → ℕ) :
    2*(∑j,C j*(threshold M J (C j)-1)) ≤ M := by
  have hterm (j : Fin J) : (2*(C j*(threshold M J (C j)-1)))*J ≤ M := by
    simpa [threshold,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      Nat.div_mul_le_self M (2*J*C j)
  have hs := sum_le_sum (fun j (_hj : j∈(univ : Finset (Fin J))) => hterm j)
  have hs' : (2*(∑j,C j*(threshold M J (C j)-1)))*J ≤ M*J := by
    simpa [mul_sum,sum_mul,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hs
  exact Nat.le_of_mul_le_mul_right hs' hJ

/-- The integer threshold strictly exceeds the intended rational density. -/
theorem threshold_crossmul (M J C : ℕ) (hJ : 0 < J) (hC : 0 < C) :
    M < (2*J*C)*threshold M J C := by
  have hden : 0 < 2*J*C := by positivity
  have hh := (Nat.div_lt_iff_lt_mul hden).mp (Nat.lt_succ_self (M/(2*J*C)))
  simpa only [threshold,Nat.mul_comm] using hh

theorem threshold_real (M J C : ℕ) (hJ : 0 < J) (hC : 0 < C) :
    (M:ℝ)/(2*(J:ℝ)*(C:ℝ)) < (threshold M J C:ℝ) := by
  have hJr : (0:ℝ) < J := by exact_mod_cast hJ
  have hCr : (0:ℝ) < C := by exact_mod_cast hC
  have hh : (M:ℝ) < (2*(J:ℝ)*(C:ℝ))*(threshold M J C:ℝ) := by
    exact_mod_cast threshold_crossmul M J C hJ hC
  exact (div_lt_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hh)

/-- The final common core and all of its class densities are constructed from
the actual original maps, labels, and weights. There is no supplied deletion
budget or final-core certificate. Each level retains its own original count. -/
theorem exists_automatic_simultaneous_dense_core {α : Type*} {J : ℕ} {β : Fin J → Type*}
    (hJ : 0 < J) (A : Finset α) (f : (j : Fin J) → α → β j) (w : α → ℕ)
    (hpos : 0 < mass A w) :
    ∃K⊆A, K.Nonempty ∧ mass A w ≤ 2*mass K w ∧
      mass (A\K) w ≤ classBudget A f (fun j => threshold (mass A w) J (A.image (f j)).card) ∧
      ∀j,∀c∈K.image (f j),
        threshold (mass A w) J (A.image (f j)).card ≤ mass (classFiber K (f j) c) w ∧
        (mass A w:ℝ)/(2*(J:ℝ)*((A.image (f j)).card:ℝ)) <
          (mass (classFiber K (f j) c) w:ℝ) := by
  let k := fun j => threshold (mass A w) J (A.image (f j)).card
  have hbudget : 2*classBudget A f k ≤ mass A w :=
    threshold_budget (mass A w) J hJ (fun j => (A.image (f j)).card)
  obtain ⟨K,hKA,hKne,hhalf,hloss,hmin⟩ :=
    exists_simultaneous_dense_core_half A f w k hpos hbudget
  refine ⟨K,hKA,hKne,hhalf,hloss,?_⟩
  intro j c hc
  have hC : 0 < (A.image (f j)).card :=
    card_pos.mpr ⟨c,(image_subset_image hKA) hc⟩
  have hmin' := hmin j c hc
  refine ⟨hmin',?_⟩
  have hcast : (threshold (mass A w) J (A.image (f j)).card:ℝ) ≤
      (mass (classFiber K (f j) c) w:ℝ) := by exact_mod_cast hmin'
  exact (threshold_real (mass A w) J (A.image (f j)).card hJ hC).trans_le hcast

end NativeAutomaticWeightedGrainCore
