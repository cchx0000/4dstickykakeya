import Theorems.Thm_StickyKakeya4_original_tensor_coefficient_permutation
import Theorems.Thm_StickyKakeya4_finite_plane_projection_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTensorProjectionPairs
open ActualRoundedAdditiveEnergy OriginalPolynomialCoefficientGrid OriginalTensorFrostman
open OriginalTensorCoefficientPermutation

def parameters (n M : ℕ) : Finset (Fin (n+1) → ℝ) := tensor (grid M) (n+1)
def projection {n : ℕ} (v x : Fin (n+1) → ℝ) : ℝ := ∑ i, v i*x i

def pairParameters (n M : ℕ) (x y : Fin (n+1) → ℝ) (delta : ℝ) :
    Finset (Fin (n+1) → ℝ) :=
  (parameters n M).filter (fun v => |projection v x-projection v y| ≤ delta)

def labelCollisions {n : ℕ} (P : Finset (Fin (n+1) → ℝ))
    (v : Fin (n+1) → ℝ) (delta : ℝ) : Finset ((Fin (n+1) → ℝ) × (Fin (n+1) → ℝ)) :=
  (P.product P).filter (fun p => |projection v p.1-projection v p.2| ≤ delta)

def close {n : ℕ} (r : ℝ) (x y : Fin (n+1) → ℝ) : Prop :=
  ∀ i, |y i-x i| ≤ r

def annulus {n : ℕ} (j : ℕ) (delta : ℝ) (x y : Fin (n+1) → ℝ) : Prop :=
  close (2^(j+1)*delta) x y ∧ ∃ i, 2^j*delta < |y i-x i|

/-- Count parameters for an actual original secant, using a nonzero original
coordinate and the explicit coefficient grid. -/
theorem original_pair_parameter_count (n M : ℕ) (x y : Fin (n+1) → ℝ)
    (j : Fin (n+1)) {delta : ℝ} (hd : 0 ≤ delta)
    (hneq : x j≠y j) (hbox : |x j-y j| ≤ 2)
    (hmesh : FinitePlaneProjectionGrid.mesh M ≤ delta) :
    ((pairParameters n M x y delta).card:ℝ) ≤
      (8*delta/|x j-y j|)*(parameters n M).card := by
  have hid (v : Fin (n+1) → ℝ) :
      projection v x-projection v y=∑ i, v i*(x i-y i) := by
    unfold projection
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hset : pairParameters n M x y delta=
      (tensor (grid M) (n+1)).filter (fun v => |∑ i, v i*(x i-y i)| ≤ delta) := by
    ext v
    simp only [pairParameters,parameters,Finset.mem_filter,hid]
  rw [hset]
  exact original_tensor_two_box_collision n M (fun i => x i-y i) j hd
    (sub_ne_zero.mpr hneq) hbox hmesh

/-- The original lower secant scale can be used directly in the parameter
count, before any image cardinality or energy averaging. -/
theorem original_pair_scale_count (n M : ℕ) (x y : Fin (n+1) → ℝ)
    (j : Fin (n+1)) {delta r : ℝ} (hd : 0 ≤ delta) (hr : 0 < r)
    (hfar : r ≤ |y j-x j|) (hbox : |y j-x j| ≤ 2)
    (hmesh : FinitePlaneProjectionGrid.mesh M ≤ delta) :
    ((pairParameters n M x y delta).card:ℝ) ≤
      (8*delta/r)*(parameters n M).card := by
  have hpos : 0 < |x j-y j| := by simpa only [abs_sub_comm] using hr.trans_le hfar
  have hneq : x j≠y j := sub_ne_zero.mp (abs_pos.mp hpos)
  have hh := original_pair_parameter_count n M x y j hd hneq
    (by simpa only [abs_sub_comm] using hbox) hmesh
  have hs : r ≤ |x j-y j| := by simpa only [abs_sub_comm] using hfar
  have hfrac := div_le_div_of_nonneg_left (show 0 ≤ 8*delta by positivity) hr hs
  exact hh.trans (mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg _))

/-- Cauchy is applied to literal original tuple fibers; cell equality implies
an actual scalar collision at the original mesh. -/
theorem original_projected_cell_energy {n : ℕ} (P : Finset (Fin (n+1) → ℝ))
    (v : Fin (n+1) → ℝ) {delta : ℝ} (hd : 0 < delta) :
    (P.card:ℝ)^2 ≤ ((P.image (fun x => rounded delta (projection v x))).card:ℝ)*
      (labelCollisions P v delta).card := by
  let f := fun x => rounded delta (projection v x)
  have hc : (P.card:ℝ)^2 ≤ ((P.image f).card:ℝ)*
      (TwoTubePathCollisionCount.collisions P f).card := by
    exact_mod_cast TwoTubePathCollisionCount.square_card_le_image_mul_collisions P f
  have hsub : TwoTubePathCollisionCount.collisions P f ⊆ labelCollisions P v delta := by
    intro p hp
    obtain ⟨hx,hy,he⟩ := TwoTubePathCollisionCount.mem_collisions P f p |>.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,
      FinitePlaneProjectionGrid.same_floor_close hd he⟩
  exact hc.trans (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Finset.card_le_card hsub)) (Nat.cast_nonneg _))

lemma original_collision_fubini {n : ℕ} (P : Finset (Fin (n+1) → ℝ)) (M : ℕ) (delta : ℝ) :
    (∑ v∈parameters n M, ((labelCollisions P v delta).card:ℝ))=
      ∑ x∈P, ∑ y∈P, ((pairParameters n M x y delta).card:ℝ) := by
  simp only [labelCollisions,pairParameters,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.product_eq_sprod,Finset.sum_product,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.sum_comm]

/-- Actual coordinate windows admit a finite dyadic annular cover. -/
lemma original_exists_annulus {n : ℕ} (J : ℕ) {delta : ℝ} (x y : Fin (n+1) → ℝ)
    (hsmall : ¬close delta x y) (htop : close (2^(J+1)*delta) x y) :
    ∃ j∈Finset.range (J+1), annulus j delta x y := by
  have hex : ∃ j : ℕ, close (2^(j+1)*delta) x y := ⟨J,htop⟩
  let j := Nat.find hex
  have hj : j ≤ J := Nat.find_min' hex htop
  refine ⟨j,Finset.mem_range.mpr (by omega),Nat.find_spec hex,?_⟩
  have hnot : ¬close (2^j*delta) x y := by
    by_cases hz : j=0
    · simpa only [hz,pow_zero,one_mul] using hsmall
    · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hh : ¬close (2^(k+1)*delta) x y :=
        Nat.find_min hex (by dsimp [j] at hk ⊢; omega)
      simpa only [hk,Nat.succ_eq_add_one] using hh
  change ¬∀ i, |y i-x i| ≤ 2^j*delta at hnot
  push Not at hnot
  exact hnot

end OriginalTensorProjectionPairs
