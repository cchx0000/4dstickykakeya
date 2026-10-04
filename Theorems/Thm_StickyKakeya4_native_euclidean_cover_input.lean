import Theorems.Thm_StickyKakeya4_native_dyadic_tube_stopping
import Theorems.Thm_StickyKakeya4_euclidean_alignment_patches
import Theorems.Thm_StickyKakeya4_packing_reference_overlap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace NativeEuclideanCoverInput
open NativeDyadicTubeStopping FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open EuclideanAlignmentPatches
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev EPlane := EuclideanSpace ℝ (Fin 2)
def eball (A : Finset Plane) (a : Plane) (r : ℝ) : Finset Plane :=
  A.filter (fun p => dist (euclidean p) (euclidean a) ≤ r)
def ecover (A : Finset Plane) (delta : ℝ) (a : Plane) (r : ℝ) : ℝ :=
  ((eball A a r).image (ADGridCoverMenus.gridLabel delta)).card

def EuclideanCoverAD (A : Finset Plane) (delta C t : ℝ) : Prop :=
  ∀ a ∈ A, ∀ r : ℝ, delta ≤ r → r ≤ 1 →
    (r / delta) ^ t / C ≤ ecover A delta a r ∧ ecover A delta a r ≤ C * (r / delta) ^ t

def EuclideanSeparated (A : Finset Plane) (delta : ℝ) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≠ q → delta ≤ dist (euclidean p) (euclidean q)

def packingBound : ℕ := max 1
  (Classical.choose (StickyKakeya4.exists_uniform_separated_ball_card_bound EPlane))
def inputConstant : ℝ := 4 * (packingBound : ℝ)
lemma packingBound_pos : 0 < packingBound := lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _)
lemma inputConstant_ge_one : 1 ≤ inputConstant := by
  have h : (1 : ℝ) ≤ packingBound := by exact_mod_cast packingBound_pos
  unfold inputConstant
  linarith only [h]
lemma euclidean_injective : Function.Injective (euclidean : Plane → EPlane) := by
  intro p q h
  exact congrArg (fun x : EPlane => WithLp.ofLp x) h

/-- Fixed occupancy of actual original mesh cells from Euclidean separation.
No point is replaced by a grid center. -/
lemma cell_capacity {A : Finset Plane} {delta : ℝ} (hdelta : 0 < delta)
    (hsep : EuclideanSeparated A delta) (z : Fin 2 → ℤ) :
    (A.filter (fun p => ADGridCoverMenus.gridLabel delta p = z)).card ≤ packingBound := by
  let S := A.filter (fun p => ADGridCoverMenus.gridLabel delta p = z)
  by_cases hne : S.Nonempty
  · obtain ⟨q, hq⟩ := hne
    have hqz := (Finset.mem_filter.mp hq).2
    have hK := Classical.choose_spec (StickyKakeya4.exists_uniform_separated_ball_card_bound EPlane)
    have hh := hK (2 * delta) (by positivity) (euclidean q) (S.image euclidean)
    have hnear : ∀ p ∈ S.image euclidean, dist p (euclidean q) ≤ 2 * delta := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      have hz := (Finset.mem_filter.mp hx).2
      have hg := same_cell_euclidean_dist_le delta hdelta x q (hz.trans hqz.symm)
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using hg
    have hseparated : ∀ p ∈ S.image euclidean, ∀ q' ∈ S.image euclidean,
        p ≠ q' → 2 * delta / 2 ≤ dist p q' := by
      intro p hp q' hq' hpq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq'
      have hxy : x ≠ y := fun h => hpq (congrArg euclidean h)
      simpa only [mul_div_cancel_left₀ delta (by norm_num : (2 : ℝ) ≠ 0)] using
        hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
    have hbound := hh hnear hseparated
    rw [Finset.card_image_of_injective _ euclidean_injective] at hbound
    exact hbound.trans (le_max_right _ _)
  · change S.card ≤ packingBound
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    exact Nat.zero_le _

lemma subset_card_le_cover {A S : Finset Plane} {delta : ℝ} (hdelta : 0 < delta)
    (hsep : EuclideanSeparated A delta) (hSA : S ⊆ A) :
    (S.card : ℝ) ≤ (packingBound : ℝ) * ((S.image (ADGridCoverMenus.gridLabel delta)).card : ℝ) := by
  have hsum : (S.card : ℝ) = ∑ z ∈ S.image (ADGridCoverMenus.gridLabel delta),
      ((S.filter (fun p => ADGridCoverMenus.gridLabel delta p = z)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (ADGridCoverMenus.gridLabel delta) S
  rw [hsum]
  calc
    _ ≤ ∑ _z ∈ S.image (ADGridCoverMenus.gridLabel delta), (packingBound : ℝ) := by
      apply Finset.sum_le_sum
      intro z _hz
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset_filter _ hSA)).trans (cell_capacity hdelta hsep z)
    _ = _ := by simp [mul_comm]

lemma quarter_square_euclidean_diameter {A : Finset Plane}
    (hbox : ∀ p ∈ A, ∀ i : Fin 2, |p i| ≤ 1 / 4) :
    ∀ p ∈ A, ∀ q ∈ A, dist (euclidean p) (euclidean q) ≤ 1 := by
  intro p hp q hq
  have hh := euclidean_dist_le_card_mul p q (1 / 2) (by norm_num)
    (fun i => (abs_sub _ _).trans (by linarith [hbox p hp i, hbox q hq i]))
  norm_num at hh
  exact hh

/-- Convert Euclidean occupied-cell AD on unchanged original points to native
sup-metric point-count AD; the whole quarter-square controls the top tail. -/
theorem native_AD_of_euclidean_cover_AD {A : Finset Plane} {delta C t : ℝ}
    (hdelta : 0 < delta) (hdeltaone : delta ≤ 1) (hC : 0 < C)
    (ht : 0 ≤ t) (ht2 : t ≤ 2) (hsep : EuclideanSeparated A delta)
    (hbox : ∀ p ∈ A, ∀ i : Fin 2, |p i| ≤ 1 / 4)
    (H : EuclideanCoverAD A delta C t) :
    ADBounds A delta (inputConstant * C) t := by
  have hL := inputConstant_ge_one
  intro a ha r hrlo hrhi
  have hr : 0 < r := hdelta.trans_le hrlo
  have hp : 0 ≤ (r / delta) ^ t := by positivity
  constructor
  · have heS : eball A a r ⊆ carrierBall A a r := by
      intro p hp'
      obtain ⟨hpA, hdist⟩ := Finset.mem_filter.mp hp'
      exact Finset.mem_filter.mpr ⟨hpA, (sup_dist_le p a).trans hdist⟩
    have hc : ecover A delta a r ≤ ((carrierBall A a r).card : ℝ) := by
      unfold ecover
      exact_mod_cast (Finset.card_image_le.trans (Finset.card_le_card heS))
    have hCL : C ≤ inputConstant * C := le_mul_of_one_le_left hC.le hL
    exact (div_le_div_of_nonneg_left hp hC hCL).trans ((H a ha r hrlo hrhi).1.trans hc)
  · let u := min (2 * r) 1
    have hdu : delta ≤ u := le_min (by linarith only [hrlo, hr]) hdeltaone
    have huone : u ≤ 1 := min_le_right _ _
    have hu2 : u ≤ 2 * r := min_le_left _ _
    have hEu : carrierBall A a r ⊆ eball A a u := by
      intro p hp'
      obtain ⟨hpA, hdist⟩ := Finset.mem_filter.mp hp'
      refine Finset.mem_filter.mpr ⟨hpA, le_min ?_ ?_⟩
      · have hh := euclidean_dist_le_card_mul p a r hr.le (fun i => by
          simpa only [Real.dist_eq] using (dist_le_pi_dist p a i).trans hdist)
        simpa only [Fintype.card_fin, Nat.cast_ofNat] using hh
      · exact quarter_square_euclidean_diameter hbox p hpA a ha
    have hmass := subset_card_le_cover hdelta hsep (Finset.filter_subset (fun p => dist p a ≤ r) A)
    have hcover : (((carrierBall A a r).image (ADGridCoverMenus.gridLabel delta)).card : ℝ) ≤ ecover A delta a u := by
      unfold ecover
      exact_mod_cast Finset.card_le_card (Finset.image_subset_image hEu)
    have hpow : (u / delta) ^ t ≤ 4 * (r / delta) ^ t := by
      have hbase : u / delta ≤ 2 * (r / delta) := by
        have hh := div_le_div_of_nonneg_right hu2 hdelta.le
        simpa only [mul_div_assoc] using hh
      have hfirst := Real.rpow_le_rpow (div_nonneg (hdelta.le.trans hdu) hdelta.le) hbase ht
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ r / delta)] at hfirst
      have htwo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ht2
      norm_num at htwo
      exact hfirst.trans (mul_le_mul_of_nonneg_right htwo hp)
    calc
      _ ≤ (packingBound : ℝ) * (((carrierBall A a r).image (ADGridCoverMenus.gridLabel delta)).card : ℝ) := hmass
      _ ≤ (packingBound : ℝ) * ecover A delta a u := mul_le_mul_of_nonneg_left hcover (Nat.cast_nonneg _)
      _ ≤ (packingBound : ℝ) * (C * (u / delta) ^ t) :=
        mul_le_mul_of_nonneg_left (H a ha u hdu huone).2 (Nat.cast_nonneg _)
      _ ≤ (packingBound : ℝ) * (C * (4 * (r / delta) ^ t)) := by gcongr
      _ = _ := by unfold inputConstant; ring
end
end NativeEuclideanCoverInput
