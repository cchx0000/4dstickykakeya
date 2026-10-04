import Theorems.Thm_StickyKakeya4_original_dense_coefficient_energy
import Theorems.Thm_StickyKakeya4_finite_plane_projection_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
open scoped BigOperators
namespace OriginalDenseCoefficientProjection
open Classical OriginalDenseCoefficientCounts OriginalDenseCoefficientEnergy
open ActualRoundedAdditiveEnergy GKZOriginalGapEnergy

def sumCover (A : Finset ℝ) (delta xi : ℝ) : Finset ℤ :=
  (sourcePairs A).image (fun z => rounded delta (z.1+xi*z.2))

lemma original_sum_cover_energy (A : Finset ℝ) (delta xi : ℝ) (hd : 0 < delta) :
    (A.card : ℝ)^4 ≤ (sumCover A delta xi).card*(collisions A delta xi).card := by
  let P := sourcePairs A
  let f : ℝ × ℝ → ℤ := fun z => rounded delta (z.1+xi*z.2)
  have hc : (P.card : ℝ)^2 ≤ ((P.image f).card : ℝ)*(TwoTubePathCollisionCount.collisions P f).card := by
    exact_mod_cast TwoTubePathCollisionCount.square_card_le_image_mul_collisions P f
  have hsub : TwoTubePathCollisionCount.collisions P f⊆collisions A delta xi := by
    intro z hz
    obtain ⟨h1,h2,he⟩ := (TwoTubePathCollisionCount.mem_collisions P f z).mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1,h2⟩,
      FinitePlaneProjectionGrid.same_floor_close hd he⟩
  have hm := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub))
    (Nat.cast_nonneg (α:=ℝ) (P.image f).card)
  have he : (P.card : ℝ)^2=(A.card : ℝ)^4 := by
    simp only [P,sourcePairs,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
    ring
  rw [he] at hc
  exact hc.trans hm

/-- One ACTUAL original coefficient gives a genuine projection-cover
gain, using the derived four-variable near/far collision energy. -/
theorem exists_original_coefficient_projection_bound (A Xi : Finset ℝ)
    (delta tau K u : ℝ) (hA : A.Nonempty) (hXi : Xi.Nonempty)
    (hd : 0 < delta) (hquery : delta ≤ tau) (htau1 : tau ≤ 1)
    (hAsep : ∀ x∈A,∀ y∈A,x≠y → delta ≤ |x-y|)
    (hXsep : ∀ x∈Xi,∀ y∈Xi,x≠y → delta ≤ |x-y|)
    (hprofile : ScalarFrostman A delta K u) :
    ∃ xi∈Xi,(A.card : ℝ) ≤ (sumCover A delta xi).card*
      (4*K*tau^u+6*A.card/(tau*Xi.card)) := by
  let N : ℝ := A.card
  let X : ℝ := Xi.card
  let B := 4*K*tau^u+6*N/(tau*X)
  let C := B*N^3
  have hN : 0 < N := Nat.cast_pos.mpr hA.card_pos
  have hX : 0 < X := Nat.cast_pos.mpr hXi.card_pos
  have htau : 0 < tau := hd.trans_le hquery
  have hsum := original_dense_coefficient_collision_energy A Xi delta tau K u
    hd hquery htau1 hAsep hXsep hprofile
  have he : C*X=4*K*tau^u*N^3*X+6*N^4/tau := by
    dsimp [C,B]
    field_simp [hX.ne',htau.ne']
  have hbudget : (∑ xi∈Xi,((collisions A delta xi).card : ℝ)) ≤ C*Xi.card := by
    change (∑ xi∈Xi,((collisions A delta xi).card : ℝ)) ≤ C*X
    rw [he]
    exact hsum
  obtain ⟨xi,hxi,hcol⟩ := FinitePlaneProjectionGrid.exists_le_average Xi
    (fun xi => ((collisions A delta xi).card : ℝ)) C hXi hbudget
  have hc := original_sum_cover_energy A delta xi hd
  have hm := mul_le_mul_of_nonneg_left hcol (Nat.cast_nonneg (α:=ℝ) (sumCover A delta xi).card)
  refine ⟨xi,hxi,?_⟩
  change N ≤ (sumCover A delta xi).card*B
  apply (mul_le_mul_iff_of_pos_right (pow_pos hN 3)).mp
  calc
    N*N^3 = N^4 := by ring
    _ ≤ (sumCover A delta xi).card*C := hc.trans hm
    _ = ((sumCover A delta xi).card*B)*N^3 := by dsimp [C]; ring

/-- A common small-sum bound on a genuinely dense ORIGINAL coefficient
family must pay this explicit obstruction. The near/far energy is derived
from the actual separated source, not assumed. -/
theorem original_common_small_sum_obstruction (A Xi : Finset ℝ)
    (delta tau K u M : ℝ) (hA : A.Nonempty) (hXi : Xi.Nonempty)
    (hd : 0 < delta) (hquery : delta ≤ tau) (htau1 : tau ≤ 1) (hK : 0 ≤ K)
    (hAsep : ∀ x∈A,∀ y∈A,x≠y → delta ≤ |x-y|)
    (hXsep : ∀ x∈Xi,∀ y∈Xi,x≠y → delta ≤ |x-y|)
    (hprofile : ScalarFrostman A delta K u)
    (hsmall : ∀ xi∈Xi,((sumCover A delta xi).card : ℝ) ≤ M*A.card) :
    1 ≤ M*(4*K*tau^u+6*A.card/(tau*Xi.card)) := by
  obtain ⟨xi,hxi,hgain⟩ := exists_original_coefficient_projection_bound A Xi delta tau K u
    hA hXi hd hquery htau1 hAsep hXsep hprofile
  have hN : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hX : 0 < (Xi.card : ℝ) := Nat.cast_pos.mpr hXi.card_pos
  have htau : 0 < tau := hd.trans_le hquery
  let B := 4*K*tau^u+6*A.card/(tau*Xi.card)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm := mul_le_mul_of_nonneg_right (hsmall xi hxi) hB
  apply (mul_le_mul_iff_of_pos_left hN).mp
  change (A.card : ℝ)*1 ≤ (A.card : ℝ)*(M*B)
  calc
    _ = (A.card : ℝ) := by ring
    _ ≤ (sumCover A delta xi).card*B := hgain
    _ ≤ (M*A.card)*B := hm
    _ = _ := by ring

end OriginalDenseCoefficientProjection
