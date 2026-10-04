import Theorems.Thm_StickyKakeya4_gkz_original_ratio_dichotomy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped BigOperators

namespace GKZOriginalDenseRatioSelection
open ActualRoundedAdditiveEnergy GKZOriginalRatioGap

/-- Choose an original point from each occupied cell. Counting all original
labels, including repeated values, gives a light original window. -/
theorem exists_original_light_window {X : Type*} [DecidableEq X]
    (P : Finset X) (value : X → ℝ) (B : Finset ℝ) {s : ℝ}
    (hs : 0 < s) (hdense : 1 ≤ 8*s*(B.image (rounded s)).card) :
    ∃ b ∈ B, ((P.filter (fun p => |value p-b| ≤ s)).card : ℝ) ≤
      32*s*P.card := by
  let C := B.image (rounded s)
  have hw : ∀ z ∈ C, ∃ b ∈ B, rounded s b=z := fun z hz => Finset.mem_image.mp hz
  let rep : ℤ → ℝ := fun z => if hz : z∈C then Classical.choose (hw z hz) else 0
  have hrep (z : ℤ) (hz : z∈C) : rep z ∈ B ∧ rounded s (rep z)=z := by
    dsimp [rep]
    rw [dif_pos hz]
    exact Classical.choose_spec (hw z hz)
  have hC : C.Nonempty := by
    by_contra hn
    have hc : C.card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    change 1 ≤ 8*s*(C.card : ℝ) at hdense
    rw [hc] at hdense
    norm_num at hdense
  have hlocal (p : X) : ((C.filter (fun z => |value p-rep z| ≤ s)).card : ℝ) ≤ 4 := by
    apply (NativeTangentGridCoarsening.scalar_injective_grid_centered_card
      (C.filter (fun z => |value p-rep z| ≤ s)) rep
      (r := s) (R := 1) (c := value p) hs (by norm_num) ?_ ?_).trans (by norm_num)
    · intro z hz w hw hzw
      have hz' := (hrep z (Finset.mem_filter.mp hz).1).2
      have hw' := (hrep w (Finset.mem_filter.mp hw).1).2
      change rounded s (rep z)=rounded s (rep w) at hzw
      simpa only [hz', hw'] using hzw
    · intro z hz
      simpa only [one_mul, abs_sub_comm] using (Finset.mem_filter.mp hz).2
  have hswap : (∑ z ∈ C, ((P.filter (fun p => |value p-rep z| ≤ s)).card : ℝ)) =
      ∑ p ∈ P, ((C.filter (fun z => |value p-rep z| ≤ s)).card : ℝ) := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have hsum : (∑ z ∈ C, ((P.filter (fun p => |value p-rep z| ≤ s)).card : ℝ)) ≤
      ∑ _z ∈ C, 32*s*(P.card : ℝ) := by
    rw [hswap]
    calc
      _ ≤ ∑ _p ∈ P, (4:ℝ) := Finset.sum_le_sum (fun p _ => hlocal p)
      _ = 4*(P.card : ℝ) := by simp [mul_comm]
      _ ≤ (C.card : ℝ)*(32*s*(P.card : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hdense
          (show 0 ≤ 4*(P.card : ℝ) by positivity)
        change 1*(4*(P.card : ℝ)) ≤ (8*s*(C.card : ℝ))*(4*(P.card : ℝ)) at hm
        nlinarith
      _ = _ := by simp
  obtain ⟨z, hz, hlight⟩ := Finset.exists_le_of_sum_le hC hsum
  exact ⟨rep z, (hrep z hz).1, hlight⟩

def originalLargeDenominators (A : Finset ℝ) (h : ℝ) : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((A.product A).product (A.product A)).filter (fun z => h < |z.2.1-z.2.2|)

/-- The dense ratio alternative produces an actual original four-tuple whose
ratio window contains few original four-tuples, with all multiplicities kept. -/
theorem exists_original_light_ratio (A : Finset ℝ) {h s : ℝ} (hs : 0 < s)
    (hdense : 1 ≤ 8*s*
      (((cutoffRatios A h).filter (fun b => 0 ≤ b ∧ b ≤ 1)).image (rounded s)).card) :
    ∃ x ∈ A, ∃ x' ∈ A, ∃ y ∈ A, ∃ y' ∈ A,
      h < |y-y'| ∧ 0 ≤ (x-x')/(y-y') ∧ (x-x')/(y-y') ≤ 1 ∧
      ((((originalLargeDenominators A h).filter
        (fun p => |(p.1.1-p.1.2)/(p.2.1-p.2.2)-(x-x')/(y-y')| ≤ s)).card : ℝ)
          ≤ 32*s*(A.card : ℝ)^4) := by
  obtain ⟨b, hb, hlight⟩ := exists_original_light_window (originalLargeDenominators A h)
    (fun p => (p.1.1-p.1.2)/(p.2.1-p.2.2))
    ((cutoffRatios A h).filter (fun b => 0 ≤ b ∧ b ≤ 1)) hs hdense
  obtain ⟨hb, hb0, hb1⟩ := Finset.mem_filter.mp hb
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hvp, hvden⟩ := Finset.mem_filter.mp hv
  obtain ⟨hxpair, hypair⟩ := Finset.mem_product.mp hvp
  obtain ⟨hx, hx'⟩ := Finset.mem_product.mp hxpair
  obtain ⟨hy, hy'⟩ := Finset.mem_product.mp hypair
  refine ⟨v.1.1, hx, v.1.2, hx', v.2.1, hy, v.2.2, hy', hvden, hb0, hb1, ?_⟩
  apply hlight.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hc := Finset.card_filter_le
    ((A.product A).product (A.product A)) (fun z => h < |z.2.1-z.2.2|)
  have hp : ((A.product A).product (A.product A)).card = A.card^4 := by
    simp only [Finset.product_eq_sprod, Finset.card_product]
    ring
  rw [hp] at hc
  exact_mod_cast hc

end GKZOriginalDenseRatioSelection
