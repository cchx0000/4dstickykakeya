import Theorems.Thm_StickyKakeya4_actual_planar_rounded_energy
import Theorems.Thm_StickyKakeya4_rounded_iterated_cover_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open scoped Pointwise

namespace PlanarRoundedSumsetCover
open PlanarShiftedNearEnergy
noncomputable section

def synthesis (eta : ℝ) : (ℤ×ℤ) →+ (ℝ×ℝ) where
  toFun z := (eta*(z.1:ℝ),eta*(z.2:ℝ))
  map_zero' := by simp
  map_add' := by intro a b; ext <;> simp <;> ring

lemma point_rounding_error {eta : ℝ} (heta : 0 < eta) (x : ℝ×ℝ) :
    ‖x-synthesis eta (roundPoint eta x)‖ ≤ eta := by
  have h1 := ActualRoundedAdditiveEnergy.round_error heta x.1
  have h2 := ActualRoundedAdditiveEnergy.round_error heta x.2
  simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
  change max |x.1-eta*(ActualRoundedAdditiveEnergy.rounded eta x.1:ℝ)|
    |x.2-eta*(ActualRoundedAdditiveEnergy.rounded eta x.2:ℝ)| ≤ eta
  rw [abs_of_nonneg h1.1,abs_of_nonneg h2.1]
  exact max_le h1.2.le h2.2.le

private theorem nsmul_witness (X : Finset (ℝ×ℝ)) {eta : ℝ} (heta : 0 < eta)
    (n : ℕ) {x : ℝ×ℝ} (hx : x ∈ n • X) :
    ∃ z ∈ n • (X.image (roundPoint eta)), ‖x-synthesis eta z‖ ≤ (n:ℝ)*eta := by
  classical
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
    rw [succ_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨z,hz,he⟩ := ih ha
    refine ⟨z+roundPoint eta b,?_,?_⟩
    · rw [succ_nsmul]
      exact Finset.mem_add.mpr ⟨z,hz,roundPoint eta b,Finset.mem_image_of_mem _ hb,rfl⟩
    · rw [map_add]
      have hid : a+b-(synthesis eta z+synthesis eta (roundPoint eta b)) =
          (a-synthesis eta z)+(b-synthesis eta (roundPoint eta b)) := by abel
      rw [hid]
      have h := (norm_add_le _ _).trans (add_le_add he (point_rounding_error heta b))
      push_cast
      nlinarith

private theorem mixed_witness (X Y : Finset (ℝ×ℝ)) {eta : ℝ} (heta : 0 < eta)
    (n m : ℕ) {x : ℝ×ℝ} (hx : x ∈ Y+n • X-m • X) :
    ∃ z ∈ Y.image (roundPoint eta)+n • X.image (roundPoint eta)-m • X.image (roundPoint eta),
      ‖x-synthesis eta z‖ ≤ ((n+m+1:ℕ):ℝ)*eta := by
  classical
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  obtain ⟨y,hy,c,hc,rfl⟩ := Finset.mem_add.mp ha
  obtain ⟨zb,hzb,heb⟩ := nsmul_witness X heta m hb
  obtain ⟨zc,hzc,hec⟩ := nsmul_witness X heta n hc
  refine ⟨roundPoint eta y+zc-zb,?_,?_⟩
  · exact Finset.mem_sub.mpr ⟨roundPoint eta y+zc,
      Finset.mem_add.mpr ⟨roundPoint eta y,Finset.mem_image_of_mem _ hy,zc,hzc,rfl⟩,zb,hzb,rfl⟩
  · rw [map_sub,map_add]
    have hid : y+c-b-(synthesis eta (roundPoint eta y)+synthesis eta zc-synthesis eta zb) =
        ((y-synthesis eta (roundPoint eta y))+(c-synthesis eta zc))-(b-synthesis eta zb) := by abel
    rw [hid]
    have h := (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (point_rounding_error heta y) hec)) heb)
    push_cast
    nlinarith

private lemma close_label_box {eta : ℝ} (heta : 0 < eta) (B : ℕ)
    {x : ℝ×ℝ} {z : ℤ×ℤ} (h : ‖x-synthesis eta z‖ ≤ (B:ℝ)*eta) :
    roundPoint eta x ∈
      (Finset.Icc (z.1-(B:ℤ)) (z.1+(B:ℤ))).product
      (Finset.Icc (z.2-(B:ℤ)) (z.2+(B:ℤ))) := by
  have hm : max |x.1-eta*(z.1:ℝ)| |x.2-eta*(z.2:ℝ)| ≤ (B:ℝ)*eta := by
    simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,synthesis,AddMonoidHom.coe_mk,ZeroHom.coe_mk] using h
  exact Finset.mem_product.mpr ⟨
    RoundedIteratedCoverTransfer.rounded_label_close heta B ((le_max_left _ _).trans hm),
    RoundedIteratedCoverTransfer.rounded_label_close heta B ((le_max_right _ _).trans hm)⟩

/-- All planar iterated sums are covered by their coupled original Z² sums;
there is no independent selection of the two coordinates. -/
theorem actual_planar_iterated_cover (X Y : Finset (ℝ×ℝ)) {eta : ℝ}
    (heta : 0 < eta) (n m : ℕ) :
    ((Y+n • X-m • X).image (roundPoint eta)).card ≤
      (2*(n+m+1)+1)^2 *
        (Y.image (roundPoint eta)+n • X.image (roundPoint eta)-m • X.image (roundPoint eta)).card := by
  classical
  let Z := Y.image (roundPoint eta)+n • X.image (roundPoint eta)-m • X.image (roundPoint eta)
  let B := n+m+1
  let box (z : ℤ×ℤ) := (Finset.Icc (z.1-(B:ℤ)) (z.1+(B:ℤ))).product
    (Finset.Icc (z.2-(B:ℤ)) (z.2+(B:ℤ)))
  have hc (q : ℤ) : (Finset.Icc (q-(B:ℤ)) (q+(B:ℤ))).card = 2*B+1 := by
    rw [Int.card_Icc]
    have h : q+(B:ℤ)+1-(q-(B:ℤ)) = ((2*B+1:ℕ):ℤ) := by push_cast; ring
    rw [h]
    exact Int.toNat_natCast _
  have hb (z : ℤ×ℤ) : (box z).card = (2*B+1)^2 := by simp only [box,Finset.product_eq_sprod,Finset.card_product,hc,pow_two]
  have hsub : (Y+n • X-m • X).image (roundPoint eta) ⊆ Z.biUnion box := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨z,hz,he⟩ := mixed_witness X Y heta n m hx
    exact Finset.mem_biUnion.mpr ⟨z,hz,close_label_box heta B he⟩
  calc
    _ ≤ (Z.biUnion box).card := Finset.card_le_card hsub
    _ ≤ ∑ z∈Z, (box z).card := Finset.card_biUnion_le
    _ = _ := by simp only [hb,Finset.sum_const,Nat.nsmul_eq_mul]; dsimp [B,Z]; ring
end
end PlanarRoundedSumsetCover
