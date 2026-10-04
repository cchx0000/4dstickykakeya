import Theorems.Thm_StickyKakeya4_actual_rounded_additive_energy
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

namespace RoundedIteratedCoverTransfer
open ActualRoundedAdditiveEnergy
open scoped Pointwise BigOperators
noncomputable section

/-- Selected integer labels have unique actual preimages in the original
separated source, with exactly the same retained cardinality. -/
theorem original_preimage (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (S : Finset ℤ) (hS : S ⊆ X.image (rounded δ)) :
    ∃ X' ⊆ X, X'.image (rounded δ) = S ∧ X'.card = S.card := by
  classical
  let X' := X.filter (fun x => rounded δ x ∈ S)
  have hsub : X' ⊆ X := Finset.filter_subset _ _
  have him : X'.image (rounded δ) = S := by
    ext k
    constructor
    · intro hk
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
      exact (Finset.mem_filter.mp hx).2
    · intro hk
      obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp (hS hk)
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,by simpa only [heq] using hk⟩,heq⟩
  have hinj : Set.InjOn (rounded δ) X' := (rounding_injOn X hδ hsep).mono hsub
  exact ⟨X',hsub,him,(Finset.card_image_of_injOn hinj).symm.trans (congrArg Finset.card him)⟩

lemma round_abs_error {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |x-δ*(rounded δ x : ℝ)| ≤ δ := by
  have h := round_error hδ x
  rw [abs_of_nonneg h.1]
  exact h.2.le

/-- Every original iterated sum carries its own actual rounded integer sum. -/
theorem nsmul_rounding_witness (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    {x : ℝ} (hx : x ∈ n • X) :
    ∃ z ∈ n • (X.image (rounded δ)), |x-δ*(z : ℝ)| ≤ (n : ℝ)*δ := by
  classical
  induction n generalizing x with
  | zero =>
    simpa using hx
  | succ n ih =>
    rw [succ_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨z,hz,he⟩ := ih ha
    refine ⟨z+rounded δ b,?_,?_⟩
    · rw [succ_nsmul]
      exact Finset.mem_add.mpr ⟨z,hz,rounded δ b,Finset.mem_image_of_mem _ hb,rfl⟩
    · have hid : a+b-δ*((z+rounded δ b : ℤ) : ℝ) =
          (a-δ*(z : ℝ))+(b-δ*(rounded δ b : ℝ)) := by push_cast; ring
      rw [hid]
      have hbnd := (abs_add_le _ _).trans (add_le_add he (round_abs_error hδ b))
      push_cast
      nlinarith

/-- All original mixed sums remain within the explicit mesh error of the
literal integer Minkowski sumset. -/
theorem mixed_rounding_witness (X Y : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) (n m : ℕ)
    {x : ℝ} (hx : x ∈ Y + n • X - m • X) :
    ∃ z ∈ Y.image (rounded δ) + n • X.image (rounded δ) - m • X.image (rounded δ),
      |x-δ*(z : ℝ)| ≤ ((n+m+1 : ℕ) : ℝ)*δ := by
  classical
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  obtain ⟨y,hy,c,hc,rfl⟩ := Finset.mem_add.mp ha
  obtain ⟨zb,hzb,heb⟩ := nsmul_rounding_witness X hδ m hb
  obtain ⟨zc,hzc,hec⟩ := nsmul_rounding_witness X hδ n hc
  refine ⟨rounded δ y+zc-zb,?_,?_⟩
  · exact Finset.mem_sub.mpr ⟨rounded δ y+zc,
      Finset.mem_add.mpr ⟨rounded δ y,Finset.mem_image_of_mem _ hy,zc,hzc,rfl⟩,zb,hzb,rfl⟩
  · have hid : y+c-b-δ*((rounded δ y+zc-zb : ℤ) : ℝ) =
        ((y-δ*(rounded δ y : ℝ))+(c-δ*(zc : ℝ)))-(b-δ*(zb : ℝ)) := by push_cast; ring
    rw [hid]
    have h := (abs_sub _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (round_abs_error hδ y) hec)) heb)
    push_cast
    nlinarith

lemma rounded_label_close {δ x : ℝ} {z : ℤ} (hδ : 0 < δ) (B : ℕ)
    (h : |x-δ*(z : ℝ)| ≤ (B : ℝ)*δ) :
    rounded δ x ∈ Finset.Icc (z-(B : ℤ)) (z+(B : ℤ)) := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  have hlo : ((z-(B : ℤ) : ℤ) : ℝ) ≤ x/δ := by
    apply (le_div_iff₀ hδ).mpr
    push_cast
    nlinarith
  have hup : x/δ ≤ ((z+(B : ℤ) : ℤ) : ℝ) := by
    apply (div_le_iff₀ hδ).mpr
    push_cast
    nlinarith
  apply Finset.mem_Icc.mpr
  constructor
  · exact Int.le_floor.mpr hlo
  · simpa only [rounded, Int.floor_intCast] using Int.floor_mono hup

/-- Convert the actual original real sumset to an explicit grid cover, with
no inverse density or extra cardinality balancing. -/
theorem iterated_grid_cover_bound (X Y : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) (n m : ℕ) :
    ((Y + n • X - m • X).image (rounded δ)).card ≤
      (2*(n+m+1)+1) *
        (Y.image (rounded δ) + n • X.image (rounded δ) - m • X.image (rounded δ)).card := by
  classical
  let Z := Y.image (rounded δ) + n • X.image (rounded δ) - m • X.image (rounded δ)
  let B := n+m+1
  have hsub : (Y + n • X - m • X).image (rounded δ) ⊆
      Z.biUnion (fun z => Finset.Icc (z-(B : ℤ)) (z+(B : ℤ))) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨z,hz,he⟩ := mixed_rounding_witness X Y hδ n m hx
    exact Finset.mem_biUnion.mpr ⟨z,hz,rounded_label_close hδ B he⟩
  have hc (z : ℤ) : (Finset.Icc (z-(B : ℤ)) (z+(B : ℤ))).card = 2*B+1 := by
    rw [Int.card_Icc]
    have hi : z+(B : ℤ)+1-(z-(B : ℤ)) = ((2*B+1 : ℕ) : ℤ) := by push_cast; ring
    rw [hi]
    exact Int.toNat_natCast _
  calc
    _ ≤ (Z.biUnion (fun z => Finset.Icc (z-(B : ℤ)) (z+(B : ℤ)))).card := Finset.card_le_card hsub
    _ ≤ ∑ z ∈ Z, (Finset.Icc (z-(B : ℤ)) (z+(B : ℤ))).card := Finset.card_biUnion_le
    _ = _ := by simp only [hc, Finset.sum_const, Nat.nsmul_eq_mul]; dsimp [B,Z]; ring
end
end RoundedIteratedCoverTransfer
