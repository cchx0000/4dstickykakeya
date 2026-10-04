import Theorems.Thm_StickyKakeya4_shifted_label_energy
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

namespace ActualRoundedAdditiveEnergy
open TwoTubePathCollisionCount ShiftedLabelEnergy
noncomputable section

def rounded (δ x : ℝ) : ℤ := ⌊x/δ⌋

lemma round_error {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 ≤ x-δ*(rounded δ x : ℝ) ∧ x-δ*(rounded δ x : ℝ) < δ := by
  have hl := (le_div_iff₀ hδ).mp (Int.floor_le (x/δ))
  have hu := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x/δ))
  unfold rounded
  constructor <;> nlinarith

lemma rounding_injOn (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) : Set.InjOn (rounded δ) X := by
  intro x hx y hy heq
  by_contra hne
  have hb := hsep x hx y hy hne
  have hxe := round_error hδ x
  have hye := round_error hδ y
  rw [← heq] at hye
  have hlt : |x-y| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-- The collision count is preserved by an injective map on the original
objects, before passing to their finite image. -/
lemma collisions_image_card {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (A : Finset P) (g : P → Q) (f : Q → ℤ) (hg : Set.InjOn g A) :
    (collisions A (fun p => f (g p))).card = (collisions (A.image g) f).card := by
  apply Finset.card_bij (fun p _ => (g p.1,g p.2))
  · intro p hp
    obtain ⟨hp₁,hp₂,heq⟩ := (mem_collisions A (fun p => f (g p)) p).mp hp
    exact (mem_collisions (A.image g) f _).mpr ⟨Finset.mem_image_of_mem g hp₁,
      Finset.mem_image_of_mem g hp₂,heq⟩
  · intro p hp q hq heq
    obtain ⟨hp₁,hp₂,_⟩ := (mem_collisions A (fun p => f (g p)) p).mp hp
    obtain ⟨hq₁,hq₂,_⟩ := (mem_collisions A (fun p => f (g p)) q).mp hq
    exact Prod.ext (hg hp₁ hq₁ (congrArg Prod.fst heq)) (hg hp₂ hq₂ (congrArg Prod.snd heq))
  · intro q hq
    obtain ⟨hq₁,hq₂,heq⟩ := (mem_collisions (A.image g) f q).mp hq
    obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hq₁
    obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hq₂
    refine ⟨(a,b),(mem_collisions A (fun p => f (g p)) _).mpr ⟨ha,hb,?_⟩,?_⟩
    · simpa only [hea,heb] using heq
    · exact Prod.ext hea heb

lemma rounded_product_image (X Y : Finset ℝ) (δ : ℝ) :
    (X.product Y).image (fun p => (rounded δ p.1,rounded δ p.2)) =
      (X.image (rounded δ)).product (Y.image (rounded δ)) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp₁,Finset.mem_image_of_mem _ hp₂⟩
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    obtain ⟨x,hx,hex⟩ := Finset.mem_image.mp hq₁
    obtain ⟨y,hy,hey⟩ := Finset.mem_image.mp hq₂
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,Prod.ext hex hey⟩

lemma rounded_label_energy (X Y : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) :
    (collisions (X.product Y) (fun p => rounded δ p.1+rounded δ p.2)).card =
      Finset.addEnergy (X.image (rounded δ)) (Y.image (rounded δ)) := by
  classical
  have hg : Set.InjOn (fun p : ℝ × ℝ => (rounded δ p.1,rounded δ p.2)) (X.product Y) := by
    intro p hp q hq heq
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hp
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    exact Prod.ext ((rounding_injOn X hδ hX) hp₁ hq₁ (congrArg Prod.fst heq))
      ((rounding_injOn Y hδ hY) hp₂ hq₂ (congrArg Prod.snd heq))
  have h := collisions_image_card (X.product Y)
    (fun p : ℝ × ℝ => (rounded δ p.1,rounded δ p.2)) (fun q => q.1+q.2) hg
  rw [rounded_product_image] at h
  calc
    _ = _ := h
    _ = _ := by
      simpa only [collisions, Finset.product_eq_sprod] using (Finset.addEnergy_eq_card_filter
        (X.image (rounded δ)) (Y.image (rounded δ))).symm

def nearEnergy (X Y : Finset ℝ) (δ : ℝ) : ℕ :=
  (nearPairs (X.product Y) (fun p => p.1+p.2) δ).card

/-- The original real near-energy loses at most five under literal floor
rounding. Separation is used only to retain the exact original labels. -/
theorem near_energy_le_five_rounded_energy (X Y : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) :
    nearEnergy X Y δ ≤ 5 * Finset.addEnergy (X.image (rounded δ)) (Y.image (rounded δ)) := by
  classical
  have herr (p : ℝ × ℝ) :
      0 ≤ p.1+p.2-δ*((rounded δ p.1+rounded δ p.2 : ℤ) : ℝ) ∧
      p.1+p.2-δ*((rounded δ p.1+rounded δ p.2 : ℤ) : ℝ) < 2*δ := by
    have hx := round_error hδ p.1
    have hy := round_error hδ p.2
    push_cast
    constructor <;> nlinarith
  have h := near_pairs_le_five_energy (X.product Y)
    (fun p => rounded δ p.1+rounded δ p.2) (fun p => p.1+p.2) hδ (fun p _ => herr p)
  rw [rounded_label_energy X Y hδ hX hY] at h
  exact h
lemma rounded_card (X : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|) :
    (X.image (rounded δ)).card = X.card := Finset.card_image_of_injOn (rounding_injOn X hδ hX)

def quadSwap : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ ((ℝ × ℝ) × (ℝ × ℝ)) where
  toFun p := ((p.1.1,p.2.2),(p.2.1,p.1.2))
  invFun p := ((p.1.1,p.2.2),(p.2.1,p.1.2))
  left_inv p := by rcases p with ⟨⟨x,y⟩,⟨z,w⟩⟩; rfl
  right_inv p := by rcases p with ⟨⟨x,y⟩,⟨z,w⟩⟩; rfl

def nearDifferenceEnergy (X Y : Finset ℝ) (δ : ℝ) : ℕ :=
  (nearPairs (X.product Y) (fun p => p.1-p.2) δ).card

/-- The actual original Y-label swap identifies difference and sum energies,
including the closed near-collision boundary. -/
theorem near_difference_eq_near_sum (X Y : Finset ℝ) (δ : ℝ) :
    nearDifferenceEnergy X Y δ = nearEnergy X Y δ := by
  unfold nearDifferenceEnergy nearEnergy
  apply Finset.card_equiv quadSwap
  rintro ⟨⟨x,y⟩,⟨z,w⟩⟩
  simp only [nearPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, quadSwap, Equiv.coe_fn_mk]
  have heq : x-y-(z-w) = x+w-(z+y) := by ring
  rw [heq]
  tauto

theorem near_difference_le_five_rounded_energy (X Y : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|) :
    nearDifferenceEnergy X Y δ ≤
      5 * Finset.addEnergy (X.image (rounded δ)) (Y.image (rounded δ)) := by
  rw [near_difference_eq_near_sum]
  exact near_energy_le_five_rounded_energy X Y hδ hX hY

/-- The native asymmetric energy density is retained with precisely the
factor five, on the same-cardinality original rounded images. -/
theorem rounded_energy_density (X Y : Finset ℝ) {δ c : ℝ} (hδ : 0 < δ)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hY : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ |x-y|)
    (henergy : c * (X.card : ℝ)^2 * (Y.card : ℝ) ≤ (nearDifferenceEnergy X Y δ : ℝ)) :
    (c/5) * ((X.image (rounded δ)).card : ℝ)^2 * ((Y.image (rounded δ)).card : ℝ) ≤
      (Finset.addEnergy (X.image (rounded δ)) (Y.image (rounded δ)) : ℝ) := by
  rw [rounded_card X hδ hX, rounded_card Y hδ hY]
  have hu : (nearDifferenceEnergy X Y δ : ℝ) ≤
      5 * (Finset.addEnergy (X.image (rounded δ)) (Y.image (rounded δ)) : ℝ) := by
    exact_mod_cast near_difference_le_five_rounded_energy X Y hδ hX hY
  nlinarith

end
end ActualRoundedAdditiveEnergy
