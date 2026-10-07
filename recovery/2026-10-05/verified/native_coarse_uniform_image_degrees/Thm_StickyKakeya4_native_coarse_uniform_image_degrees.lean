import Theorems.Thm_StickyKakeya4_native_incidence_multiplicity_tower
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section

namespace NativeCoarseUniformImageDegrees
open Classical Finset
open scoped BigOperators

/-- Partition an original point fiber by its distinct image pairs. -/
lemma point_fiber_card_sum {A P X : Type*} [DecidableEq A] [DecidableEq P]
    [DecidableEq X] (E : Finset A) (f : A → P × X) (x : X) :
    (E.filter (fun z => (f z).2 = x)).card =
      ∑ b ∈ (E.image f).filter (fun b => b.2 = x),
        (E.filter (fun z => f z = b)).card := by
  have himage : (E.filter (fun z => (f z).2 = x)).image f =
      (E.image f).filter (fun b => b.2 = x) := by
    ext b
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨z, ⟨hz, hx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, hx⟩
    · rintro ⟨⟨z, hz, rfl⟩, hx⟩
      exact ⟨z, ⟨hz, hx⟩, rfl⟩
  rw [card_eq_sum_card_image f, himage]
  apply sum_congr rfl
  intro b hb
  congr 1
  ext z
  have hx := (mem_filter.mp hb).2
  simp only [mem_filter]
  constructor
  · exact fun hz => ⟨hz.1.1, hz.2⟩
  · intro hz
    exact ⟨⟨hz.1, by rw [hz.2, hx]⟩, hz.2⟩

/-- Uniform original point fibers control their size relative to total mass. -/
lemma point_fiber_card_cross {A P X : Type*} [DecidableEq A] [DecidableEq P]
    [DecidableEq X] (E : Finset A) (f : A → P × X) (L : ℕ)
    (hpoint : ∀ a ∈ E, ∀ b ∈ E,
      (E.filter (fun z => (f z).2 = (f a).2)).card ≤
        L * (E.filter (fun z => (f z).2 = (f b).2)).card)
    (x : X) :
    (E.filter (fun z => (f z).2 = x)).card *
      ((E.image f).image Prod.snd).card ≤ L * E.card := by
  have hsupport : (E.image f).image Prod.snd = E.image (fun z => (f z).2) := by
    simp only [image_image, Function.comp_def]
  rw [hsupport]
  by_cases hx : x ∈ E.image (fun z => (f z).2)
  · obtain ⟨a, ha, hax⟩ := mem_image.mp hx
    calc
      _ = ∑ _y ∈ E.image (fun z => (f z).2),
          (E.filter (fun z => (f z).2 = x)).card := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ E.image (fun z => (f z).2),
          L * (E.filter (fun z => (f z).2 = y)).card := by
        apply sum_le_sum
        intro y hy
        obtain ⟨b, hb, hby⟩ := mem_image.mp hy
        simpa only [hax, hby] using hpoint a ha b hb
      _ = L * E.card := by rw [← mul_sum, ← card_eq_sum_card_image]
  · have hempty : E.filter (fun z => (f z).2 = x) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hx (mem_image.mpr ⟨a, (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩)
    simp [hempty]

/-- Erasing multiplicities preserves uniform point degrees up to the product
of the original pair-fiber and point-fiber comparison factors. -/
theorem image_point_degree_cross {A P X : Type*} [DecidableEq A] [DecidableEq P]
    [DecidableEq X] (E : Finset A) (f : A → P × X) (K L : ℕ)
    (hpair : ∀ a ∈ E, ∀ b ∈ E,
      (E.filter (fun z => f z = f a)).card ≤
        K * (E.filter (fun z => f z = f b)).card)
    (hpoint : ∀ a ∈ E, ∀ b ∈ E,
      (E.filter (fun z => (f z).2 = (f a).2)).card ≤
        L * (E.filter (fun z => (f z).2 = (f b).2)).card)
    (x : X) :
    ((E.image f).filter (fun b => b.2 = x)).card *
      ((E.image f).image Prod.snd).card ≤ K * L * (E.image f).card := by
  by_cases hE : E.Nonempty
  · obtain ⟨a, ha, hmin⟩ := exists_min_image E
      (fun a => (E.filter (fun z => f z = f a)).card) hE
    let m := (E.filter (fun z => f z = f a)).card
    have hm : 0 < m := card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, rfl⟩⟩
    have hlo : m * ((E.image f).filter (fun b => b.2 = x)).card ≤
        (E.filter (fun z => (f z).2 = x)).card := by
      rw [point_fiber_card_sum E f x]
      calc
        _ = ∑ _b ∈ (E.image f).filter (fun b => b.2 = x), m := by
          simp [Nat.mul_comm]
        _ ≤ _ := by
          apply sum_le_sum
          intro b hb
          obtain ⟨c, hc, rfl⟩ := mem_image.mp (mem_filter.mp hb).1
          exact hmin c hc
    have hhi : E.card ≤ K * m * (E.image f).card := by
      calc
        _ = ∑ b ∈ E.image f, (E.filter (fun z => f z = b)).card :=
          card_eq_sum_card_image f E
        _ ≤ ∑ _b ∈ E.image f, K * m := by
          apply sum_le_sum
          intro b hb
          obtain ⟨c, hc, rfl⟩ := mem_image.mp hb
          exact hpair c hc a ha
        _ = _ := by simp [Nat.mul_comm]
    have hcross := point_fiber_card_cross E f L hpoint x
    apply (mul_le_mul_iff_right₀ hm).mp
    calc
      _ = (m * ((E.image f).filter (fun b => b.2 = x)).card) *
          ((E.image f).image Prod.snd).card := by ring
      _ ≤ (E.filter (fun z => (f z).2 = x)).card *
          ((E.image f).image Prod.snd).card := Nat.mul_le_mul_right _ hlo
      _ ≤ L * E.card := hcross
      _ ≤ L * (K * m * (E.image f).card) := Nat.mul_le_mul_left L hhi
      _ = _ := by ring
  · rw [not_nonempty_iff_eq_empty.mp hE]
    simp

/-- Every image point degree is bounded by the actual image multiplicity. -/
theorem image_point_degree_le_multiplicity {A P X : Type*} [DecidableEq A]
    [DecidableEq P] [DecidableEq X] (E : Finset A) (f : A → P × X) (K L : ℕ)
    (hpair : ∀ a ∈ E, ∀ b ∈ E,
      (E.filter (fun z => f z = f a)).card ≤
        K * (E.filter (fun z => f z = f b)).card)
    (hpoint : ∀ a ∈ E, ∀ b ∈ E,
      (E.filter (fun z => (f z).2 = (f a).2)).card ≤
        L * (E.filter (fun z => (f z).2 = (f b).2)).card)
    (x : X) :
    (((E.image f).filter (fun b => b.2 = x)).card : ℝ) ≤
      (K * L : ℝ) * NativeIncidenceMultiplicityTower.multiplicity (E.image f) := by
  by_cases hE : E.Nonempty
  · have hs : (0 : ℝ) < ((E.image f).image Prod.snd).card := by
      exact_mod_cast card_pos.mpr ((hE.image f).image Prod.snd)
    rw [NativeIncidenceMultiplicityTower.multiplicity, ← mul_div_assoc]
    apply (le_div_iff₀ hs).mpr
    exact_mod_cast image_point_degree_cross E f K L hpair hpoint x
  · rw [not_nonempty_iff_eq_empty.mp hE]
    simp [NativeIncidenceMultiplicityTower.multiplicity]

end NativeCoarseUniformImageDegrees
