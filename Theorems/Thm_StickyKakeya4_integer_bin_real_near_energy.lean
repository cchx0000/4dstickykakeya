import Theorems.Thm_StickyKakeya4_labelled_real_energy_bin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

noncomputable section
namespace IntegerBinRealNearEnergy
open TwoTubePathCollisionCount ShiftedLabelEnergy ActualRoundedAdditiveEnergy

def realGrid (delta : ℝ) (S : Finset ℤ) : Finset ℝ := S.image (fun s : ℤ => delta*(s:ℝ))

theorem real_grid_injective {delta : ℝ} (hdelta : 0<delta) :
    Function.Injective (fun s : ℤ => delta*(s:ℝ)) := by
  intro s t h
  have hh : (s:ℝ)=(t:ℝ) := mul_left_cancel₀ (ne_of_gt hdelta) h
  exact_mod_cast hh

theorem real_grid_card {delta : ℝ} (hdelta : 0<delta) (S : Finset ℤ) :
    (realGrid delta S).card=S.card := Finset.card_image_of_injective _ (real_grid_injective hdelta)

theorem real_grid_separated {delta : ℝ} (hdelta : 0<delta) (S : Finset ℤ) :
    ∀ x∈realGrid delta S, ∀ y∈realGrid delta S, x≠y → delta≤|x-y| := by
  intro x hx y hy hxy
  obtain ⟨s,_hs,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨t,_ht,rfl⟩ := Finset.mem_image.mp hy
  have hst : s≠t := fun h => hxy (congrArg (fun z : ℤ => delta*(z:ℝ)) h)
  have hi : (1:ℤ)≤|s-t| := by
    rcases le_total s t with h|h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      omega
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      omega
  have hr : (1:ℝ)≤|(s:ℝ)-(t:ℝ)| := by exact_mod_cast hi
  calc
    _ = delta*1 := by ring
    _ ≤ delta*|(s:ℝ)-(t:ℝ)| := mul_le_mul_of_nonneg_left hr hdelta.le
    _ = _ := by rw [← mul_sub,abs_mul,abs_of_pos hdelta]

/-- Exact integer bin energy lifts to closed near-energy of the ORIGINAL
real A and the literal real grid delta*S. Only the two A rounding errors
remain, and their difference has absolute value less than delta. -/
theorem integer_energy_le_original_near
    (A : Finset ℝ) (S : Finset ℤ) {delta : ℝ} (hdelta : 0<delta)
    (hsep : ∀ a∈A, ∀ b∈A, a≠b → delta≤|a-b|) :
    Finset.addEnergy (A.image (rounded delta)) S ≤ nearDifferenceEnergy (realGrid delta S) A delta := by
  classical
  let g : ℝ × ℤ → ℤ × ℤ := fun p => (rounded delta p.1,p.2)
  have hinj : Set.InjOn g (A.product S) := by
    intro p hp q hq heq
    have hs : p.2=q.2 := by simpa only [g] using congrArg (fun r : ℤ × ℤ => r.2) heq
    have ha : rounded delta p.1=rounded delta q.1 := by
      simpa only [g] using congrArg (fun r : ℤ × ℤ => r.1) heq
    exact Prod.ext ((rounding_injOn A hdelta hsep) (Finset.mem_product.mp hp).1
      (Finset.mem_product.mp hq).1 ha) hs
  have him : (A.product S).image g=(A.image (rounded delta)).product S := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨ha,hs⟩ := Finset.mem_product.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ha,hs⟩
    · intro hq
      obtain ⟨ha,hs⟩ := Finset.mem_product.mp hq
      obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨(a,q.2),Finset.mem_product.mpr ⟨ha,hs⟩,Prod.ext heq rfl⟩
  have hcoll := collisions_image_card (A.product S) g (fun p : ℤ × ℤ => p.1+p.2) hinj
  rw [him] at hcoll
  have heq : (collisions (A.product S) (fun p => rounded delta p.1+p.2)).card =
      Finset.addEnergy (A.image (rounded delta)) S := by
    calc
      _ = _ := hcoll
      _ = _ := by simpa only [collisions,Finset.product_eq_sprod] using
        (Finset.addEnergy_eq_card_filter (A.image (rounded delta)) S).symm
  rw [← heq,near_difference_eq_near_sum,nearEnergy]
  apply Finset.card_le_card_of_injOn (fun z : (ℝ × ℤ) × (ℝ × ℤ) =>
    ((delta*(z.1.2:ℝ),z.1.1),(delta*(z.2.2:ℝ),z.2.1)))
  · intro z hz
    obtain ⟨h1,h2,hlabel⟩ := (mem_collisions _ _ z).mp hz
    obtain ⟨ha,hs⟩ := Finset.mem_product.mp h1
    obtain ⟨hb,ht⟩ := Finset.mem_product.mp h2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hs,ha⟩,Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ ht,hb⟩⟩,?_⟩
    have ea := round_error hdelta z.1.1
    have eb := round_error hdelta z.2.1
    have hreal := congrArg (fun q : ℤ => delta*(q:ℝ)) hlabel
    push_cast at hreal
    dsimp
    exact abs_le.mpr ⟨by nlinarith [ea.1,ea.2,eb.1,eb.2],
      by nlinarith [ea.1,ea.2,eb.1,eb.2]⟩
  · intro z _ w _ h
    have ha : z.1.1=w.1.1 := congrArg (fun q => q.1.2) h
    have hb : z.2.1=w.2.1 := congrArg (fun q => q.2.2) h
    have hs := (real_grid_injective hdelta) (congrArg (fun q => q.1.1) h)
    have ht := (real_grid_injective hdelta) (congrArg (fun q => q.2.1) h)
    exact Prod.ext (Prod.ext ha hs) (Prod.ext hb ht)

end IntegerBinRealNearEnergy
