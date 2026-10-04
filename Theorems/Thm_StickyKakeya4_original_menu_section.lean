import Theorems.Thm_StickyKakeya4_native_original_phase_grid_edges
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalMenuSection
open Classical
open scoped BigOperators
variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
def anchor (e : A × ((B × B) × (C × C))) : B × C := (e.2.1.1,e.2.2.1)
def remaining (e : A × ((B × B) × (C × C))) : A × (B × C) := (e.1,(e.2.1.2,e.2.2.2))
def sectionGraph (G : Finset (A × ((B × B) × (C × C)))) (q : B × C) : Finset (A × (B × C)) :=
  (G.filter (fun e => anchor e=q)).image remaining
lemma section_card (G : Finset (A × ((B × B) × (C × C)))) (q : B × C) :
    (sectionGraph G q).card=(G.filter (fun e => anchor e=q)).card := by
  apply Finset.card_image_of_injOn
  intro e he f hf hef
  have ha : anchor e=anchor f := (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
  rcases e with ⟨a,⟨b₀,b₁⟩,⟨c₀,c₁⟩⟩
  rcases f with ⟨a',⟨b₀',b₁'⟩,⟨c₀',c₁'⟩⟩
  simp only [anchor,remaining,Prod.mk.injEq] at ha hef
  rcases ha with ⟨rfl,rfl⟩
  rcases hef with ⟨rfl,rfl,rfl⟩
  rfl
lemma section_subset (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × ((B × B) × (C × C))))
    (hG : G ⊆ X ×ˢ ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi))) (q : B × C) :
    sectionGraph G q ⊆ X ×ˢ (Z ×ˢ Phi) := by
  intro e he
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp he
  have hh := Finset.mem_product.mp (hG (Finset.mem_filter.mp hw).1)
  have hb := Finset.mem_product.mp hh.2
  exact Finset.mem_product.mpr ⟨hh.1,Finset.mem_product.mpr
    ⟨(Finset.mem_product.mp hb.1).2,(Finset.mem_product.mp hb.2).2⟩⟩
theorem exists_large_original_section (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × ((B × B) × (C × C)))) (hGne : G.Nonempty)
    (hG : G ⊆ X ×ˢ ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi))) :
    ∃ q ∈ Z ×ˢ Phi, (sectionGraph G q).Nonempty ∧
      sectionGraph G q ⊆ X ×ˢ (Z ×ˢ Phi) ∧
      G.card ≤ (Z.card*Phi.card)*(sectionGraph G q).card ∧
      ∀ e ∈ sectionGraph G q, (e.1,((q.1,e.2.1),(q.2,e.2.2))) ∈ G := by
  have hmaps : ∀ e ∈ G, anchor e ∈ Z ×ˢ Phi := by
    intro e he
    have hh := Finset.mem_product.mp (hG he)
    have hb := Finset.mem_product.mp hh.2
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hb.1).1,(Finset.mem_product.mp hb.2).1⟩
  have hQ : (Z ×ˢ Phi).Nonempty := by
    obtain ⟨e,he⟩ := hGne
    exact ⟨anchor e,hmaps e he⟩
  obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image (Z ×ˢ Phi) (fun q => (sectionGraph G q).card) hQ
  have hsum : (∑ q ∈ Z ×ˢ Phi, (sectionGraph G q).card)=G.card := by
    simp_rw [section_card]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_eq_self.mpr hmaps
  have hmass : G.card ≤ (Z.card*Phi.card)*(sectionGraph G q).card := by
    calc
      _ = ∑ r ∈ Z ×ˢ Phi, (sectionGraph G r).card := hsum.symm
      _ ≤ ∑ _r ∈ Z ×ˢ Phi, (sectionGraph G q).card := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hne : (sectionGraph G q).Nonempty := by
    apply Finset.card_pos.mp
    have hp := hGne.card_pos
    by_contra hzero
    have hz : (sectionGraph G q).card=0 := by omega
    simp only [hz,mul_zero] at hmass
    omega
  refine ⟨q,hq,hne,section_subset X Z Phi G hG q,hmass,?_⟩
  intro e he
  obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp he
  obtain ⟨hwG,hwq⟩ := Finset.mem_filter.mp hw
  have hid : (e.1,((q.1,e.2.1),(q.2,e.2.2)))=w := by
    rw [← hwe,← hwq]
    rfl
  exact hid ▸ hwG
theorem section_relative_density {g n m a s beta : ℝ}
    (hn : 0 < n) (hm : 0 < m)
    (hG : beta*a*n^2*m^2 ≤ g) (hsection : g ≤ (n*m)*s) : beta*a*n*m ≤ s := by
  apply (mul_le_mul_iff_left₀ (mul_pos hn hm)).mp
  nlinarith
end OriginalMenuSection
