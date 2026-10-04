import Theorems.Thm_StickyKakeya4_original_angular_alphabet_translation
import Theorems.Thm_StickyKakeya4_original_menu_bc_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalAngularGraphTranslation
open Classical OriginalAngularAlphabetTranslation
variable {A B : Type*} [DecidableEq A] [DecidableEq B]
def translateEdge (anchor : ℝ) (e : A × (B × ℝ)) : A × (B × ℝ) := (e.1,(e.2.1,e.2.2-anchor))
def translatedGraph (G : Finset (A × (B × ℝ))) (anchor : ℝ) := G.image (translateEdge anchor)
omit [DecidableEq A] [DecidableEq B] in
lemma translateEdge_injective (anchor : ℝ) : Function.Injective (translateEdge (A:=A) (B:=B) anchor) := by
  intro x y h
  change (x.1,(x.2.1,x.2.2-anchor))=(y.1,(y.2.1,y.2.2-anchor)) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h₁,h₂,h₃⟩ := h
  apply Prod.ext h₁
  apply Prod.ext h₂
  linarith

lemma translatedGraph_card (G : Finset (A × (B × ℝ))) (anchor : ℝ) :
    (translatedGraph G anchor).card=G.card := Finset.card_image_of_injective G (translateEdge_injective anchor)
lemma translatedGraph_subset (P : Finset A) (Q : Finset B) (Phi : Finset ℝ)
    (G : Finset (A × (B × ℝ))) (hG : G ⊆ P ×ˢ (Q ×ˢ Phi)) (anchor : ℝ) :
    translatedGraph G anchor ⊆ P ×ˢ (Q ×ˢ shifted Phi anchor) := by
  intro e he
  obtain ⟨old,hold,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hp,hrest⟩ := Finset.mem_product.mp (hG hold)
  obtain ⟨hq,hphi⟩ := Finset.mem_product.mp hrest
  exact Finset.mem_product.mpr ⟨hp,Finset.mem_product.mpr ⟨hq,Finset.mem_image_of_mem _ hphi⟩⟩
lemma translatedGraph_original_edge (G : Finset (A × (B × ℝ))) (anchor : ℝ)
    (a : A) (b : B) (c : ℝ) (he : (a,(b,c)) ∈ translatedGraph G anchor) :
    (a,(b,c+anchor)) ∈ G := by
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp he
  have ha : e.1=a := congrArg Prod.fst heq
  have hb : e.2.1=b := congrArg (fun e => e.2.1) heq
  have hc : e.2.2-anchor=c := congrArg (fun e => e.2.2) heq
  have hid : (a,(b,c+anchor))=e := by
    apply Prod.ext ha.symm
    apply Prod.ext hb.symm
    linarith
  exact hid ▸ he
/-- The anchor translation preserves the actual graph density and the entire
 original C cardinality. It does not prune angular labels. -/
theorem translatedGraph_density (P : Finset A) (Q : Finset B) (Phi : Finset ℝ)
    (G : Finset (A × (B × ℝ))) (anchor beta : ℝ)
    (hG : beta*(P.card : ℝ)*(Q.card : ℝ)*(Phi.card : ℝ) ≤ (G.card : ℝ)) :
    beta*(P.card : ℝ)*(Q.card : ℝ)*((shifted Phi anchor).card : ℝ) ≤ ((translatedGraph G anchor).card : ℝ) := by
  simpa only [shifted_card,translatedGraph_card] using hG
end OriginalAngularGraphTranslation
