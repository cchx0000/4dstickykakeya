import Theorems.Thm_StickyKakeya4_original_height_graph_density
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalMenuBCGraph
open Classical OriginalMenuSection OriginalHeightGraphCoarsening OriginalHeightGraphDensity DyadicOriginalFiberSelection
variable {A B C K : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq K]
lemma section_original_witness (G : Finset (A × ((B × B) × (C × C)))) (q : B × C)
    (e : A × (B × C)) (he : e ∈ sectionGraph G q) : (e.1,((q.1,e.2.1),(q.2,e.2.2))) ∈ G := by
  obtain ⟨v,hv,hve⟩ := Finset.mem_image.mp he
  obtain ⟨hvG,hvq⟩ := Finset.mem_filter.mp hv
  have hid : (e.1,((q.1,e.2.1),(q.2,e.2.2)))=v := by
    rw [← hve,← hvq]
    rfl
  exact hid ▸ hvG
lemma coarse_section_original_witness (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × ((B × B) × (C × C)))) (hG : G ⊆ X ×ˢ ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi)))
    (q : B × C) (f : B → K) (j : ℕ) (a : A) (k : K) (c : C)
    (he : (a,(k,c)) ∈ coarseGraph (edgeBin (sectionGraph G q) Z f j) f) :
    ∃ z ∈ bin Z f j, f z=k ∧ (a,((q.1,z),(q.2,c))) ∈ G := by
  obtain ⟨e,he,heq⟩ := Finset.mem_image.mp he
  have hsub := edgeBin_subset X Z Phi (sectionGraph G q) (section_subset X Z Phi G hG q) f j he
  have hz := (Finset.mem_product.mp (Finset.mem_product.mp hsub).2).1
  have ha : e.1=a := congrArg Prod.fst heq
  have hk : f e.2.1=k := congrArg (fun p => p.2.1) heq
  have hc : e.2.2=c := congrArg (fun p => p.2.2) heq
  refine ⟨e.2.1,hz,hk,?_⟩
  have hw := section_original_witness G q e (Finset.mem_filter.mp he).1
  simpa only [ha,hc] using hw
theorem exists_actual_BC_graph (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × ((B × B) × (C × C)))) (hGne : G.Nonempty)
    (hG : G ⊆ X ×ˢ ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi))) (f : B → K) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hdensity : beta*(X.card : ℝ)*(Z.card : ℝ)^2*(Phi.card : ℝ)^2 ≤ (G.card : ℝ)) :
    ∃ q ∈ Z ×ˢ Phi, ∃ j < levelCount Z,
      (edgeBin (sectionGraph G q) Z f j).Nonempty ∧ (bin Z f j).Nonempty ∧
      beta*(Z.card : ℝ) ≤ (levelCount Z : ℝ)*((bin Z f j).card : ℝ) ∧
      beta*(X.card : ℝ)*(((bin Z f j).image f).card : ℝ)*(Phi.card : ℝ) ≤
        2*(levelCount Z : ℝ)*((coarseGraph (edgeBin (sectionGraph G q) Z f j) f).card : ℝ) ∧
      coarseGraph (edgeBin (sectionGraph G q) Z f j) f ⊆ X ×ˢ (((bin Z f j).image f) ×ˢ Phi) ∧
      (∀ k ∈ (bin Z f j).image f, fiber (bin Z f j) f k=fiber Z f k ∧
        2^j ≤ (fiber Z f k).card ∧ (fiber Z f k).card < 2^(j+1)) ∧
      ∀ a k c, (a,(k,c)) ∈ coarseGraph (edgeBin (sectionGraph G q) Z f j) f →
        ∃ z ∈ bin Z f j, f z=k ∧ (a,((q.1,z),(q.2,c))) ∈ G := by
  obtain ⟨q,hq,hsection,hsub,hmass,_hlift⟩ := exists_large_original_section X Z Phi G hGne hG
  have hZ : (0:ℝ)<Z.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨q.1,(Finset.mem_product.mp hq).1⟩)
  have hPhi : (0:ℝ)<Phi.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨q.2,(Finset.mem_product.mp hq).2⟩)
  have hmass' : (G.card : ℝ) ≤ ((Z.card : ℝ)*(Phi.card : ℝ))*((sectionGraph G q).card : ℝ) := by exact_mod_cast hmass
  have hd := section_relative_density hZ hPhi hdensity hmass'
  obtain ⟨j,hj,hne,hbin,hret,hden,hquot,hfib⟩ := exists_dense_original_coarsening X Z Phi (sectionGraph G q) hsub hsection f hbeta hd
  exact ⟨q,hq,j,hj,hne,hbin,hret,hden,hquot,hfib,coarse_section_original_witness X Z Phi G hG q f j⟩
end OriginalMenuBCGraph
