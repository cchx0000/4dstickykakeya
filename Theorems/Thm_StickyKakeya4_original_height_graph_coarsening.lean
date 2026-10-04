import Theorems.Thm_StickyKakeya4_original_menu_section
import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalHeightGraphCoarsening
open Classical DyadicOriginalFiberSelection
open scoped BigOperators
variable {A B C K : Type*} [DecidableEq A] [DecidableEq C] [DecidableEq K]
def edgeBin (G : Finset (A × (B × C))) (Z : Finset B) (f : B → K) (j : ℕ) :=
  G.filter (fun e => level Z f e.2.1=j)
def quotientEdge (f : B → K) (e : A × (B × C)) : A × (K × C) := (e.1,(f e.2.1,e.2.2))
def coarseGraph (G : Finset (A × (B × C))) (f : B → K) := G.image (quotientEdge f)
omit [DecidableEq A] [DecidableEq C] in
lemma edgeBin_subset (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × (B × C))) (hG : G ⊆ X ×ˢ (Z ×ˢ Phi)) (f : B → K) (j : ℕ) :
    edgeBin G Z f j ⊆ X ×ˢ ((bin Z f j) ×ˢ Phi) := by
  intro e he
  obtain ⟨heG,hej⟩ := Finset.mem_filter.mp he
  obtain ⟨heX,heRest⟩ := Finset.mem_product.mp (hG heG)
  obtain ⟨heZ,hePhi⟩ := Finset.mem_product.mp heRest
  exact Finset.mem_product.mpr ⟨heX,Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨heZ,hej⟩,hePhi⟩⟩
omit [DecidableEq A] [DecidableEq C] in
lemma edgeBin_card_sum (G : Finset (A × (B × C))) (Z : Finset B) (f : B → K) :
    (∑ j ∈ Finset.range (levelCount Z), (edgeBin G Z f j).card)=G.card := by
  unfold edgeBin
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  exact Finset.filter_eq_self.mpr (fun e _he => Finset.mem_range.mpr (level_lt Z f e.2.1))
omit [DecidableEq A] [DecidableEq C] in
theorem exists_edge_mass_bin (G : Finset (A × (B × C))) (Z : Finset B) (f : B → K) (hG : G.Nonempty) :
    ∃ j < levelCount Z, (edgeBin G Z f j).Nonempty ∧ G.card ≤ levelCount Z*(edgeBin G Z f j).card := by
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.range (levelCount Z))
    (fun j => (edgeBin G Z f j).card) ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  have hmass : G.card ≤ levelCount Z*(edgeBin G Z f j).card := by
    calc
      _ = ∑ k ∈ Finset.range (levelCount Z), (edgeBin G Z f k).card := (edgeBin_card_sum G Z f).symm
      _ ≤ ∑ _k ∈ Finset.range (levelCount Z), (edgeBin G Z f j).card := Finset.sum_le_sum hmax
      _ = _ := by simp
  have hne : (edgeBin G Z f j).Nonempty := by
    apply Finset.card_pos.mp
    by_contra h
    have hz : (edgeBin G Z f j).card=0 := by omega
    simp only [hz,mul_zero] at hmass
    have hp := hG.card_pos
    omega
  exact ⟨j,Finset.mem_range.mp hj,hne,hmass⟩
lemma quotient_fiber_cap (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × (B × C))) (hG : G ⊆ X ×ˢ (Z ×ˢ Phi)) (f : B → K) (j : ℕ) (q : A × (K × C)) :
    ((edgeBin G Z f j).filter (fun e => quotientEdge f e=q)).card ≤ (fiber (bin Z f j) f q.2.1).card := by
  apply Finset.card_le_card_of_injOn (fun e => e.2.1)
  · intro e he
    obtain ⟨hebin,heq⟩ := Finset.mem_filter.mp he
    have hz := (Finset.mem_product.mp (edgeBin_subset X Z Phi G hG f j hebin)).2
    exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hz).1,congrArg (fun p => p.2.1) heq⟩
  · intro e he d hd heq
    have heQ := (Finset.mem_filter.mp he).2
    have hdQ := (Finset.mem_filter.mp hd).2
    have hqd : quotientEdge f e=quotientEdge f d := heQ.trans hdQ.symm
    apply Prod.ext
    · exact congrArg (fun p : A × (K × C) => p.1) hqd
    · apply Prod.ext heq
      exact congrArg (fun p => p.2.2) hqd
lemma coarseGraph_subset (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × (B × C))) (hG : G ⊆ X ×ˢ (Z ×ˢ Phi)) (f : B → K) :
    coarseGraph G f ⊆ X ×ˢ ((Z.image f) ×ˢ Phi) := by
  intro e he
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hx,hz⟩ := Finset.mem_product.mp (hG hw)
  obtain ⟨hz,hphi⟩ := Finset.mem_product.mp hz
  exact Finset.mem_product.mpr ⟨hx,Finset.mem_product.mpr ⟨Finset.mem_image_of_mem f hz,hphi⟩⟩
lemma dyadic_label_mass_bounds (Z : Finset B) (f : B → K) (j : ℕ) :
    2^j*((bin Z f j).image f).card ≤ (bin Z f j).card ∧
      (bin Z f j).card ≤ 2^(j+1)*((bin Z f j).image f).card := by
  rw [← fiber_sum (bin Z f j) f]
  constructor
  · calc
      _ = ∑ _k ∈ (bin Z f j).image f, 2^j := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun k hk => (bin_fiber_bounds Z f j hk).1)
  · calc
      _ ≤ ∑ _k ∈ (bin Z f j).image f, 2^(j+1) := Finset.sum_le_sum (fun k hk => (bin_fiber_bounds Z f j hk).2.le)
      _ = _ := by simp [mul_comm]
lemma edgeBin_coarse_card (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × (B × C))) (hG : G ⊆ X ×ˢ (Z ×ˢ Phi)) (f : B → K) (j : ℕ) :
    ((edgeBin G Z f j).card : ℝ) ≤ (2^(j+1):ℝ)*((coarseGraph (edgeBin G Z f j) f).card : ℝ) := by
  let W := edgeBin G Z f j
  let Q := coarseGraph W f
  have hf : ∀ q ∈ Q, ((W.filter (fun e => quotientEdge f e=q)).card : ℝ) ≤ (2^(j+1):ℝ) := by
    intro q hq
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hq
    have heZ := (Finset.mem_product.mp (edgeBin_subset X Z Phi G hG f j he)).2
    have heB : e.2.1 ∈ bin Z f j := (Finset.mem_product.mp heZ).1
    have hfib := (bin_fiber_bounds Z f j (Finset.mem_image_of_mem f heB)).2.le
    have hh := (quotient_fiber_cap X Z Phi G hG f j (quotientEdge f e)).trans hfib
    exact_mod_cast hh
  have hc := FinePointSlabGeometry.card_le_real_mul_of_fibers W Q (quotientEdge f)
    (2^(j+1):ℝ) (fun e he => Finset.mem_image_of_mem _ he) hf
  simpa only [mul_comm] using hc
theorem exists_original_graph_coarsening (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × (B × C))) (hG : G ⊆ X ×ˢ (Z ×ˢ Phi)) (hGne : G.Nonempty) (f : B → K) :
    ∃ j < levelCount Z, (edgeBin G Z f j).Nonempty ∧ (bin Z f j).Nonempty ∧
      G.card ≤ levelCount Z*(edgeBin G Z f j).card ∧
      ((edgeBin G Z f j).card : ℝ) ≤ (2^(j+1):ℝ)*((coarseGraph (edgeBin G Z f j) f).card : ℝ) ∧
      coarseGraph (edgeBin G Z f j) f ⊆ X ×ˢ (((bin Z f j).image f) ×ˢ Phi) ∧
      2^j*((bin Z f j).image f).card ≤ (bin Z f j).card ∧
      (bin Z f j).card ≤ 2^(j+1)*((bin Z f j).image f).card ∧
      ∀ k ∈ (bin Z f j).image f, fiber (bin Z f j) f k=fiber Z f k ∧
        2^j ≤ (fiber Z f k).card ∧ (fiber Z f k).card < 2^(j+1) := by
  obtain ⟨j,hj,hne,hmass⟩ := exists_edge_mass_bin G Z f hGne
  have hbin : (bin Z f j).Nonempty := by
    obtain ⟨e,he⟩ := hne
    have hh := (Finset.mem_product.mp (edgeBin_subset X Z Phi G hG f j he)).2
    exact ⟨e.2.1,(Finset.mem_product.mp hh).1⟩
  refine ⟨j,hj,hne,hbin,hmass,edgeBin_coarse_card X Z Phi G hG f j,
    coarseGraph_subset X (bin Z f j) Phi _ (edgeBin_subset X Z Phi G hG f j) f,
    (dyadic_label_mass_bounds Z f j).1,(dyadic_label_mass_bounds Z f j).2,?_⟩
  intro k hk
  have heq := fiber_bin_eq Z f j hk
  refine ⟨heq,?_⟩
  simpa only [heq] using bin_fiber_bounds Z f j hk
end OriginalHeightGraphCoarsening
