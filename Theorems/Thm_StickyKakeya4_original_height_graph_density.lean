import Theorems.Thm_StickyKakeya4_original_height_graph_coarsening
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalHeightGraphDensity
open Classical DyadicOriginalFiberSelection OriginalHeightGraphCoarsening
open scoped BigOperators
variable {A B C K : Type*} [DecidableEq A] [DecidableEq C] [DecidableEq K]
theorem exists_dense_original_coarsening (X : Finset A) (Z : Finset B) (Phi : Finset C)
    (G : Finset (A × (B × C))) (hG : G ⊆ X ×ˢ (Z ×ˢ Phi)) (hGne : G.Nonempty)
    (f : B → K) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hdensity : beta*(X.card : ℝ)*(Z.card : ℝ)*(Phi.card : ℝ) ≤ (G.card : ℝ)) :
    ∃ j < levelCount Z, (edgeBin G Z f j).Nonempty ∧ (bin Z f j).Nonempty ∧
      beta*(Z.card : ℝ) ≤ (levelCount Z : ℝ)*((bin Z f j).card : ℝ) ∧
      beta*(X.card : ℝ)*(((bin Z f j).image f).card : ℝ)*(Phi.card : ℝ) ≤
        2*(levelCount Z : ℝ)*((coarseGraph (edgeBin G Z f j) f).card : ℝ) ∧
      coarseGraph (edgeBin G Z f j) f ⊆ X ×ˢ (((bin Z f j).image f) ×ˢ Phi) ∧
      ∀ k ∈ (bin Z f j).image f, fiber (bin Z f j) f k=fiber Z f k ∧
        2^j ≤ (fiber Z f k).card ∧ (fiber Z f k).card < 2^(j+1) := by
  obtain ⟨j,hj,hne,hbin,hmass,hquot,hsub,hlo,_hhi,hfib⟩ := exists_original_graph_coarsening X Z Phi G hG hGne f
  have hL : 0 ≤ (levelCount Z : ℝ) := by positivity
  have hmass' : (G.card : ℝ) ≤ (levelCount Z : ℝ)*((edgeBin G Z f j).card : ℝ) := by exact_mod_cast hmass
  have hupper : ((edgeBin G Z f j).card : ℝ) ≤ (X.card : ℝ)*((bin Z f j).card : ℝ)*(Phi.card : ℝ) := by
    have hh := Finset.card_le_card (edgeBin_subset X Z Phi G hG f j)
    simp only [Finset.card_product] at hh
    exact_mod_cast (by nlinarith : (edgeBin G Z f j).card ≤ X.card*(bin Z f j).card*Phi.card)
  have hprod : 0 < (X.card : ℝ)*(Phi.card : ℝ) := by
    obtain ⟨e,he⟩ := hGne
    obtain ⟨heX,heRest⟩ := Finset.mem_product.mp (hG he)
    have hePhi := (Finset.mem_product.mp heRest).2
    exact mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨e.1,heX⟩))
      (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨e.2.2,hePhi⟩))
  have hret : beta*(Z.card : ℝ) ≤ (levelCount Z : ℝ)*((bin Z f j).card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hprod).mp
    calc
      _ = beta*(X.card : ℝ)*(Z.card : ℝ)*(Phi.card : ℝ) := by ring
      _ ≤ (G.card : ℝ) := hdensity
      _ ≤ (levelCount Z : ℝ)*((edgeBin G Z f j).card : ℝ) := hmass'
      _ ≤ (levelCount Z : ℝ)*((X.card : ℝ)*((bin Z f j).card : ℝ)*(Phi.card : ℝ)) := mul_le_mul_of_nonneg_left hupper hL
      _ = _ := by ring
  have hZ : (2^j:ℝ)*(((bin Z f j).image f).card : ℝ) ≤ (Z.card : ℝ) := by
    have hh := hlo.trans (Finset.card_le_card (Finset.filter_subset _ _))
    exact_mod_cast hh
  have hcoarse : beta*(X.card : ℝ)*(((bin Z f j).image f).card : ℝ)*(Phi.card : ℝ) ≤
      2*(levelCount Z : ℝ)*((coarseGraph (edgeBin G Z f j) f).card : ℝ) := by
    apply (mul_le_mul_iff_left₀ (by positivity : (0:ℝ)<2^j)).mp
    calc
      _ = (beta*(X.card : ℝ)*(Phi.card : ℝ))*((2^j:ℝ)*(((bin Z f j).image f).card : ℝ)) := by ring
      _ ≤ (beta*(X.card : ℝ)*(Phi.card : ℝ))*(Z.card : ℝ) := mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = beta*(X.card : ℝ)*(Z.card : ℝ)*(Phi.card : ℝ) := by ring
      _ ≤ (G.card : ℝ) := hdensity
      _ ≤ (levelCount Z : ℝ)*((edgeBin G Z f j).card : ℝ) := hmass'
      _ ≤ (levelCount Z : ℝ)*((2^(j+1):ℝ)*((coarseGraph (edgeBin G Z f j) f).card : ℝ)) := mul_le_mul_of_nonneg_left hquot hL
      _ = _ := by rw [pow_succ]; ring
  exact ⟨j,hj,hne,hbin,hret,hcoarse,hsub,hfib⟩
theorem bad_coarse_labels_count (Z : Finset B) (f : B → K) (j : ℕ)
    (Bad : Finset K) (U : Finset B) (hBad : Bad ⊆ (bin Z f j).image f)
    (hcharge : ∀ k ∈ Bad, ∀ z ∈ fiber Z f k, z ∈ U) : 2^j*Bad.card ≤ U.card := by
  let W := (bin Z f j).filter (fun z => f z ∈ Bad)
  have hW : W ⊆ U := by
    intro z hz
    obtain ⟨hzbin,hzBad⟩ := Finset.mem_filter.mp hz
    apply hcharge (f z) hzBad z
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzbin).1,rfl⟩
  have hsum : (∑ k ∈ Bad, (fiber (bin Z f j) f k).card)=W.card := by
    unfold fiber
    rw [Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ = ∑ _k ∈ Bad, 2^j := by simp [mul_comm]
    _ ≤ ∑ k ∈ Bad, (fiber (bin Z f j) f k).card := Finset.sum_le_sum (fun k hk => (bin_fiber_bounds Z f j (hBad hk)).1)
    _ = W.card := hsum
    _ ≤ U.card := Finset.card_le_card hW
theorem coarse_bad_fraction {b coarse bad original retained lambda epsilon : ℝ}
    (hb : 0 < b) (hlambda : 0 ≤ lambda) (hepsilon : 0 ≤ epsilon)
    (hret : lambda*original ≤ retained) (hupper : retained ≤ 2*b*coarse)
    (hbad : b*bad ≤ epsilon*original) : lambda*bad ≤ 2*epsilon*coarse := by
  apply (mul_le_mul_iff_left₀ hb).mp
  calc
    _ = lambda*(b*bad) := by ring
    _ ≤ lambda*(epsilon*original) := mul_le_mul_of_nonneg_left hbad hlambda
    _ = epsilon*(lambda*original) := by ring
    _ ≤ epsilon*retained := mul_le_mul_of_nonneg_left hret hepsilon
    _ ≤ epsilon*(2*b*coarse) := mul_le_mul_of_nonneg_left hupper hepsilon
    _ = _ := by ring
end OriginalHeightGraphDensity
