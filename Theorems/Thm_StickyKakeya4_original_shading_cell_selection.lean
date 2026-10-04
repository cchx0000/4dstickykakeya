import Theorems.Thm_StickyKakeya4_dyadic_original_fiber_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

noncomputable section
open Classical
open scoped BigOperators
namespace OriginalShadingCellSelection
open DyadicOriginalFiberSelection

/-- Original points in distinct grid cells are disjoint resources. -/
theorem original_cell_charge {X C : Type*} (P : Finset X) (cells : Finset C)
    (grid : X → C) (M : ℕ)
    (hM : ∀ c∈cells, M ≤ (fiber P grid c).card) :
    M*cells.card ≤ (P.filter (fun p => grid p ∈ cells)).card := by
  calc
    _ = ∑ _c∈cells, M := by simp [Nat.mul_comm]
    _ ≤ ∑ c∈cells, (fiber P grid c).card := Finset.sum_le_sum hM
    _ = _ := by
      simpa only [fiber] using Finset.sum_card_fiberwise_eq_card_filter P cells grid

/-- Each occupied UNION cell is paid by one actual retained shading fiber.
There is no multiplication by a global maximum cell occupancy. -/
theorem original_union_cell_charge {X C I : Type*} (P : Finset X) (T : Finset I)
    (Y : I → Finset X) (cells : I → Finset C) (grid : X → C) (M : ℕ)
    (hsub : ∀ t∈T, Y t ⊆ P)
    (hM : ∀ t∈T, ∀ c∈cells t, M ≤ (fiber (Y t) grid c).card) :
    M*(T.biUnion cells).card ≤ P.card := by
  apply (original_cell_charge P (T.biUnion cells) grid M ?_).trans
    (Finset.card_le_card (Finset.filter_subset _ _))
  intro c hc
  obtain ⟨t,ht,hc⟩ := Finset.mem_biUnion.mp hc
  exact (hM t ht c hc).trans (Finset.card_le_card (Finset.filter_subset_filter _ (hsub t ht)))

lemma levelCount_mono {X : Type*} {Y P : Finset X} (hsub : Y ⊆ P) :
    levelCount Y ≤ levelCount P :=
  Nat.add_le_add_right (Nat.log_mono_right (Finset.card_le_card hsub)) 1

/-- A per-tube whole-fiber class preserves original mass; its cell-count
class has the same finite logarithmic label range as the original P. -/
lemma exists_shading_bin_label {X C : Type*} (P Y : Finset X) (grid : X → C)
    (hsub : Y ⊆ P) (hne : Y.Nonempty) :
    ∃ j k : ℕ, j < levelCount P ∧ k < levelCount P ∧
      (bin Y grid j).Nonempty ∧ Y.card ≤ levelCount P*(bin Y grid j).card ∧
      2^k ≤ ((bin Y grid j).image grid).card ∧
      ((bin Y grid j).image grid).card < 2^(k+1) := by
  obtain ⟨j,hj,hbin,hcard⟩ := exists_dyadic_bin Y grid hne
  let N := ((bin Y grid j).image grid).card
  have hN : 0 < N := Finset.card_pos.mpr (hbin.image grid)
  have hNP : N ≤ P.card := (Finset.card_image_le).trans
    ((Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_le_card hsub))
  refine ⟨j,Nat.log 2 N,hj.trans_le (levelCount_mono hsub),?_,hbin,
    hcard.trans (Nat.mul_le_mul_right _ (levelCount_mono hsub)),?_,?_⟩
  · exact Nat.lt_succ_of_le (Nat.log_mono_right hNP)
  · exact Nat.pow_log_le_self 2 hN.ne'
  · exact Nat.lt_pow_succ_log_self (by decide : 1<2) N

/-- Select a common actual occupancy exponent and actual number-of-cells
exponent across tubes. The original tube labels and all chosen cell fibers
are retained, with an explicit squared logarithmic population loss. -/
theorem exists_uniform_original_shading_bins {X C I : Type*}
    (P : Finset X) (T : Finset I) (Y : I → Finset X) (grid : X → C)
    (hT : T.Nonempty) (hsub : ∀ t∈T, Y t ⊆ P) (hY : ∀ t∈T, (Y t).Nonempty) :
    ∃ j k : ℕ, ∃ S : Finset I, S ⊆ T ∧ S.Nonempty ∧
      j < levelCount P ∧ k < levelCount P ∧
      T.card ≤ (levelCount P)^2*S.card ∧
      (∀ t∈S, (bin (Y t) grid j).Nonempty ∧
        (Y t).card ≤ levelCount P*(bin (Y t) grid j).card ∧
        2^k ≤ ((bin (Y t) grid j).image grid).card ∧
        ((bin (Y t) grid j).image grid).card < 2^(k+1)) ∧
      2^j*(S.biUnion (fun t => (bin (Y t) grid j).image grid)).card ≤ P.card := by
  have hex : ∀ t : I, ∃ b : ℕ×ℕ, t∈T →
      b.1 < levelCount P ∧ b.2 < levelCount P ∧
      (bin (Y t) grid b.1).Nonempty ∧
      (Y t).card ≤ levelCount P*(bin (Y t) grid b.1).card ∧
      2^b.2 ≤ ((bin (Y t) grid b.1).image grid).card ∧
      ((bin (Y t) grid b.1).image grid).card < 2^(b.2+1) := by
    intro t
    by_cases ht : t∈T
    · obtain ⟨j,k,h⟩ := exists_shading_bin_label P (Y t) grid (hsub t ht) (hY t ht)
      exact ⟨(j,k),fun _ => h⟩
    · exact ⟨(0,0),fun h => (ht h).elim⟩
  choose code hcode using hex
  let labels := (Finset.range (levelCount P)).product (Finset.range (levelCount P))
  let part (b : ℕ×ℕ) := T.filter (fun t => code t=b)
  have hlab : ∀ t∈T, code t∈labels := by
    intro t ht
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hcode t ht).1,
      Finset.mem_range.mpr (hcode t ht).2.1⟩
  have hlabels : labels.Nonempty := by
    exact ⟨(0,0),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
      Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩⟩
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image labels (fun b => (part b).card) hlabels
  have hsum : (∑ c∈labels, (part c).card)=T.card := by
    dsimp [part]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_eq_self.mpr hlab
  have hmass : T.card ≤ (levelCount P)^2*(part b).card := by
    calc
      _ = ∑ c∈labels, (part c).card := hsum.symm
      _ ≤ ∑ _c∈labels, (part b).card := Finset.sum_le_sum (fun c hc => hmax c hc)
      _ = _ := by simp [labels,pow_two]
  have hne : (part b).Nonempty := by
    apply Finset.card_pos.mp
    have hpos := hT.card_pos
    by_contra h
    have hz : (part b).card=0 := Nat.eq_zero_of_not_pos h
    rw [hz,Nat.mul_zero] at hmass
    omega
  have hs : part b ⊆ T := Finset.filter_subset _ _
  have hbounds := Finset.mem_product.mp hb
  have hspec : ∀ t∈part b, (bin (Y t) grid b.1).Nonempty ∧
      (Y t).card ≤ levelCount P*(bin (Y t) grid b.1).card ∧
      2^b.2 ≤ ((bin (Y t) grid b.1).image grid).card ∧
      ((bin (Y t) grid b.1).image grid).card < 2^(b.2+1) := by
    intro t ht
    have hh := hcode t (hs ht)
    have heq := (Finset.mem_filter.mp ht).2
    rw [heq] at hh
    exact hh.2.2
  refine ⟨b.1,b.2,part b,hs,hne,Finset.mem_range.mp hbounds.1,
    Finset.mem_range.mp hbounds.2,hmass,hspec,?_⟩
  apply original_union_cell_charge P (part b) (fun t => bin (Y t) grid b.1)
    (fun t => (bin (Y t) grid b.1).image grid) grid (2^b.1)
  · intro t ht
    exact (Finset.filter_subset _ _).trans (hsub t (hs ht))
  · intro t _ c hc
    exact (bin_fiber_bounds (Y t) grid b.1 hc).1

end OriginalShadingCellSelection
