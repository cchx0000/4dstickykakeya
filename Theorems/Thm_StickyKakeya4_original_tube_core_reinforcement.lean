import Theorems.Thm_StickyKakeya4_original_planar_tube_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open scoped BigOperators
namespace OriginalTubeCoreReinforcement
open Classical OriginalThreeDimensionalCapCount
open OriginalPlanarTubePairCount OriginalPlanarTubeEnergy

/-- An actual pair-to-tube assignment pays each original graph fiber by
its actual retained-core population squared. -/
theorem original_core_pair_fiber {α : Type*} [DecidableEq α] (S : Finset α)
    (G : Finset (α × α)) (region : TubeCell → Finset α)
    (assign : α × α → TubeCell) (z : TubeCell)
    (hG : G⊆S.product S)
    (hassign : ∀ e∈G,e.1∈region (assign e) ∧ e.2∈region (assign e)) :
    ((G.filter (fun e => assign e=z)).card : ℝ) ≤
      ((S∩region z).card : ℝ)^2 := by
  have hsub : G.filter (fun e => assign e=z)⊆(S∩region z).product (S∩region z) := by
    intro e he
    obtain ⟨heG,heq⟩ := Finset.mem_filter.mp he
    obtain ⟨he1,he2⟩ := Finset.mem_product.mp (hG heG)
    have hs := hassign e heG
    rw [heq] at hs
    exact Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨he1,hs.1⟩,
      Finset.mem_inter.mpr ⟨he2,hs.2⟩⟩
  have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_product _ _)
  simpa only [pow_two,Nat.cast_mul] using
    (Nat.cast_le.mpr hc : ((G.filter (fun e => assign e=z)).card : ℝ) ≤
      ((S∩region z).card*(S∩region z).card : ℕ))

/-- Uniform original ambient richness and the actual square-energy sum
bound the number of representative tubes, with no resampling of the core. -/
theorem original_rich_family_count {α : Type*} [DecidableEq α] (Q : Finset α)
    (T : Finset TubeCell) (region : TubeCell → Finset α) (m E : ℝ)
    (hm : 0 ≤ m) (hrich : ∀ z∈T,m ≤ ((Q∩region z).card : ℝ))
    (henergy : (∑ z∈T,((Q∩region z).card : ℝ)^2) ≤ E) :
    (T.card : ℝ)*m^2 ≤ E := by
  calc
    _ = ∑ _z∈T,m^2 := by simp
    _ ≤ ∑ z∈T,((Q∩region z).card : ℝ)^2 :=
      Finset.sum_le_sum (fun z hz => pow_le_pow_left₀ hm (hrich z hz) 2)
    _ ≤ E := henergy

/-- A single deletion of low core-population tube fibers retains half of
an ORIGINAL graph. The ambient-rich family size is derived from its own
square energy; the desired core richness is not a graph-input hypothesis. -/
theorem original_core_rich_graph {α : Type*} [DecidableEq α] (Q S : Finset α)
    (G : Finset (α × α)) (T : Finset TubeCell)
    (region : TubeCell → Finset α) (assign : α × α → TubeCell)
    (m E ell : ℝ) (hm : 0 < m)
    (hG : G⊆S.product S) (hmap : ∀ e∈G,assign e∈T)
    (hassign : ∀ e∈G,e.1∈region (assign e) ∧ e.2∈region (assign e))
    (hrich : ∀ z∈T,m ≤ ((Q∩region z).card : ℝ))
    (henergy : (∑ z∈T,((Q∩region z).card : ℝ)^2) ≤ E)
    (hbudget : 2*E*ell^2 ≤ m^2*G.card) :
    ∃ G' : Finset (α × α),G'⊆G ∧ (G.card : ℝ) ≤ 2*G'.card ∧
      (∀ e∈G',assign e∈T ∧ e.1∈region (assign e) ∧ e.2∈region (assign e) ∧
        ell ≤ ((S∩region (assign e)).card : ℝ)) := by
  let G' := G.filter (fun e => ell ≤ ((S∩region (assign e)).card : ℝ))
  let B := G.filter (fun e => ¬ell ≤ ((S∩region (assign e)).card : ℝ))
  have hT := original_rich_family_count Q T region m E hm.le hrich henergy
  have hB : (B.card : ℝ) ≤ ell^2*T.card := by
    have hf (z : TubeCell) (hz : z∈B.image assign) :
        ((B.filter (fun e => assign e=z)).card : ℝ)*1 ≤ ell^2 := by
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
      have hless : ((S∩region (assign e)).card : ℝ) < ell :=
        lt_of_not_ge (Finset.mem_filter.mp he).2
      have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (S∩region (assign e)).card) hless.le 2
      have hb := original_core_pair_fiber S B region assign (assign e)
        ((Finset.filter_subset _ _).trans hG)
        (fun v hv => hassign v (Finset.mem_filter.mp hv).1)
      simpa only [mul_one] using hb.trans hsq
    have hcount := weighted_fiber_count B assign 1 (ell^2) hf
    have hsub : B.image assign⊆T := by
      intro z hz
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
      exact hmap e (Finset.mem_filter.mp he).1
    have hc := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hsub)) (sq_nonneg ell)
    have hcountB : (B.card : ℝ) ≤ ell^2*(B.image assign).card := by
      simpa only [mul_one] using hcount
    exact hcountB.trans hc
  have hpart : (G'.card : ℝ)+B.card=G.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=G)
      (fun e => ell ≤ ((S∩region (assign e)).card : ℝ))
  have hkeep : (G.card : ℝ) ≤ 2*G'.card := by
    have hb := mul_le_mul_of_nonneg_left hB (sq_nonneg m)
    have ht := mul_le_mul_of_nonneg_right hT (sq_nonneg ell)
    have hp := congrArg (fun u : ℝ => m^2*u) hpart
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hm)).mp
    nlinarith only [hb,ht,hbudget,hp]
  refine ⟨G',Finset.filter_subset _ _,hkeep,?_⟩
  intro e he
  obtain ⟨heG,hepop⟩ := Finset.mem_filter.mp he
  exact ⟨hmap e heG,(hassign e heG).1,(hassign e heG).2,hepop⟩

end OriginalTubeCoreReinforcement
