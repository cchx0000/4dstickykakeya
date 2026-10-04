import Theorems.Thm_StickyKakeya4_original_three_dimensional_literal_slab_cover
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
namespace OriginalFiniteCellWeights
open Classical

variable {α β : Type*} [DecidableEq β]

def occupied (P : Finset α) (code : α → β) : Finset β := P.image code

def pointFiber (P : Finset α) (code : α → β) (k : β) : Finset α :=
  P.filter (fun x => code x=k)

def pointWeight (P : Finset α) (code : α → β) (k : β) : ℝ :=
  (pointFiber P code k).card

def pairCode (code : α → β) (z : α × α) : β × β := (code z.1,code z.2)

def pairFiber (G : Finset (α × α)) (code : α → β) (z : β × β) : Finset (α × α) :=
  pointFiber G (pairCode code) z

def pairWeight (G : Finset (α × α)) (code : α → β) (z : β × β) : ℝ :=
  pointWeight G (pairCode code) z

lemma pointWeight_nonneg (P : Finset α) (code : α → β) (k : β) :
    0 ≤ pointWeight P code k := Nat.cast_nonneg _

lemma pairWeight_nonneg (G : Finset (α × α)) (code : α → β) (z : β × β) :
    0 ≤ pairWeight G code z := Nat.cast_nonneg _

/-- Every quotient atom has its literal number of original point labels. -/
theorem point_mass_readback (P : Finset α) (code : α → β) :
    ∑ k∈occupied P code,pointWeight P code k=(P.card : ℝ) := by
  unfold occupied pointWeight pointFiber
  exact_mod_cast (Finset.card_eq_sum_card_image code P).symm

/-- Every quotient edge keeps all original ordered pair labels, including
those whose two endpoints happen to lie in one cell. -/
theorem pair_mass_readback (G : Finset (α × α)) (code : α → β) :
    ∑ z∈occupied G (pairCode code),pairWeight G code z=(G.card : ℝ) := by
  exact point_mass_readback G (pairCode code)

theorem point_subset_mass_readback (P : Finset α) (code : α → β) (Q : Finset β) :
    ∑ k∈Q,pointWeight P code k=((P.filter (fun x => code x∈Q)).card : ℝ) := by
  unfold pointWeight pointFiber
  exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter P Q code

theorem pair_subset_mass_readback (G : Finset (α × α)) (code : α → β)
    (H : Finset (β × β)) :
    ∑ z∈H,pairWeight G code z=((G.filter (fun e => pairCode code e∈H)).card : ℝ) := by
  exact point_subset_mass_readback G (pairCode code) H

lemma pairFiber_subset_product (P : Finset α) (G : Finset (α × α)) (code : α → β)
    (hG : G⊆P.product P) (z : β × β) :
    pairFiber G code z⊆(pointFiber P code z.1).product (pointFiber P code z.2) := by
  intro e he
  obtain ⟨heG,hcode⟩ := Finset.mem_filter.mp he
  obtain ⟨he1,he2⟩ := Finset.mem_product.mp (hG heG)
  have hc1 := congrArg Prod.fst hcode
  have hc2 := congrArg Prod.snd hcode
  exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨he1,hc1⟩,
    Finset.mem_filter.mpr ⟨he2,hc2⟩⟩

theorem pairWeight_le_pointWeight_product (P : Finset α) (G : Finset (α × α))
    (code : α → β) (hG : G⊆P.product P) (z : β × β) :
    pairWeight G code z ≤ pointWeight P code z.1*pointWeight P code z.2 := by
  have h := Finset.card_le_card (pairFiber_subset_product P G code hG z)
  rw [Finset.product_eq_sprod,Finset.card_product] at h
  unfold pairWeight pointWeight
  exact_mod_cast h

lemma original_pair_occupied_endpoints (P : Finset α) (G : Finset (α × α))
    (code : α → β) (hG : G⊆P.product P) (e : α × α) (he : e∈G) :
    code e.1∈occupied P code ∧ code e.2∈occupied P code := by
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hG he)
  exact ⟨Finset.mem_image_of_mem code h1,Finset.mem_image_of_mem code h2⟩

/-- Original graph density is an exact weighted statement on the cell
quotient; no unweighted density or injectivity is asserted. -/
theorem original_graph_weighted_density (P : Finset α) (G : Finset (α × α))
    (code : α → β) (lam : ℝ) (h : lam*(P.card : ℝ)^2 ≤ (G.card : ℝ)) :
    lam*(∑ k∈occupied P code,pointWeight P code k)^2 ≤
      ∑ z∈occupied G (pairCode code),pairWeight G code z := by
  rwa [point_mass_readback,pair_mass_readback]

end OriginalFiniteCellWeights
