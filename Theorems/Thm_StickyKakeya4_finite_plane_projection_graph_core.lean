import Theorems.Thm_StickyKakeya4_finite_plane_projection_separated
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
open Finset
open scoped BigOperators
noncomputable section
open Classical
namespace FinitePlaneProjectionGraph

def goodEdges {X Y Z : Type*} (G : Finset (X × (Y × Z))) (U : Finset X) (V : Finset Y) :
    Finset (X × (Y × Z)) := G.filter (fun e => e.1 ∈ U ∧ e.2.1 ∈ V)
lemma goodEdges_subset {X Y Z : Type*} (G : Finset (X × (Y × Z))) (U : Finset X) (V : Finset Y) :
    goodEdges G U V ⊆ G := Finset.filter_subset _ _
lemma goodEdges_product {X Y Z : Type*} (P : Finset X) (B : Finset Y) (C : Finset Z)
    (G : Finset (X × (Y × Z))) (U : Finset X) (V : Finset Y)
    (hG : G ⊆ P ×ˢ (B ×ˢ C)) : goodEdges G U V ⊆ U ×ˢ (V ×ˢ C) := by
  intro e he
  obtain ⟨heG, heU, heV⟩ := Finset.mem_filter.mp he
  have heC := (Finset.mem_product.mp (Finset.mem_product.mp (hG heG)).2).2
  exact Finset.mem_product.mpr ⟨heU, Finset.mem_product.mpr ⟨heV, heC⟩⟩

theorem deleted_edge_bound {X Y Z : Type*} (P : Finset X) (B : Finset Y) (C : Finset Z)
    (G : Finset (X × (Y × Z))) (U : Finset X) (V : Finset Y)
    (hG : G ⊆ P ×ˢ (B ×ˢ C)) :
    (G.card : ℝ) ≤ (goodEdges G U V).card +
      ((P \ U).card : ℝ) * B.card * C.card + (P.card : ℝ) * (B \ V).card * C.card := by
  have hsub : G \ goodEdges G U V ⊆
      ((P \ U) ×ˢ (B ×ˢ C)) ∪ (P ×ˢ ((B \ V) ×ˢ C)) := by
    intro e he
    obtain ⟨heG, heNot⟩ := Finset.mem_sdiff.mp he
    obtain ⟨heP, heBC⟩ := Finset.mem_product.mp (hG heG)
    obtain ⟨heB, heC⟩ := Finset.mem_product.mp heBC
    by_cases heU : e.1 ∈ U
    · have heV : e.2.1 ∉ V := fun hh => heNot (Finset.mem_filter.mpr ⟨heG, heU, hh⟩)
      exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨heP, Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨heB, heV⟩, heC⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_sdiff.mpr ⟨heP, heU⟩, Finset.mem_product.mpr ⟨heB, heC⟩⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardR : ((G \ goodEdges G U V).card : ℝ) ≤
      ((P \ U).card : ℝ) * B.card * C.card + (P.card : ℝ) * (B \ V).card * C.card := by
    have hh : ((G \ goodEdges G U V).card : ℝ) ≤
        (((P \ U) ×ˢ (B ×ˢ C)).card : ℝ) + (P ×ˢ ((B \ V) ×ˢ C)).card := by
      exact_mod_cast hcard
    simpa only [Finset.card_product, Nat.cast_mul, mul_assoc] using hh
  have hsum : ((G \ goodEdges G U V).card : ℝ) + (goodEdges G U V).card = G.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (goodEdges_subset G U V)
  linarith

lemma goodEdges_half_of_density {X Y Z : Type*}
    (P : Finset X) (B : Finset Y) (C : Finset Z) (G : Finset (X × (Y × Z)))
    (U : Finset X) (V : Finset Y) {beta : ℝ}
    (hG : G ⊆ P ×ˢ (B ×ˢ C))
    (hdense : beta * P.card * B.card * C.card ≤ (G.card : ℝ))
    (hbadP : ((P \ U).card : ℝ) ≤ beta / 4 * P.card)
    (hbadB : ((B \ V).card : ℝ) ≤ beta / 4 * B.card) :
    (G.card : ℝ) / 2 ≤ (goodEdges G U V).card := by
  have hh := deleted_edge_bound P B C G U V hG
  have h1 := mul_le_mul_of_nonneg_right hbadP (show 0 ≤ (B.card : ℝ) * C.card by positivity)
  have h2 := mul_le_mul_of_nonneg_right hbadB (show 0 ≤ (P.card : ℝ) * C.card by positivity)
  nlinarith
lemma goodEdges_three_quarters_of_density {X Y Z : Type*}
    (P : Finset X) (B : Finset Y) (C : Finset Z) (G : Finset (X × (Y × Z)))
    (U : Finset X) (V : Finset Y) {beta : ℝ}
    (hG : G ⊆ P ×ˢ (B ×ˢ C))
    (hdense : beta * P.card * B.card * C.card ≤ (G.card : ℝ))
    (hbadP : ((P \ U).card : ℝ) ≤ beta / 8 * P.card)
    (hbadB : ((B \ V).card : ℝ) ≤ beta / 8 * B.card) :
    3 * (G.card : ℝ) / 4 ≤ (goodEdges G U V).card := by
  have hh := deleted_edge_bound P B C G U V hG
  have h1 := mul_le_mul_of_nonneg_right hbadP (show 0 ≤ (B.card : ℝ) * C.card by positivity)
  have h2 := mul_le_mul_of_nonneg_right hbadB (show 0 ≤ (P.card : ℝ) * C.card by positivity)
  nlinarith

def quotientEdge {X Y Z U V : Type*} (f : X → U) (g : Y → V) (e : X × (Y × Z)) : U × (V × Z) :=
  (f e.1, (g e.2.1, e.2.2))
def quotientEdges {X Y Z U V : Type*} (G : Finset (X × (Y × Z))) (f : X → U) (g : Y → V) :
    Finset (U × (V × Z)) := G.image (quotientEdge f g)
lemma quotientEdges_product {X Y Z U V : Type*}
    (P : Finset X) (B : Finset Y) (C : Finset Z) (G : Finset (X × (Y × Z)))
    (f : X → U) (g : Y → V) (hG : G ⊆ P ×ˢ (B ×ˢ C)) :
    quotientEdges G f g ⊆ P.image f ×ˢ (B.image g ×ˢ C) := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hwP, hwBC⟩ := Finset.mem_product.mp (hG hw)
  obtain ⟨hwB, hwC⟩ := Finset.mem_product.mp hwBC
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem f hwP,
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem g hwB, hwC⟩⟩
lemma quotient_fiber_bound {X Y Z U V : Type*}
    (P : Finset X) (B : Finset Y) (C : Finset Z) (G : Finset (X × (Y × Z)))
    (f : X → U) (g : Y → V) (hG : G ⊆ P ×ˢ (B ×ˢ C)) (q : U × (V × Z)) :
    (G.filter (fun e => quotientEdge f g e = q)).card ≤
      (P.filter (fun i => f i = q.1)).card * (B.filter (fun j => g j = q.2.1)).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun e => (e.1, e.2.1))
  · intro e he
    obtain ⟨heG, heq⟩ := Finset.mem_filter.mp he
    have heP := (Finset.mem_product.mp (hG heG)).1
    have heB := (Finset.mem_product.mp (Finset.mem_product.mp (hG heG)).2).1
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨heP, congrArg Prod.fst heq⟩,
        Finset.mem_filter.mpr ⟨heB, congrArg (fun q => q.2.1) heq⟩⟩
  · intro e he d hd hed
    have heq := (Finset.mem_filter.mp he).2
    have hdq := (Finset.mem_filter.mp hd).2
    have hthird := congrArg (fun q => q.2.2) (heq.trans hdq.symm)
    have hfirst : e.1 = d.1 := congrArg (fun x : X × Y => x.1) hed
    have hsecond : e.2.1 = d.2.1 := congrArg (fun x : X × Y => x.2) hed
    exact Prod.ext hfirst (Prod.ext hsecond hthird)
theorem quotientEdges_card_bound {X Y Z U V : Type*}
    (P : Finset X) (B : Finset Y) (C : Finset Z) (G : Finset (X × (Y × Z)))
    (f : X → U) (g : Y → V) {DP DB : ℝ} (hDP : 0 ≤ DP) (_hDB : 0 ≤ DB)
    (hG : G ⊆ P ×ˢ (B ×ˢ C))
    (hPcell : ∀ i ∈ P, ((P.filter (fun k => f k = f i)).card : ℝ) ≤ DP)
    (hBcell : ∀ j ∈ B, ((B.filter (fun k => g k = g j)).card : ℝ) ≤ DB) :
    (G.card : ℝ) ≤ (DP * DB) * (quotientEdges G f g).card := by
  have hfiber : ∀ q ∈ quotientEdges G f g,
      ((G.filter (fun e => quotientEdge f g e = q)).card : ℝ) ≤ DP * DB := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    have heP := (Finset.mem_product.mp (hG he)).1
    have heB := (Finset.mem_product.mp (Finset.mem_product.mp (hG he)).2).1
    have hh : ((G.filter (fun w => quotientEdge f g w = quotientEdge f g e)).card : ℝ) ≤
        ((P.filter (fun i => f i = f e.1)).card : ℝ) *
          (B.filter (fun j => g j = g e.2.1)).card := by
      exact_mod_cast quotient_fiber_bound P B C G f g hG (quotientEdge f g e)
    exact hh.trans (mul_le_mul (hPcell _ heP) (hBcell _ heB) (by positivity) hDP)
  calc
    _ = ∑ q ∈ quotientEdges G f g, ((G.filter (fun e => quotientEdge f g e = q)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image (quotientEdge f g) G
    _ ≤ ∑ _q ∈ quotientEdges G f g, DP * DB := Finset.sum_le_sum hfiber
    _ = _ := by simp [mul_comm]
theorem exists_edge_color {Z : Type*} (G : Finset ((ℤ × ℤ) × ((ℤ × ℤ) × Z))) :
    ∃ ca ∈ FinitePlaneProjectionGrid.nineColors, ∃ cb ∈ FinitePlaneProjectionGrid.nineColors,
      ∃ H : Finset ((ℤ × ℤ) × ((ℤ × ℤ) × Z)), H ⊆ G ∧ G.card ≤ 81 * H.card ∧
        ∀ e ∈ H, FinitePlaneProjectionGrid.cellColor e.1 = ca ∧
          FinitePlaneProjectionGrid.cellColor e.2.1 = cb := by
  let colors := FinitePlaneProjectionGrid.nineColors ×ˢ FinitePlaneProjectionGrid.nineColors
  let f := fun e : (ℤ × ℤ) × ((ℤ × ℤ) × Z) =>
    (FinitePlaneProjectionGrid.cellColor e.1, FinitePlaneProjectionGrid.cellColor e.2.1)
  let pop := fun c => (G.filter (fun e => f e = c)).card
  have hnon : colors.Nonempty := ⟨(FinitePlaneProjectionGrid.cellColor (0, 0),
    FinitePlaneProjectionGrid.cellColor (0, 0)), Finset.mem_product.mpr
      ⟨FinitePlaneProjectionGrid.cellColor_mem _, FinitePlaneProjectionGrid.cellColor_mem _⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image colors pop hnon
  have hsum : G.card = ∑ d ∈ colors, pop d := Finset.card_eq_sum_card_fiberwise
    (fun e _ => Finset.mem_product.mpr
      ⟨FinitePlaneProjectionGrid.cellColor_mem _, FinitePlaneProjectionGrid.cellColor_mem _⟩)
  have hcard : G.card ≤ 81 * pop c := by
    calc
      _ = ∑ d ∈ colors, pop d := hsum
      _ ≤ ∑ _d ∈ colors, pop c := Finset.sum_le_sum (fun d hd => hmax d hd)
      _ = _ := by simp [colors, FinitePlaneProjectionGrid.nineColors_card]
  refine ⟨c.1, (Finset.mem_product.mp hc).1, c.2, (Finset.mem_product.mp hc).2,
    G.filter (fun e => f e = c), Finset.filter_subset _ _, hcard, ?_⟩
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  exact ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩
end FinitePlaneProjectionGraph
