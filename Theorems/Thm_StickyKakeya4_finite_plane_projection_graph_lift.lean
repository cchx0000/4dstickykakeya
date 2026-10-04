import Theorems.Thm_StickyKakeya4_finite_plane_projection_graph_core
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGraph

/-- Select actual representatives only for an already selected finite cell set. -/
lemma exists_selected_representatives {X U : Type*} (P : Finset X) (f : X → U)
    (K : Finset U) (hK : K ⊆ P.image f) :
    ∃ S : Finset X, S ⊆ P ∧ S.image f = K ∧ Set.InjOn f (↑S) ∧ S.card = K.card := by
  let P' := P.filter (fun i => f i ∈ K)
  have hP' : P'.image f = K := by
    apply Finset.Subset.antisymm
    · intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hi).2
    · intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hK hu)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hu⟩, rfl⟩
  obtain ⟨S, hSP', hSim, hSinj, hScard⟩ :=
    FinitePlaneProjectionGrid.exists_cell_representatives P' f
  refine ⟨S, hSP'.trans (Finset.filter_subset _ _), hSim.trans hP', hSinj, ?_⟩
  simpa only [hP'] using hScard

/-- The exact selected quotient edge set lifted to the chosen actual vertices. -/
def selectedEdges {X Y Z U V : Type*} (S : Finset X) (T : Finset Y) (C : Finset Z)
    (f : X → U) (g : Y → V) (H : Finset (U × (V × Z))) : Finset (X × (Y × Z)) :=
  (S ×ˢ (T ×ˢ C)).filter (fun e => quotientEdge f g e ∈ H)

lemma selectedEdges_subset_product {X Y Z U V : Type*}
    (S : Finset X) (T : Finset Y) (C : Finset Z) (f : X → U) (g : Y → V)
    (H : Finset (U × (V × Z))) : selectedEdges S T C f g H ⊆ S ×ˢ (T ×ˢ C) :=
  Finset.filter_subset _ _

lemma selectedEdges_card_le {X Y Z U V : Type*}
    (S : Finset X) (T : Finset Y) (C : Finset Z) (f : X → U) (g : Y → V)
    (H : Finset (U × (V × Z))) :
    (selectedEdges S T C f g H).card ≤ S.card * T.card * C.card := by
  simpa only [Finset.card_product, Nat.mul_assoc] using
    Finset.card_le_card (selectedEdges_subset_product S T C f g H)

lemma selectedEdges_image {X Y Z U V : Type*}
    (S : Finset X) (T : Finset Y) (C : Finset Z) (f : X → U) (g : Y → V)
    (H : Finset (U × (V × Z))) (hH : H ⊆ S.image f ×ˢ (T.image g ×ˢ C)) :
    (selectedEdges S T C f g H).image (quotientEdge f g) = H := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hw).2
  · intro e he
    obtain ⟨hef, hegC⟩ := Finset.mem_product.mp (hH he)
    obtain ⟨heg, heC⟩ := Finset.mem_product.mp hegC
    obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hef
    obtain ⟨j, hj, hgj⟩ := Finset.mem_image.mp heg
    have hq : quotientEdge f g (i, (j, e.2.2)) = e :=
      Prod.ext hfi (Prod.ext hgj rfl)
    exact Finset.mem_image.mpr ⟨(i, (j, e.2.2)), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hi, Finset.mem_product.mpr ⟨hj, heC⟩⟩, hq.symm ▸ he⟩, hq⟩

lemma quotientEdge_injOn_product {X Y Z U V : Type*}
    (S : Finset X) (T : Finset Y) (C : Finset Z) (f : X → U) (g : Y → V)
    (hf : Set.InjOn f (↑S)) (hg : Set.InjOn g (↑T)) :
    Set.InjOn (quotientEdge (Z := Z) f g) (↑(S ×ˢ (T ×ˢ C))) := by
  intro e he w hw hq
  obtain ⟨heS, heTC⟩ := Finset.mem_product.mp he
  obtain ⟨hwS, hwTC⟩ := Finset.mem_product.mp hw
  exact Prod.ext (hf heS hwS (congrArg Prod.fst hq))
    (Prod.ext (hg (Finset.mem_product.mp heTC).1 (Finset.mem_product.mp hwTC).1
      (congrArg (fun q => q.2.1) hq)) (congrArg (fun q => q.2.2) hq))

lemma selectedEdges_card {X Y Z U V : Type*}
    (S : Finset X) (T : Finset Y) (C : Finset Z) (f : X → U) (g : Y → V)
    (H : Finset (U × (V × Z))) (hH : H ⊆ S.image f ×ˢ (T.image g ×ˢ C))
    (hf : Set.InjOn f (↑S)) (hg : Set.InjOn g (↑T)) :
    (selectedEdges S T C f g H).card = H.card := by
  have hinj : Set.InjOn (quotientEdge f g) (↑(selectedEdges S T C f g H)) :=
    (quotientEdge_injOn_product S T C f g hf hg).mono
      (selectedEdges_subset_product S T C f g H)
  calc
    _ = ((selectedEdges S T C f g H).image (quotientEdge f g)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ = H.card := congrArg Finset.card (selectedEdges_image S T C f g H hH)

lemma selectedEdges_original_witness {X Y Z U V : Type*}
    (S : Finset X) (T : Finset Y) (C : Finset Z) (G : Finset (X × (Y × Z)))
    (f : X → U) (g : Y → V) (H : Finset (U × (V × Z)))
    (hH : H ⊆ quotientEdges G f g) :
    ∀ e ∈ selectedEdges S T C f g H, ∃ w ∈ G,
      f w.1 = f e.1 ∧ g w.2.1 = g e.2.1 ∧ w.2.2 = e.2.2 := by
  intro e he
  obtain ⟨w, hw, hq⟩ := Finset.mem_image.mp (hH (Finset.mem_filter.mp he).2)
  exact ⟨w, hw, congrArg Prod.fst hq, congrArg (fun q => q.2.1) hq,
    congrArg (fun q => q.2.2) hq⟩

lemma selectedEdges_support_left {X Y Z U V : Type*}
    (S : Finset X) (T : Finset Y) (C : Finset Z) (f : X → U) (g : Y → V)
    (H : Finset (U × (V × Z))) (hH : H ⊆ S.image f ×ˢ (T.image g ×ˢ C))
    (hf : Set.InjOn f (↑S)) (hS : S.image f = H.image Prod.fst) :
    (selectedEdges S T C f g H).image Prod.fst = S := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_product.mp (selectedEdges_subset_product S T C f g H he)).1
  · intro i hi
    have hfi : f i ∈ H.image Prod.fst := hS ▸ Finset.mem_image_of_mem f hi
    obtain ⟨q, hq, hqi⟩ := Finset.mem_image.mp hfi
    have hqim : q ∈ (selectedEdges S T C f g H).image (quotientEdge f g) :=
      (selectedEdges_image S T C f g H hH).symm ▸ hq
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hqim
    have heS := (Finset.mem_product.mp (selectedEdges_subset_product S T C f g H he)).1
    have hei : e.1 = i := hf heS hi ((congrArg Prod.fst heq).trans hqi)
    exact Finset.mem_image.mpr ⟨e, he, hei⟩

lemma selectedEdges_support_right {X Y Z U V : Type*}
    (S : Finset X) (T : Finset Y) (C : Finset Z) (f : X → U) (g : Y → V)
    (H : Finset (U × (V × Z))) (hH : H ⊆ S.image f ×ˢ (T.image g ×ˢ C))
    (hg : Set.InjOn g (↑T)) (hT : T.image g = H.image (fun q => q.2.1)) :
    (selectedEdges S T C f g H).image (fun e => e.2.1) = T := by
  apply Finset.Subset.antisymm
  · intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_product.mp (Finset.mem_product.mp
      (selectedEdges_subset_product S T C f g H he)).2).1
  · intro j hj
    have hgj : g j ∈ H.image (fun q => q.2.1) := hT ▸ Finset.mem_image_of_mem g hj
    obtain ⟨q, hq, hqj⟩ := Finset.mem_image.mp hgj
    have hqim : q ∈ (selectedEdges S T C f g H).image (quotientEdge f g) :=
      (selectedEdges_image S T C f g H hH).symm ▸ hq
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hqim
    have heT := (Finset.mem_product.mp (Finset.mem_product.mp
      (selectedEdges_subset_product S T C f g H he)).2).1
    have hej : e.2.1 = j := hg heT hj ((congrArg (fun q => q.2.1) heq).trans hqj)
    exact Finset.mem_image.mpr ⟨e, he, hej⟩

/-- Lift an already selected quotient graph without losing any edge and with an
original edge witness for each lifted edge. Representatives are chosen after H. -/
theorem exists_selected_graph_lift {X Y Z U V : Type*}
    (P : Finset X) (B : Finset Y) (C : Finset Z) (G : Finset (X × (Y × Z)))
    (f : X → U) (g : Y → V) (H : Finset (U × (V × Z)))
    (hG : G ⊆ P ×ˢ (B ×ˢ C)) (hH : H ⊆ quotientEdges G f g) :
    ∃ S : Finset X, ∃ T : Finset Y, ∃ E : Finset (X × (Y × Z)),
      S ⊆ P ∧ T ⊆ B ∧ Set.InjOn f (↑S) ∧ Set.InjOn g (↑T) ∧
      S.image f = H.image Prod.fst ∧ T.image g = H.image (fun q => q.2.1) ∧
      E = selectedEdges S T C f g H ∧ E ⊆ S ×ˢ (T ×ˢ C) ∧ E.card = H.card ∧
      E.image Prod.fst = S ∧ E.image (fun e => e.2.1) = T ∧
      ∀ e ∈ E, ∃ w ∈ G, f w.1 = f e.1 ∧ g w.2.1 = g e.2.1 ∧ w.2.2 = e.2.2 := by
  have hHprod : H ⊆ P.image f ×ˢ (B.image g ×ˢ C) :=
    hH.trans (quotientEdges_product P B C G f g hG)
  have hleft : H.image Prod.fst ⊆ P.image f := by
    intro u hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_product.mp (hHprod hq)).1
  have hright : H.image (fun q => q.2.1) ⊆ B.image g := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_product.mp (Finset.mem_product.mp (hHprod hq)).2).1
  obtain ⟨S, hSP, hSim, hSinj, _hScard⟩ :=
    exists_selected_representatives P f (H.image Prod.fst) hleft
  obtain ⟨T, hTB, hTim, hTinj, _hTcard⟩ :=
    exists_selected_representatives B g (H.image (fun q => q.2.1)) hright
  have hHrep : H ⊆ S.image f ×ˢ (T.image g ×ˢ C) := by
    rw [hSim, hTim]
    intro q hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem Prod.fst hq,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem (fun q => q.2.1) hq,
        (Finset.mem_product.mp (Finset.mem_product.mp (hHprod hq)).2).2⟩⟩
  exact ⟨S, T, selectedEdges S T C f g H, hSP, hTB, hSinj, hTinj, hSim, hTim, rfl,
    selectedEdges_subset_product S T C f g H, selectedEdges_card S T C f g H hHrep hSinj hTinj,
    selectedEdges_support_left S T C f g H hHrep hSinj hSim,
    selectedEdges_support_right S T C f g H hHrep hTinj hTim,
    selectedEdges_original_witness S T C G f g H hH⟩

lemma selected_graph_lift_colors {X Y Z : Type*}
    (S : Finset X) (T : Finset Y) (f : X → ℤ × ℤ) (g : Y → ℤ × ℤ)
    (H : Finset ((ℤ × ℤ) × ((ℤ × ℤ) × Z))) (ca cb : ℤ × ℤ)
    (hS : S.image f = H.image Prod.fst) (hT : T.image g = H.image (fun q => q.2.1))
    (hcolor : ∀ q ∈ H, FinitePlaneProjectionGrid.cellColor q.1 = ca ∧
      FinitePlaneProjectionGrid.cellColor q.2.1 = cb) :
    (∀ i ∈ S, FinitePlaneProjectionGrid.cellColor (f i) = ca) ∧
      ∀ j ∈ T, FinitePlaneProjectionGrid.cellColor (g j) = cb := by
  constructor
  · intro i hi
    have him : f i ∈ H.image Prod.fst := hS ▸ Finset.mem_image_of_mem f hi
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp him
    simpa only [heq] using (hcolor q hq).1
  · intro j hj
    have him : g j ∈ H.image (fun q => q.2.1) := hT ▸ Finset.mem_image_of_mem g hj
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp him
    simpa only [heq] using (hcolor q hq).2

open FinitePlaneProjectionGrid

/-- Fixed color and injective projected cells already separate every actual
representative. There is no further vertex thinning or graph loss. -/
lemma fixed_color_projection_separation {X : Type*} (P : Finset X) (p : X → Point3)
    (uv : ℝ × ℝ) {rho : ℝ} (hrho : 0 < rho) (ca : ℤ × ℤ)
    (hinj : Set.InjOn (fun i => projectedCell uv rho (p i)) (↑P))
    (hcolor : ∀ i ∈ P, cellColor (projectedCell uv rho (p i)) = ca) :
    ∀ i ∈ P, ∀ j ∈ P, i ≠ j →
      2 * rho < ‖projectionLinear uv (p i) - projectionLinear uv (p j)‖ := by
  intro i hi j hj hij
  have hcell : projectedCell uv rho (p i) ≠ projectedCell uv rho (p j) :=
    fun he => hij (hinj hi hj he)
  have hmod := (hcolor i hi).trans (hcolor j hj).symm
  have hfst := congrArg Prod.fst hmod
  have hsnd := congrArg Prod.snd hmod
  change 2 * rho < max |(project uv (p i)).1 - (project uv (p j)).1|
    |(project uv (p i)).2 - (project uv (p j)).2|
  by_cases hfirst : ⌊(project uv (p i)).1 / rho⌋ = ⌊(project uv (p j)).1 / rho⌋
  · have hsecond : ⌊(project uv (p i)).2 / rho⌋ ≠ ⌊(project uv (p j)).2 / rho⌋ := by
      intro he
      exact hcell (Prod.ext hfirst he)
    exact (same_residue_floor_separation hrho hsnd hsecond).trans_le (le_max_right _ _)
  · exact (same_residue_floor_separation hrho hfst hfirst).trans_le (le_max_left _ _)

end FinitePlaneProjectionGraph
