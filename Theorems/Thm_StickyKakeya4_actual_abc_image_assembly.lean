import Theorems.Thm_StickyKakeya4_actual_planar_target_cover
import Theorems.Thm_StickyKakeya4_planar_abc_balanced_normalization
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace ActualABCImageAssembly
open Classical NativeTangentGridCoarsening ActualPlanarTargetCover
abbrev Point := ℝ × ℝ
variable {X Y Z : Type*}
def embedEdge (p : X → Point) (b : Y → Point) (c : Z → ℝ) (e : X × (Y × Z)) : Point × (Point × ℝ) :=
  (p e.1,(b e.2.1,c e.2.2))
def imageGraph (E : Finset (X × (Y × Z))) (p : X → Point) (b : Y → Point) (c : Z → ℝ) := E.image (embedEdge p b c)
lemma embedEdge_injOn (S : Finset X) (T : Finset Y) (C : Finset Z)
    (E : Finset (X × (Y × Z))) (p : X → Point) (b : Y → Point) (c : Z → ℝ)
    (hE : E ⊆ S ×ˢ (T ×ˢ C)) (hp : Set.InjOn p (↑S)) (hb : Set.InjOn b (↑T)) (hc : Set.InjOn c (↑C)) :
    Set.InjOn (embedEdge p b c) (↑E) := by
  intro e he d hd hed
  obtain ⟨heS,heTC⟩ := Finset.mem_product.mp (hE he)
  obtain ⟨heT,heC⟩ := Finset.mem_product.mp heTC
  obtain ⟨hdS,hdTC⟩ := Finset.mem_product.mp (hE hd)
  obtain ⟨hdT,hdC⟩ := Finset.mem_product.mp hdTC
  have h₁ : p e.1=p d.1 := congrArg (fun q : Point × (Point × ℝ) => q.1) hed
  have h₂ : b e.2.1=b d.2.1 := congrArg (fun q : Point × (Point × ℝ) => q.2.1) hed
  have h₃ : c e.2.2=c d.2.2 := congrArg (fun q : Point × (Point × ℝ) => q.2.2) hed
  exact Prod.ext (hp heS hdS h₁) (Prod.ext (hb heT hdT h₂) (hc heC hdC h₃))
lemma imageGraph_card (S : Finset X) (T : Finset Y) (C : Finset Z)
    (E : Finset (X × (Y × Z))) (p : X → Point) (b : Y → Point) (c : Z → ℝ)
    (hE : E ⊆ S ×ˢ (T ×ˢ C)) (hp : Set.InjOn p (↑S)) (hb : Set.InjOn b (↑T)) (hc : Set.InjOn c (↑C)) :
    (imageGraph E p b c).card=E.card := Finset.card_image_of_injOn (embedEdge_injOn S T C E p b c hE hp hb hc)
lemma imageGraph_subset (S : Finset X) (T : Finset Y) (C : Finset Z)
    (E : Finset (X × (Y × Z))) (p : X → Point) (b : Y → Point) (c : Z → ℝ)
    (hE : E ⊆ S ×ˢ (T ×ˢ C)) : imageGraph E p b c ⊆ (S.image p) ×ˢ ((T.image b) ×ˢ (C.image c)) := by
  intro q hq
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hS,hTC⟩ := Finset.mem_product.mp (hE he)
  obtain ⟨hT,hC⟩ := Finset.mem_product.mp hTC
  exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hS,
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hT,Finset.mem_image_of_mem _ hC⟩⟩
/-- Actual point-image graph density follows from the retained original edge
 count and injectivity already proved by graph-aware projection. -/
theorem imageGraph_density (S : Finset X) (T : Finset Y) (C : Finset Z)
    (E : Finset (X × (Y × Z))) (p : X → Point) (b : Y → Point) (c : Z → ℝ)
    (hE : E ⊆ S ×ˢ (T ×ˢ C)) (hp : Set.InjOn p (↑S)) (hb : Set.InjOn b (↑T)) (hc : Set.InjOn c (↑C))
    {beta loss : ℝ} (hmass : beta*(S.card : ℝ)*(T.card : ℝ)*(C.card : ℝ) ≤ loss*(E.card : ℝ)) :
    beta*((S.image p).card : ℝ)*((T.image b).card : ℝ)*((C.image c).card : ℝ) ≤ loss*((imageGraph E p b c).card : ℝ) := by
  rw [Finset.card_image_of_injOn hp,Finset.card_image_of_injOn hb,Finset.card_image_of_injOn hc,
    imageGraph_card S T C E p b c hE hp hb hc]
  exact hmass
lemma imageGraph_output_cells (E : Finset (X × (Y × Z))) (p : X → Point) (b : Y → Point) (c : Z → ℝ) (mesh : ℝ) :
    planarCells (imageGraph E p b c) (fun e => e.1+e.2.2 • e.2.1) mesh=
      planarCells E (fun e => p e.1+c e.2.2 • b e.2.1) mesh := by
  simp only [planarCells,imageGraph,Finset.image_image,Function.comp_def,embedEdge]
/-- The actual sumset of the actual planar point-image graph has a small
 derived cover relative to its retained source image. Original targets need
 not belong to that image; their retention comparison pays the full loss. -/
theorem actual_ABC_sumset_cover {W : Type*} [DecidableEq W]
    (S : Finset X) (E : Finset (X × (Y × Z))) (targets : Finset W)
    (p : X → Point) (b : Y → Point) (c : Z → ℝ) (targetPoint : W → Point)
    (hp : Set.InjOn p (↑S)) {mesh error beta loss : ℝ}
    (hmesh : 0 < mesh) (herror : 0 ≤ error) (hbeta : 0 < beta)
    (htarget : ∀ e ∈ E, ∃ t ∈ targets, ‖p e.1+c e.2.2 • b e.2.1-targetPoint t‖ ≤ error)
    (hretention : beta*(targets.card : ℝ) ≤ loss*(S.card : ℝ)) :
    ((planarCells (imageGraph E p b c) (fun e => e.1+e.2.2 • e.2.1) mesh).card : ℝ) ≤
      (loss/beta)*(2*error/mesh+2)^2*((S.image p).card : ℝ) := by
  rw [imageGraph_output_cells]
  apply retained_target_cover E targets (S.image p) (fun e => p e.1+c e.2.2 • b e.2.1)
    targetPoint hmesh herror hbeta htarget
  simpa only [Finset.card_image_of_injOn hp] using hretention
/-- Ball and strip profiles of retained labels transfer to their actual
 injective point images exactly. -/
lemma filtered_image_card {W V : Type*} [DecidableEq V] (S : Finset W) (p : W → V)
    (hp : Set.InjOn p (↑S)) (test : V → Prop) [DecidablePred test] :
    ((S.image p).filter test).card=(S.filter (fun i => test (p i))).card := by
  rw [Finset.filter_image]
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  exact hp (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
end ActualABCImageAssembly
