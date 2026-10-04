import Theorems.Thm_StickyKakeya4_original_menu_bc_graph
import Theorems.Thm_StickyKakeya4_original_phase_window_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalActualWindowBCGraph
open Classical Finset OriginalPhaseWindowGraph OriginalMenuBCGraph OriginalMenuSection
open OriginalHeightGraphCoarsening OriginalHeightGraphDensity DyadicOriginalFiberSelection
variable {V A : Type*} [DecidableEq A]
def heightBin (sigma z : ℝ) : ℤ := ⌊z/sigma⌋
/-- The enlarged phase alphabet is exactly the image of actual states in
 the nine neighboring grain cells. -/
theorem expanded_image_readback (E : Finset V) (grain : V → GrainLabel)
    (phase : V → A) (k : GrainLabel) :
    expanded E grain phase k=(E.filter (fun v => grain v ∈ neighborCells k)).image phase := by
  ext a
  simp only [expanded,occupied,mem_biUnion,mem_image,mem_filter]
  constructor
  · rintro ⟨g,hg,v,⟨hv,hvg⟩,hva⟩
    exact ⟨v,⟨hv,by simpa only [hvg] using hg⟩,hva⟩
  · rintro ⟨v,⟨hv,hvg⟩,hva⟩
    exact ⟨grain v,hvg,v,⟨hv,rfl⟩,hva⟩
/-- The actual window graph is sectioned and coarsened by literal height
 bins. The original menu, original scalar angle and original target survive
 on every output edge. The factor is exactly 9*2=18. -/
theorem exists_actual_window_BC_graph
    (E : Finset V) (grain : V → GrainLabel) (phase : V → A)
    (Z Phi : Finset ℝ) (menus : V → Finset ((ℝ × ℝ) × (ℝ × ℝ)))
    (next : V → ((ℝ × ℝ) × (ℝ × ℝ)) → V) (k : GrainLabel) (pick : A → V)
    (sigma : ℝ) {beta : ℝ} (hbeta : 0 < beta) (hZ : Z.Nonempty) (hPhi : Phi.Nonempty)
    (hWindow : IsWindowGraph E grain phase ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi)) menus next
      (beta*(Z.card:ℝ)^2*(Phi.card:ℝ)^2) k pick) :
    let X := expanded E grain phase k
    let G0 := menuGraph (occupied E grain phase k) pick menus
    let f := heightBin sigma
    X.Nonempty ∧ ∃ anchor ∈ Z ×ˢ Phi, ∃ j < levelCount Z,
      let Zj := bin Z f j
      let B := Zj.image f
      let G := coarseGraph (edgeBin (sectionGraph G0 anchor) Z f j) f
      Zj.Nonempty ∧ B.Nonempty ∧ G.Nonempty ∧ G ⊆ X ×ˢ (B ×ˢ Phi) ∧
      beta*(Z.card:ℝ) ≤ 9*(levelCount Z:ℝ)*(Zj.card:ℝ) ∧
      beta*(X.card:ℝ)*(B.card:ℝ)*(Phi.card:ℝ) ≤ 18*(levelCount Z:ℝ)*(G.card:ℝ) ∧
      (∀ b ∈ B, fiber Zj f b=fiber Z f b ∧ 2^j ≤ (fiber Z f b).card ∧
        (fiber Z f b).card < 2^(j+1)) ∧
      ∀ a b c, (a,(b,c)) ∈ G → ∃ z ∈ Zj, f z=b ∧
        (a,((anchor.1,z),(anchor.2,c))) ∈ G0 ∧
        pick a ∈ E ∧ grain (pick a)=k ∧ phase (pick a)=a ∧
        phase (next (pick a) ((anchor.1,z),(anchor.2,c))) ∈ X := by
  let X := expanded E grain phase k
  let G0 := menuGraph (occupied E grain phase k) pick menus
  let f := heightBin sigma
  obtain ⟨hOcc,hSub,_hCap,hPick,hG0,hMass,hTarget⟩ := hWindow
  have hX : X.Nonempty := hOcc.mono hSub
  have hX0 : (0:ℝ) < X.card := Nat.cast_pos.mpr hX.card_pos
  have hZ0 : (0:ℝ) < Z.card := Nat.cast_pos.mpr hZ.card_pos
  have hP0 : (0:ℝ) < Phi.card := Nat.cast_pos.mpr hPhi.card_pos
  have hSubG : G0 ⊆ X ×ˢ ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi)) := by
    intro e he
    obtain ⟨ha,hg⟩ := mem_product.mp (hG0 he)
    exact mem_product.mpr ⟨hSub ha,hg⟩
  have hDense : (beta/9)*(X.card:ℝ)*(Z.card:ℝ)^2*(Phi.card:ℝ)^2 ≤ (G0.card:ℝ) := by
    have hh : ((beta*(Z.card:ℝ)^2*(Phi.card:ℝ)^2)*(X.card:ℝ))/9 ≤ (G0.card:ℝ) :=
      (div_le_iff₀ (by norm_num : (0:ℝ)<9)).mpr (by simpa only [mul_comm] using hMass)
    exact (show (beta/9)*(X.card:ℝ)*(Z.card:ℝ)^2*(Phi.card:ℝ)^2=
      ((beta*(Z.card:ℝ)^2*(Phi.card:ℝ)^2)*(X.card:ℝ))/9 by ring).trans_le hh
  have hGne : G0.Nonempty := card_pos.mp (Nat.cast_pos.mp
    (lt_of_lt_of_le (by positivity : (0:ℝ)<(beta/9)*(X.card:ℝ)*(Z.card:ℝ)^2*(Phi.card:ℝ)^2) hDense))
  obtain ⟨anchor,hAnchor,j,hj,hEdges,hBin,hRet,hDen,hQuot,hFib,hWitness⟩ :=
    exists_actual_BC_graph X Z Phi G0 hGne hSubG f (show 0 ≤ beta/9 by positivity) hDense
  refine ⟨hX,anchor,hAnchor,j,hj,hBin,hBin.image f,hEdges.image _,hQuot,?_,?_,hFib,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hRet (by norm_num : (0:ℝ)≤9)
    nlinarith only [hh]
  · have hh := mul_le_mul_of_nonneg_left hDen (by norm_num : (0:ℝ)≤9)
    nlinarith only [hh]
  · intro a b c he
    obtain ⟨z,hz,hzb,hmenu⟩ := hWitness a b c he
    have ha := (mem_menuGraph _ _ _ a ((anchor.1,z),(anchor.2,c))).mp hmenu
    obtain ⟨hp,hg,hphase⟩ := hPick a ha.1
    exact ⟨z,hz,hzb,hmenu,hp,hg,hphase,hTarget a _ hmenu⟩
end OriginalActualWindowBCGraph
