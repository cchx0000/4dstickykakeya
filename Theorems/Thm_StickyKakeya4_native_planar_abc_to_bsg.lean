import Theorems.Thm_StickyKakeya4_native_planar_abc_input
import Theorems.Thm_StickyKakeya4_vector_original_graph_bsg
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace NativePlanarABCToBSG
open Classical NativePlanarABCInput VectorOriginalGraphBSG
open PlanarShiftedNearEnergy VectorGraphCollisionEnergy DyadicOriginalFiberSelection
open scoped Pointwise
/-- The constructed native cover and the vector BSG cover use the identical
 componentwise floor grid on the identical actual edge outputs. -/
theorem actual_output_grid_eq (G : Finset (Point × (Point × ℝ))) (mesh : ℝ) :
    NativeTangentGridCoarsening.planarCells G (fun e => e.1+e.2.2 • e.2.1) mesh =
      G.image (fun e => roundPoint mesh (e.1+productValue e.2)) := by rfl
/-- The BSG constants are fixed before all source sets and their density or
 cover constants. The actual source-constructed ABC data supplies every
 graph, box, separation, and output-cover hypothesis directly. -/
theorem actual_planar_input_dyadic_bsg {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K n0 : ℕ, 0 < K ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ exponent ballK angularK density lineWidth lineFraction coverK : ℝ,
      0 < density → 0 < coverK →
      ∀ data : Data (((2:ℝ)^n)⁻¹) exponent ballK angularK density lineWidth lineFraction coverK,
      let delta : ℝ := ((2:ℝ)^n)⁻¹
      let f := fun p => roundPoint (delta/2) (productValue p)
      let alpha := sourceDensity (data.B ×ˢ data.C) density coverK
      let r := alpha^K * delta^epsilon
      ∃ j < levelCount (data.B ×ˢ data.C), ∃ A' : Finset Point, ∃ F : Finset (Point × ℝ),
        A' ⊆ data.A ∧ F ⊆ (data.B ×ˢ data.C) ∧ F ⊆ bin (data.B ×ˢ data.C) f j ∧
        (bin (data.B ×ˢ data.C) f j).Nonempty ∧
        (data.G.filter (fun e => level (data.B ×ˢ data.C) f e.2=j)).Nonempty ∧
        r*data.A.card ≤ A'.card ∧
        (r*(density^2/coverK)/(196*(levelCount (data.B ×ˢ data.C):ℝ)))*(data.B ×ˢ data.C).card ≤ F.card ∧
        (∀ p ∈ F, ∀ q ∈ (data.B ×ˢ data.C), f q=f p → q ∈ F) ∧
        (((A'+F.image productValue-F.image productValue).image (roundPoint (delta/2))).card : ℝ) ≤
          49*(delta^(-2*epsilon)/alpha^(2*K))*data.A.card := by
  obtain ⟨K,n0,hK,hBSG⟩ := original_ABC_dyadic_bsg hepsilon
  refine ⟨K,n0,hK,?_⟩
  intro n hn exponent ballK angularK density lineWidth lineFraction coverK hd hM data
  have hA : ∀ a ∈ data.A, |a.1| ≤ 1 ∧ |a.2| ≤ 1 := by
    intro a ha
    exact max_le_iff.mp (data.boxA a ha)
  have hB : ∀ b ∈ data.B, |b.1| ≤ 1 ∧ |b.2| ≤ 1 := by
    intro b hb
    exact max_le_iff.mp (data.boxB b hb)
  have hsep : ∀ a ∈ data.A, ∀ b ∈ data.A, a ≠ b → ((2:ℝ)^n)⁻¹/2 ≤ ‖a-b‖ := by
    intro a ha b hb hab
    have hh := data.separatedA a ha b hb hab
    rw [dist_eq_norm] at hh
    have hm : 0 < ((2:ℝ)^n)⁻¹ := by positivity
    linarith only [hh,hm]
  have hdense : density*data.A.card*(data.B ×ˢ data.C).card ≤ (data.G.card:ℝ) := by
    rw [Finset.card_product,Nat.cast_mul]
    simpa only [mul_assoc] using data.graph_density
  have hcover : ((data.G.image (fun e => roundPoint (((2:ℝ)^n)⁻¹) (e.1+productValue e.2))).card : ℝ) ≤
      coverK*data.A.card := by
    rw [← actual_output_grid_eq]
    exact data.output_cover
  exact hBSG n hn density coverK hd hM data.A data.B data.C data.G
    data.nonemptyA data.nonemptyB data.nonemptyC hA hB data.boxC hsep data.graph_subset hdense hcover
/-- The exact density-to-cover parameter supplied by the original graph
 projection and old-target cover. No further combinatorial loss is hidden. -/
theorem original_density_cover_ratio {beta loss error rho : ℝ}
    (hb : beta ≠ 0) (hL : loss ≠ 0) :
    (beta/loss)^2/((loss/beta)*(4*error/rho+8)^2)=beta^3/(loss^3*(4*error/rho+8)^2) := by
  field_simp
end NativePlanarABCToBSG
