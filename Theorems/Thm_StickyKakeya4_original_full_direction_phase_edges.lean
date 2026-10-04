import Theorems.Thm_StickyKakeya4_native_original_macro_printed_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalFullDirectionPhaseEdges
open Classical OriginalReferenceAngleGeometry OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWCoreDynamics
open OriginalWPhysicalDisplacement OriginalWNormalizedPhase OriginalWGrainDrift
open OriginalPhaseWindowGraph NativeOriginalPhaseWindowGraph NativeOriginalPhaseWindowEdges
open OriginalPhaseGridPopulation OriginalPhaseGridError
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
/-- Actual genuine full-direction W edges satisfy the rounded original
 phase relation with their unchanged original angle values. -/
theorem full_direction_graph_edge_grid_relation {L : Type*} [DecidableEq L]
    (I : Finset (P × T)) (height x : P → ℝ) (base u angle : T → ℝ)
    (offset : P → ℝ × ℝ) (v : T → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height) (labels : Finset L) (pick : L → Core S)
    (x0 z0 : ℝ) (xi0 f0 : ℝ × ℝ) {delta rho q IncErr DirErr Lip mesh : ℝ}
    (hmesh : 0 < mesh) (hq : 0 < q) (hqrho : q ≤ rho) (hrho : 0 < rho)
    (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 1 ≤ Lip) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x base u p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hangle : ∀ t ∈ TwoTubePathCollisionCount.tubes I, |u t-angle t| ≤ rho)
    (a : L) (g : (ℝ × ℝ) × (ℝ × ℝ))
    (hEdge : (a,g) ∈ menuGraph labels pick (M I height (OriginalMacroDirectionCells.directionCell (q/8) u v) angle S)) :
    let source := rep I height S hSV (pick a)
    let target := rep I height S hSV (next I height (OriginalMacroDirectionCells.directionCell (q/8) u v) angle S (pick a) g)
    ‖gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x0 xi0 x offset target)-
      gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x0 xi0 x offset source)-
      (g.2.2-g.2.1) • (graphCoordinates rho Lip z0 f0 g.1.2 (F g.1.2)-graphCoordinates rho Lip z0 f0 g.1.1 (F g.1.1))‖ ≤
      max (3+12*IncErr) (3+8*DirErr)*rho+2*mesh := by
  obtain ⟨w,hw,_hl,_hr,hm,hp1,hp2,hz1,hz2⟩ := graph_edge_original_witness I height (OriginalMacroDirectionCells.directionCell (q/8) u v) angle S hSV labels pick a g hEdge
  let source := rep I height S hSV (pick a)
  let target := rep I height S hSV (next I height (OriginalMacroDirectionCells.directionCell (q/8) u v) angle S (pick a) g)
  have hcell : ∀ s t, OriginalMacroDirectionCells.directionCell (q/8) u v s=
      OriginalMacroDirectionCells.directionCell (q/8) u v t → |u s-u t| ≤ rho := by
    intro s t hs
    exact (OriginalMacroDirectionCells.direction_cell_gap u v (by positivity : 0 < q/8) s t hs).1.trans
      (by linarith only [hq,hqrho])
  have he := reference_original_normalized_phase I height x base u angle
    (OriginalMacroDirectionCells.directionCell (q/8) u v) offset v F Z x0 z0 xi0 f0
    hrho hInc hDir hLip hdelta hinc hdir hheight hdiam hcluster hangle hcell
    w hw source target hp1 hp2 hz1 hz2
  have hm0 : height w.1.point₀=g.1.1 := congrArg (fun j => j.1.1) hm
  have hm1 : height w.1.point₁=g.1.2 := congrArg (fun j => j.1.2) hm
  have ha0 : angle w.1.tube₁=g.2.1 := congrArg (fun j => j.2.1) hm
  have ha1 : angle w.2.tube₁=g.2.2 := congrArg (fun j => j.2.2) hm
  rw [hm0,hm1,ha0,ha1] at he
  exact rounded_phase_relation _ _
    (phaseCoordinates rho Lip x0 xi0 (x target) (offset target))
    (phaseCoordinates rho Lip x0 xi0 (x source) (offset source)) _
    (original_phase_grid_error hmesh rho Lip x0 xi0 x offset target)
    (original_phase_grid_error hmesh rho Lip x0 xi0 x offset source) he
/-- Replacing the original fine height by its actual sampled height keeps
 the original target and pays only its proved curve displacement. -/
theorem sampled_direction_error (target source fine sampled anchor : ℝ × (ℝ × ℝ))
    {c error displacement bound : ℝ}
    (herror : ‖target-source-c • (fine-anchor)‖ ≤ error)
    (hnear : ‖fine-sampled‖ ≤ displacement) (hc : |c| ≤ bound) (hbound : 0 ≤ bound) :
    ‖target-source-c • (sampled-anchor)‖ ≤ error+bound*displacement := by
  have he : target-source-c • (sampled-anchor)=
      (target-source-c • (fine-anchor))+c • (fine-sampled) := by module
  rw [he]
  calc
    _ ≤ ‖target-source-c • (fine-anchor)‖+‖c • (fine-sampled)‖ := norm_add_le _ _
    _ = ‖target-source-c • (fine-anchor)‖+|c| *‖fine-sampled‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ error+bound*displacement := add_le_add herror (mul_le_mul hc hnear (norm_nonneg _) hbound)
end OriginalFullDirectionPhaseEdges
