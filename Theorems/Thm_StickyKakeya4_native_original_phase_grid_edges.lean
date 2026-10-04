import Theorems.Thm_StickyKakeya4_original_phase_grid_error
import Theorems.Thm_StickyKakeya4_original_phase_window_density

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalPhaseGridEdges
open Classical OriginalPhaseWindowGraph OriginalWCoreDynamics
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWPhysicalDisplacement
open OriginalWNormalizedPhase OriginalPhaseGridPopulation NativeOriginalPhaseWindowGraph
open NativeOriginalPhaseWindowEdges OriginalPhaseGridError

variable {P T L : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq L]

/-- The actual graph's original endpoints satisfy the phase-grid relation.
 The correct physical meshes are explicit, and their total error is 2*mesh. -/
theorem graph_edge_grid_phase_error
    (I : Finset (P × T)) (height x : P → ℝ) (base : T → ℝ)
    (theta : T → Fin 3 → ℝ) (offset : P → ℝ × ℝ) (v : T → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (labels : Finset L) (pick : L → Core S)
    (x₀ z₀ : ℝ) (xi₀ f₀ : ℝ × ℝ)
    {delta rho q IncErr DirErr Lip mesh : ℝ}
    (hmesh : 0 < mesh) (hrho : 0 < rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 1 ≤ Lip) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height x base (scalarSlope theta) p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I →
      ‖v t-offset p-F (height p) (scalarSlope theta t)‖ ≤ DirErr*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (a : L) (g : (ℝ × ℝ) × (ℤ × ℤ))
    (hEdge : (a,g) ∈ menuGraph labels pick
      (M I height (terminalGrid q theta) (scalarAngle q theta) S)) :
    let source := rep I height S hSV (pick a)
    let target := rep I height S hSV
      (next I height (terminalGrid q theta) (scalarAngle q theta) S (pick a) g)
    let c := scalarDecode q g.2.2-scalarDecode q g.2.1
    ‖gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x₀ xi₀ x offset target)-
      gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x₀ xi₀ x offset source)-
      c • (graphCoordinates rho Lip z₀ f₀ g.1.2 (F g.1.2)-
        graphCoordinates rho Lip z₀ f₀ g.1.1 (F g.1.1))‖ ≤
      max (3+12*IncErr) (3+8*DirErr)*rho+2*mesh := by
  let source := rep I height S hSV (pick a)
  let target := rep I height S hSV
    (next I height (terminalGrid q theta) (scalarAngle q theta) S (pick a) g)
  have he := graph_edge_normalized_phase_error I height x base theta offset v F Z S hSV
    labels pick x₀ z₀ xi₀ f₀ hrho hq hqρ hInc hDir hLip hdelta hinc hdir hheight hdiam hcluster a g hEdge
  exact rounded_phase_relation _ _
    (phaseCoordinates rho Lip x₀ xi₀ (x target) (offset target))
    (phaseCoordinates rho Lip x₀ xi₀ (x source) (offset source)) _
    (original_phase_grid_error hmesh rho Lip x₀ xi₀ x offset target)
    (original_phase_grid_error hmesh rho Lip x₀ xi₀ x offset source) he

end NativeOriginalPhaseGridEdges
