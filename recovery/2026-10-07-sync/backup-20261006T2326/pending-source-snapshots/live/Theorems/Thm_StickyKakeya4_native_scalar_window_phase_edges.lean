import Theorems.Thm_StickyKakeya4_original_reference_angle_geometry
import Theorems.Thm_StickyKakeya4_original_reference_angle_selection
import Theorems.Thm_StickyKakeya4_original_terminal_scalar_collision_geometry
import Theorems.Thm_StickyKakeya4_native_original_phase_window_edges
import Theorems.Thm_StickyKakeya4_original_phase_grid_error

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeScalarWindowPhaseEdges
open Classical OriginalReferenceAngleGeometry OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open OriginalWCoreDynamics OriginalWPhysicalDisplacement OriginalWNormalizedPhase
open OriginalPhaseWindowGraph NativeOriginalPhaseWindowGraph NativeOriginalPhaseWindowEdges
open OriginalPhaseGridPopulation OriginalPhaseGridError OriginalTerminalScalarCollisionGeometry

/-- The scalar-terminal window uses its own actual reference-Phi angle and
its own actual W witness. Full-direction terminal membership is not needed.
Both physical phase meshes are the exact normalized-coordinate meshes. -/
theorem graph_edge_grid_relation {P T L : Type*}
    [DecidableEq P] [DecidableEq T] [DecidableEq L]
    (I : Finset (P × T)) (height x : P → ℝ) (base u : T → ℝ)
    (offset : P → ℝ × ℝ) (v : T → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z Phi : Finset ℝ) (hPhi : Phi.Nonempty)
    (S : Finset (ℝ × T)) (hSV : S⊆vertices I height)
    (labels : Finset L) (pick : L → Core S)
    (x0 z0 : ℝ) (xi0 f0 : ℝ × ℝ) {delta rho q IncErr DirErr Lip mesh : ℝ}
    (hmesh : 0<mesh) (hq : 0<q) (hqrho : q≤rho) (hrho : 0<rho)
    (hInc : 0≤IncErr) (hDir : 0≤DirErr) (hLip : 1≤Lip) (hdelta : delta≤rho^2)
    (hnear : ∀t∈TwoTubePathCollisionCount.tubes I,∃a∈Phi,|u t-a|≤rho)
    (hinc : ∀p t,(p,t)∈I → ‖incidenceResidual height x base u p t‖≤IncErr*delta)
    (hdir : ∀p t,(p,t)∈I → ‖v t-offset p-F (height p) (u t)‖≤DirErr*delta)
    (hheight : ∀p∈TwoTubePathCollisionCount.points I,height p∈Z)
    (hdiam : ∀s∈Z,∀t∈Z,|s-t|≤rho)
    (hcluster : ∀s∈Z,∀t∈Z,‖F s-F t‖≤Lip*rho) :
    let angle:=OriginalReferenceAngleSelection.angle I u Phi hPhi rho hnear
    ∀a : L,∀g : (ℝ × ℝ) × (ℝ × ℝ),
    (a,g)∈menuGraph labels pick (M I height (scalarTerminalCell q u) angle S) →
    let source:=rep I height S hSV (pick a)
    let target:=rep I height S hSV (next I height (scalarTerminalCell q u) angle S (pick a) g)
    ‖gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x0 xi0 x offset target)-
      gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x0 xi0 x offset source)-
      (g.2.2-g.2.1) • (graphCoordinates rho Lip z0 f0 g.1.2 (F g.1.2)-
        graphCoordinates rho Lip z0 f0 g.1.1 (F g.1.1))‖≤
      max (3+12*IncErr) (3+8*DirErr)*rho+2*mesh := by
  intro angle a g hEdge source target
  obtain ⟨w,hw,_hl,_hr,hm,hp1,hp2,hz1,hz2⟩:=graph_edge_original_witness
    I height (scalarTerminalCell q u) angle S hSV labels pick a g hEdge
  have hangle : ∀t∈TwoTubePathCollisionCount.tubes I,|u t-angle t|≤rho := by
    intro t ht
    exact (OriginalReferenceAngleSelection.angle_spec I u Phi hPhi rho hnear t ht).2
  have hcell : ∀s t,scalarTerminalCell q u s=scalarTerminalCell q u t → |u s-u t|≤rho :=
    fun s t he => (scalar_terminal_gap u hq s t he).trans hqrho
  have he:=reference_original_normalized_phase I height x base u angle (scalarTerminalCell q u)
    offset v F Z x0 z0 xi0 f0 hrho hInc hDir hLip hdelta hinc hdir hheight hdiam hcluster
    hangle hcell w hw source target hp1 hp2 hz1 hz2
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

end NativeScalarWindowPhaseEdges
