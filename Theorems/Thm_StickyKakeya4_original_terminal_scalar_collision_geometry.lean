import Theorems.Thm_StickyKakeya4_original_scalar_collision_mass
import Theorems.Thm_StickyKakeya4_original_reference_angle_geometry
import Theorems.Thm_StickyKakeya4_native_original_phase_window_edges
import Theorems.Thm_StickyKakeya4_original_phase_grid_error
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalTerminalScalarCollisionGeometry
open Classical OriginalScalarCollisionMass OriginalReferenceAngleGeometry
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWCoreDynamics
open OriginalWPhysicalDisplacement OriginalWNormalizedPhase OriginalWGrainDrift
open OriginalPhaseWindowGraph NativeOriginalPhaseWindowGraph NativeOriginalPhaseWindowEdges
open OriginalPhaseGridPopulation OriginalPhaseGridError
/-- Scalar label equality supplies exactly the terminal slope difference
 used by the checked phase and grain identities. No full-direction claim. -/
theorem scalar_terminal_gap {T : Type*} (u : T → ℝ) {q : ℝ} (hq : 0 < q)
    (s t : T) (hcell : scalarTerminalCell q u s=scalarTerminalCell q u t) : |u s-u t| ≤ q := by
  have hl := (le_div_iff₀ hq).mp (Int.floor_le (u s/q))
  have hu := (div_lt_iff₀ hq).mp (Int.lt_floor_add_one (u s/q))
  have hl' := (le_div_iff₀ hq).mp (Int.floor_le (u t/q))
  have hu' := (div_lt_iff₀ hq).mp (Int.lt_floor_add_one (u t/q))
  change ⌊u s/q⌋=⌊u t/q⌋ at hcell
  rw [hcell] at hl hu
  exact abs_le.mpr ⟨by linarith only [hl,hu'],by linarith only [hu,hl']⟩
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
/-- Original scalar direction-ball populations supply the terminal fiber
 cap for the actual scalar collision label. -/
theorem scalar_terminal_fiber_cap (I : Finset (P × T)) (u : T → ℝ)
    {q radius U : ℝ} (hq : 0 < q) (hqR : q ≤ radius)
    (hball : ∀ p a, (((tubesAt I p).filter (fun t => |u t-a| ≤ radius)).card:ℝ) ≤ U) :
    ∀ p k, (((tubesAt I p).filter (fun t => scalarTerminalCell q u t=k)).card:ℝ) ≤ U := by
  intro p k
  have hsub : (tubesAt I p).filter (fun t => scalarTerminalCell q u t=k) ⊆
      (tubesAt I p).filter (fun t => |u t-q*(k:ℝ)| ≤ radius) := by
    intro t ht
    obtain ⟨ht,hcell⟩ := Finset.mem_filter.mp ht
    change ⌊u t/q⌋=k at hcell
    have hl := (le_div_iff₀ hq).mp (Int.floor_le (u t/q))
    have hu := (div_lt_iff₀ hq).mp (Int.lt_floor_add_one (u t/q))
    rw [hcell] at hl hu
    exact Finset.mem_filter.mpr ⟨ht,(abs_le.mpr ⟨by nlinarith only [hl,hq.le],by nlinarith only [hu]⟩).trans hqR⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hball p (q*(k:ℝ)))
/-- The original signed phase relation for scalar-terminal collisions is
 proved from the actual original incidence and field equations. -/
theorem scalar_witness_phase_relation
    (I : Finset (P × T)) (height x : P → ℝ) (base u angle : T → ℝ)
    (offset : P → ℝ × ℝ) (v : T → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z : Finset ℝ)
    (x0 z0 : ℝ) (xi0 f0 : ℝ × ℝ) {delta rho q IncErr DirErr Lip : ℝ}
    (hq : 0 < q) (hqrho : q ≤ rho) (hrho : 0 < rho) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr)
    (hLip : 1 ≤ Lip) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x base u p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hangle : ∀ t ∈ TwoTubePathCollisionCount.tubes I, |u t-angle t| ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height (scalarTerminalCell q u))
    (p1 p2 : P) (hp1 : (p1,w.1.tube₂) ∈ I) (hp2 : (p2,w.2.tube₂) ∈ I)
    (hz1 : height p1=height w.1.point₂) (hz2 : height p2=height w.2.point₂) :
    ‖phaseCoordinates rho Lip x0 xi0 (x p2) (offset p2)-phaseCoordinates rho Lip x0 xi0 (x p1) (offset p1)-
      (angle w.2.tube₁-angle w.1.tube₁) •
      (graphCoordinates rho Lip z0 f0 (height w.1.point₁) (F (height w.1.point₁))-
        graphCoordinates rho Lip z0 f0 (height w.1.point₀) (F (height w.1.point₀)))‖ ≤
      max (3+12*IncErr) (3+8*DirErr)*rho := by
  exact reference_original_normalized_phase I height x base u angle (scalarTerminalCell q u) offset v F Z x0 z0 xi0 f0
    hrho hInc hDir hLip hdelta hinc hdir hheight hdiam hcluster hangle
    (fun s t hc => (scalar_terminal_gap u hq s t hc).trans hqrho) w hw p1 p2 hp1 hp2 hz1 hz2
/-- The same scalar-terminal collision set satisfies the original physical
 grain drift. Full-direction W membership is neither used nor concluded. -/
theorem scalar_witness_grain_drift
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z : Finset ℝ)
    {A B IncErr DirErr Lip delta rho q : ℝ} (hq : 0 < q) (hqrho : q ≤ rho)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 0 ≤ Lip)
    (hd : 0 ≤ delta) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hincU : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖u t‖ ≤ B) (hF : ∀ z ∈ Z, ‖F z‖ ≤ A)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height (scalarTerminalCell q u))
    (p1 p2 : P) (hp1 : (p1,w.1.tube₂) ∈ I) (hp2 : (p2,w.2.tube₂) ∈ I)
    (hz1 : height p1=height w.1.point₂) (hz2 : height p2=height w.2.point₂) :
    ‖grainCoordinate height x y F p2-grainCoordinate height x y F p1‖ ≤
      ((4*B+1)*Lip+(12+4*A)*max DirErr (2*IncErr))*rho^2 := by
  apply original_witness_grain_drift I height (scalarTerminalCell q u) x y offset baseU u baseV v F Z
    hA hB hInc hDir hLip hd hrho hrho1 hdscale hincU hincV hdir hu hF hcluster hheight hdiam
  · intro s t hc
    exact (scalar_terminal_gap u hq s t hc).trans hqrho
  · exact hw
  · exact hp1
  · exact hp2
  · exact hz1
  · exact hz2
/-- Actual scalar-terminal menu edges have the full rounded phase relation
 needed downstream by BC coarsening and the old-target covering theorem. -/
theorem scalar_graph_edge_grid_relation {L : Type*} [DecidableEq L]
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
    (hEdge : (a,g) ∈ menuGraph labels pick (M I height (scalarTerminalCell q u) angle S)) :
    let source := rep I height S hSV (pick a)
    let target := rep I height S hSV (next I height (scalarTerminalCell q u) angle S (pick a) g)
    ‖gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x0 xi0 x offset target)-
      gridPoint mesh (phaseLabel (mesh*rho) (mesh*Lip*rho) x0 xi0 x offset source)-
      (g.2.2-g.2.1) • (graphCoordinates rho Lip z0 f0 g.1.2 (F g.1.2)-graphCoordinates rho Lip z0 f0 g.1.1 (F g.1.1))‖ ≤
      max (3+12*IncErr) (3+8*DirErr)*rho+2*mesh := by
  obtain ⟨w,hw,_hl,_hr,hm,hp1,hp2,hz1,hz2⟩ := graph_edge_original_witness I height (scalarTerminalCell q u) angle S hSV labels pick a g hEdge
  let source := rep I height S hSV (pick a)
  let target := rep I height S hSV (next I height (scalarTerminalCell q u) angle S (pick a) g)
  have he := scalar_witness_phase_relation I height x base u angle offset v F Z x0 z0 xi0 f0
    hq hqrho hrho hInc hDir hLip hdelta hinc hdir hheight hdiam hcluster hangle w hw source target hp1 hp2 hz1 hz2
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
end OriginalTerminalScalarCollisionGeometry
