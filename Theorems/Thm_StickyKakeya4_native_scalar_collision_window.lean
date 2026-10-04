import Theorems.Thm_StickyKakeya4_original_terminal_scalar_collision_geometry
import Theorems.Thm_StickyKakeya4_native_original_graph_density_costs
import Theorems.Thm_StickyKakeya4_native_reference_phase_window_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeScalarCollisionWindow
open Classical OriginalScalarCollisionMass OriginalTerminalScalarCollisionGeometry NativeOriginalGraphDensityCosts
open OriginalReferenceAngleSelection NativeReferencePhaseWindowGraph OriginalPhaseWindowGraph OriginalWCoreDynamics
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWPhysicalDisplacement OriginalWGrainDrift
open NativeOriginalPhaseWindowGraph
variable {P T : Type*} [DecidableEq P] [DecidableEq T]
/-- The scalar-terminal phase graph is constructed from original incidence
 populations and source geometry. W mass, the terminal-fiber bound, menu
 density and the terminal gap are all derived here. Printed full-direction
 W membership is neither an input nor a conclusion of this caller. -/
theorem exists_scalar_original_phase_window_graph
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (Z Phi : Finset ℝ) (hI : I.Nonempty) (hPhi : Phi.Nonempty)
    (q r tau x₀ : ℝ) (xi₀ : ℝ × ℝ)
    {C D U lambda Aop B IncErr DirErr Lip delta rho width : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hU : 0 < U) (hlambda : 0 < lambda)
    (hq : 0 < q) (hqrho : q ≤ rho)
    (hA : 0 ≤ Aop) (hB : 0 ≤ B) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 0 ≤ Lip)
    (hd : 0 ≤ delta) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hwidth : 0 < width) (hdrift : ((4*B+1)*Lip+(12+4*Aop)*max DirErr (2*IncErr))*rho^2 ≤ width)
    (hnear : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |u t-a| ≤ rho)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hball : ∀ p a, (((tubesAt I p).filter (fun t => |u t-a| ≤ rho)).card : ℝ) ≤ U)
    (hdegree : D*(TwoTubePathCollisionCount.points I).card ≤ (I.card:ℝ))
    (hheightMass : lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card)
    (hincU : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖u t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ Aop) (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho) :
    let alpha := collisionAlpha lambda C (2*rho/q+2) D U Phi.card
    let beta := menuBeta alpha D U Phi.card
    ∃ S : Finset (ℝ × T), ∃ hSV : S ⊆ vertices I height, S.Nonempty ∧
      ((witnesses I height (scalarTerminalCell q u)).card : ℝ) ≤ 2*((RichWitnessCore.retained (witnesses I height (scalarTerminalCell q u))
        (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∃ z ∈ Z, ∃ k : GrainLabel, ∃ pick : OriginalPhaseGridPopulation.Label → Core S,
        IsWindowGraph (heightSlice S z)
          (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
          (fun s => phaseLabel r tau x₀ xi₀ x offset (rep I height S hSV s))
          ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi))
          (M I height (scalarTerminalCell q u) (angle I u Phi hPhi rho hnear) S)
          (next I height (scalarTerminalCell q u) (angle I u Phi hPhi rho hnear) S)
          (beta*(Z.card : ℝ)^2*(Phi.card : ℝ)^2) k pick := by
  let alpha := collisionAlpha lambda C (2*rho/q+2) D U Phi.card
  let beta := menuBeta alpha D U Phi.card
  have hN : (0:ℝ)<Phi.card := Nat.cast_pos.mpr hPhi.card_pos
  have ha : 0 < alpha := by dsimp [alpha,collisionAlpha]; positivity
  have hb : 0 < beta := menuBeta_pos ha hD hU hN
  have hm := scalar_original_collision_mass I height u Z Phi hI hPhi hq hrho hC hD hU hlambda.le
    hheight hdegree hheightMass hnear
  have ht := scalar_terminal_fiber_cap I u hq hqrho hball
  have hscale : 4*beta*U^2*(Phi.card:ℝ)^2 ≤ alpha*D^2 :=
    (menu_scale_eq alpha D hU.ne' hN.ne').le
  exact exists_reference_phase_window_graph I height x y offset baseU u baseV v F
    (scalarTerminalCell q u) Z Phi hI hPhi r tau x₀ xi₀ hC hU ha.le hb.le
    hA hB hInc hDir hLip hd hrho hrho1 hdscale hwidth hdrift hnear hpoints ht hball hm hscale
    hincU hincV hdir hu hF hcluster hheight hdiam
    (fun s t hc => (scalar_terminal_gap u hq s t hc).trans hqrho)
end NativeScalarCollisionWindow
