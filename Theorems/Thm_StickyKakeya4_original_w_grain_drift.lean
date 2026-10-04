import Theorems.Thm_StickyKakeya4_original_w_adapted_boxes

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalWGrainDrift
open Classical OriginalWWitnessCounts OriginalWPhysicalDisplacement OriginalWAdaptedBoxes
open OriginalWCoreDynamics OriginalWCoarseEscapeMenus TwoWalkBoxComparison

variable {P T K U V : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual original normal grain coordinate, distinct from the direction
 plane intercept xi. All old height and point labels remain unchanged. -/
def grainCoordinate (height : P → ℝ) (x : P → U) (y : P → V)
    (F : ℝ → U →L[ℝ] V) (p : P) : V := y p-F (height p) (x p)

/-- Original W partners remain in a grain window of width O(K*rho²+delta).
 The K dependence follows from primitive incidences and original direction
 graphs and is not replaced by an assumed common rho²-grain-cell label. -/
theorem original_witness_grain_drift
    (I : Finset (P × T)) (height : P → ℝ) (cell : T → K)
    (x : P → U) (y offset : P → V) (baseU u : T → U) (baseV v : T → V)
    (F : ℝ → U →L[ℝ] V) (Z : Finset ℝ)
    {A B IncErr DirErr Lip delta rho : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 0 ≤ Lip)
    (hd : 0 ≤ delta) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hincU : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖u t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ A)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hcell : ∀ s t, cell s=cell t → ‖u s-u t‖ ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell)
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂) :
    ‖grainCoordinate height x y F p₂-grainCoordinate height x y F p₁‖ ≤
      ((4*B+1)*Lip+(12+4*A)*max DirErr (2*IncErr))*rho^2 := by
  let E := max DirErr (2*IncErr)
  let D := originalData height x y offset u v F w p₁ p₂
  have hE : 0 ≤ E := hDir.trans (le_max_left _ _)
  have he : 2*(IncErr*delta) ≤ E*delta := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right DirErr (2*IncErr)) hd
    nlinarith
  have hBounds := original_data_bounds I height cell x y offset baseU u baseV v F Z
    hA hB (mul_nonneg hLip hrho) (mul_nonneg hE hd) hrho he
    (mul_le_mul_of_nonneg_right (le_max_left DirErr (2*IncErr)) hd)
    hincU hincV hdir hu hF hcluster hheight hdiam hcell w hw p₁ p₂ hp₁ hp₂ hz₁ hz₂
  have hn := sharp_normal_point_bound D A B E Lip delta rho rho hBounds hE hLip hd hrho hrho1
  have hZend := (witness_conditions I height cell hw).2.2.2.2.1
  have hidentity : grainCoordinate height x y F p₂-grainCoordinate height x y F p₁=D.dy-D.F₂ D.dx := by
    dsimp [grainCoordinate,D,originalData,originalWalk,Data.dy,Data.dx]
    rw [hz₁,hz₂,hZend,map_sub]
    abel
  rw [hidentity]
  have heScale := mul_le_mul_of_nonneg_left hdscale
    (mul_nonneg (show 0 ≤ 12+4*A by positivity) hE)
  change ‖D.dy-D.F₂ D.dx‖ ≤ ((4*B+1)*Lip+(12+4*A)*E)*rho^2
  nlinarith

/-- Native scalar-tangent grain drift for the actual deterministic original
 successor. This supplies the physical width for Section21 phase windows. -/
theorem scalar_constructed_successor_grain_drift
    (I : Finset (P × T)) (height : P → ℝ) (x : P → ℝ) (y offset : P → V)
    (baseU : T → ℝ) (baseV v : T → V) (theta : T → Fin 3 → ℝ)
    (F : ℝ → ℝ →L[ℝ] V) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    {A B IncErr DirErr Lip delta rho q : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 0 ≤ Lip)
    (hd : 0 ≤ delta) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hq : 0 < q) (hqρ : q ≤ rho)
    (hincU : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x baseU (scalarSlope theta) p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (scalarSlope theta t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖scalarSlope theta t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ A)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (state : Core S) (g : (ℝ × ℝ) × (ℤ × ℤ))
    (hg : g ∈ M I height (terminalGrid q theta) (scalarAngle q theta) S state) :
    ‖grainCoordinate height x y F (rep I height S hSV
        (next I height (terminalGrid q theta) (scalarAngle q theta) S state g))-
      grainCoordinate height x y F (rep I height S hSV state)‖ ≤
      ((4*B+1)*Lip+(12+4*A)*max DirErr (2*IncErr))*rho^2 := by
  obtain ⟨_hn,w,hw,hl,hr,_hm⟩ := next_spec I height (terminalGrid q theta) (scalarAngle q theta) S state g hg
  let target := next I height (terminalGrid q theta) (scalarAngle q theta) S state g
  have hlt : w.1.tube₂=state.val.2 := congrArg Prod.snd hl
  have hrt : w.2.tube₂=target.val.2 := congrArg Prod.snd hr
  have hp := rep_spec I height S hSV state
  have hqSpec := rep_spec I height S hSV target
  apply original_witness_grain_drift I height (terminalGrid q theta) x y offset baseU (scalarSlope theta)
    baseV v F Z hA hB hInc hDir hLip hd hrho hrho1 hdscale hincU hincV hdir hu hF hcluster hheight hdiam
    (fun s t heq => (scalar_terminal_grid_gap q hq theta s t heq).trans hqρ) w hw
    (rep I height S hSV state) (rep I height S hSV target)
  · simpa only [hlt] using hp.1
  · simpa only [hrt] using hqSpec.1
  · exact hp.2.trans (congrArg Prod.fst hl).symm
  · exact hqSpec.2.trans (congrArg Prod.fst hr).symm

end OriginalWGrainDrift
