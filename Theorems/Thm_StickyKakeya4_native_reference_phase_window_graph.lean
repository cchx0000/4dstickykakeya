import Theorems.Thm_StickyKakeya4_original_reference_angle_geometry
import Theorems.Thm_StickyKakeya4_native_original_phase_window_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeReferencePhaseWindowGraph
open Classical OriginalReferenceAngleSelection OriginalReferenceAngleGeometry
open OriginalPhaseWindowGraph OriginalWCoreDynamics OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open OriginalWPhysicalDisplacement OriginalWGrainDrift NativeOriginalPhaseWindowGraph
variable {P T K : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]
/-- The maximal phase-window graph is constructed with the literal common
 source Phi alphabet. Its menu density is normalized against that full Phi;
 the tube-to-Phi angle assignment includes original realization errors. -/
theorem exists_reference_phase_window_graph
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ) (F : ℝ → ℝ →L[ℝ] ℝ × ℝ)
    (cell : T → K) (Z Phi : Finset ℝ) (hI : I.Nonempty) (hPhi : Phi.Nonempty)
    (r tau x₀ : ℝ) (xi₀ : ℝ × ℝ)
    {C D U alpha beta Aop B IncErr DirErr Lip delta rho width : ℝ}
    (hC : 0 < C) (hU : 0 < U) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hA : 0 ≤ Aop) (hB : 0 ≤ B) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 0 ≤ Lip)
    (hd : 0 ≤ delta) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hwidth : 0 < width) (hdrift : ((4*B+1)*Lip+(12+4*Aop)*max DirErr (2*IncErr))*rho^2 ≤ width)
    (hnear : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |u t-a| ≤ rho)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (hball : ∀ p a, (((tubesAt I p).filter (fun t => |u t-a| ≤ rho)).card : ℝ) ≤ U)
    (hmass : alpha*(C^5*D^2*U*(Z.card : ℝ)^2)*(vertices I height).card ≤ (witnesses I height cell).card)
    (hscale : 4*beta*U^2*(Phi.card : ℝ)^2 ≤ alpha*D^2)
    (hincU : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖u t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ Aop) (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho) (hcell : ∀ s t, cell s=cell t → ‖u s-u t‖ ≤ rho) :
    ∃ S : Finset (ℝ × T), ∃ hSV : S ⊆ vertices I height, S.Nonempty ∧
      ((witnesses I height cell).card : ℝ) ≤ 2*((RichWitnessCore.retained (witnesses I height cell)
        (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∃ z ∈ Z, ∃ k : GrainLabel, ∃ pick : OriginalPhaseGridPopulation.Label → Core S,
        IsWindowGraph (heightSlice S z)
          (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
          (fun s => phaseLabel r tau x₀ xi₀ x offset (rep I height S hSV s))
          ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi))
          (M I height cell (angle I u Phi hPhi rho hnear) S)
          (next I height cell (angle I u Phi hPhi rho hnear) S)
          (beta*(Z.card : ℝ)^2*(Phi.card : ℝ)^2) k pick := by
  let a := angle I u Phi hPhi rho hnear
  obtain ⟨S,hSV,hS,hhalf,hrich⟩ := exists_full_reference_rich_core I height cell u Z Phi hI hPhi rho hnear
    hC hU halpha hheight hpoints hterminal hball hmass hscale
  obtain ⟨s,hs⟩ := hS
  let s₀ : Core S := ⟨s,hs⟩
  let z := s.1
  let E := heightSlice S z
  have hE : E.Nonempty := ⟨s₀,Finset.mem_filter.mpr ⟨Finset.mem_attach S s₀,rfl⟩⟩
  have hz : z ∈ Z := by
    have hr := rep_spec I height S hSV s₀
    have hp := hheight _ (Finset.mem_image_of_mem Prod.fst hr.1)
    simpa only [hr.2] using hp
  let grain := fun s : Core S => grainCell width (grainCoordinate height x y F (rep I height S hSV s))
  let phase := fun s : Core S => phaseLabel r tau x₀ xi₀ x offset (rep I height S hSV s)
  let menus := M I height cell a S
  let successor := next I height cell a S
  have hmenu : ∀ s ∈ E, menus s ⊆ (Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi) := by
    intro s _hs
    exact (hrich s.val s.property).2
  have hdeg : ∀ s ∈ E, beta*(Z.card : ℝ)^2*(Phi.card : ℝ)^2 ≤ ((menus s).card : ℝ) := by
    intro s _hs
    exact (hrich s.val s.property).1
  have hnext : ∀ s ∈ E, ∀ j ∈ menus s, successor s j ∈ E ∧ grain (successor s j) ∈ neighborCells (grain s) := by
    intro s hs j hj
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_attach S _,
        (next_preserves_height I height cell a S s j).trans (Finset.mem_filter.mp hs).2⟩
    · apply grainCell_neighbor hwidth
      exact (constructed_reference_grain_drift I height x y offset baseU u baseV v F Z cell a S hSV
        hA hB hInc hDir hLip hd hrho hrho1 hdscale hincU hincV hdir hu hF hcluster hheight hdiam hcell s j hj).trans hdrift
  obtain ⟨k,pick,hgraph⟩ := exists_maximal_window_graph E hE grain phase ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi))
    menus successor (by positivity) hmenu hdeg hnext
  exact ⟨S,hSV,⟨s,hs⟩,hhalf,z,hz,k,pick,hgraph⟩
end NativeReferencePhaseWindowGraph
