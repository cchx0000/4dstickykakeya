import Theorems.Thm_StickyKakeya4_original_phase_window_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalPhaseWindowGraph
open Classical OriginalPhaseWindowGraph OriginalWCoreDynamics
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWPhysicalDisplacement
open OriginalWGrainDrift FinitePhaseFieldImages

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

/-- A slice of the persistent original core at one exact original height. -/
def heightSlice (S : Finset (ℝ × T)) (z : ℝ) : Finset (Core S) :=
  S.attach.filter (fun v => v.val.1=z)

/-- Literal reflected phase-grid label of an original point. -/
def phaseLabel (r tau x₀ : ℝ) (xi₀ : ℝ × ℝ) (x : P → ℝ)
    (offset : P → ℝ × ℝ) (p : P) : OriginalPhaseGridPopulation.Label :=
  (⌊(x p-x₀)/r⌋,normalPhaseCell tau xi₀ offset p)

/-- Original incidence mass and incidence/field errors construct a genuine
 phase-menu graph in a bounded enlargement of a maximal occupied grain cell.
 There is no population or output-density certificate among the hypotheses. -/
theorem exists_original_phase_window_graph
    (I : Finset (P × T)) (height x : P → ℝ) (y offset : P → ℝ × ℝ)
    (baseU : T → ℝ) (baseV v : T → ℝ × ℝ) (theta : T → Fin 3 → ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z : Finset ℝ)
    (r tau x₀ : ℝ) (xi₀ : ℝ × ℝ)
    {C D U alpha A B IncErr DirErr Lip delta rho q width : ℝ}
    (hI : I.Nonempty) (hC : 0 < C) (hU : 0 < U) (halpha : 0 ≤ alpha)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hLip : 0 ≤ Lip)
    (hd : 0 ≤ delta) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (hdscale : delta ≤ rho^2)
    (hq : 0 < q) (hqρ : q ≤ rho) (hwidth : 0 < width)
    (hdrift : ((4*B+1)*Lip+(12+4*A)*max DirErr (2*IncErr))*rho^2 ≤ width)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hterminal : ∀ p c,
      (((tubesAt I p).filter (fun t => terminalGrid q theta t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a,
      (((tubesAt I p).filter (fun t => scalarAngle q theta t=a)).card : ℝ) ≤ U)
    (hmass : alpha*(C^5*D^2*U*(Z.card : ℝ)^2)*(vertices I height).card ≤
      (witnesses I height (terminalGrid q theta)).card)
    (hincU : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height x baseU (scalarSlope theta) p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I →
      ‖v t-offset p-F (height p) (scalarSlope theta t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖scalarSlope theta t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ A)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ Lip*rho)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho) :
    ∃ S : Finset (ℝ × T), ∃ hSV : S ⊆ vertices I height,
      S.Nonempty ∧
      ((witnesses I height (terminalGrid q theta)).card : ℝ) ≤
        2*((RichWitnessCore.retained (witnesses I height (terminalGrid q theta))
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∃ z ∈ Z, ∃ k : GrainLabel, ∃ pick : OriginalPhaseGridPopulation.Label → Core S,
        IsWindowGraph (heightSlice S z)
          (fun s => grainCell width (grainCoordinate height x y F (rep I height S hSV s)))
          (fun s => phaseLabel r tau x₀ xi₀ x offset (rep I height S hSV s))
          ((Z ×ˢ Z) ×ˢ ((angles I (scalarAngle q theta)) ×ˢ (angles I (scalarAngle q theta))))
          (M I height (terminalGrid q theta) (scalarAngle q theta) S)
          (next I height (terminalGrid q theta) (scalarAngle q theta) S)
          (((alpha/4)*D^2*(Z.card : ℝ)^2)/U^2) k pick := by
  obtain ⟨S,hSV,hS,hhalf,hrich⟩ := OriginalCoreMenuDensity.exists_original_menu_rich_core
    I height (terminalGrid q theta) (scalarAngle q theta) Z hI hC hU halpha
    hheight hpoints hterminal hangular hmass
  obtain ⟨s,hs⟩ := hS
  let s₀ : Core S := ⟨s,hs⟩
  let z := s.1
  let E := heightSlice S z
  have hE : E.Nonempty := ⟨s₀,Finset.mem_filter.mpr ⟨Finset.mem_attach S s₀,rfl⟩⟩
  have hz : z ∈ Z := by
    have hr := rep_spec I height S hSV s₀
    have hp := hheight _ (Finset.mem_image_of_mem Prod.fst hr.1)
    simpa only [hr.2] using hp
  let grain := fun s : Core S => grainCell width
    (grainCoordinate height x y F (rep I height S hSV s))
  let phase := fun s : Core S => phaseLabel r tau x₀ xi₀ x offset (rep I height S hSV s)
  let menus := M I height (terminalGrid q theta) (scalarAngle q theta) S
  let successor := next I height (terminalGrid q theta) (scalarAngle q theta) S
  let alphabet := (Z ×ˢ Z) ×ˢ ((angles I (scalarAngle q theta)) ×ˢ (angles I (scalarAngle q theta)))
  let degree := ((alpha/4)*D^2*(Z.card : ℝ)^2)/U^2
  have hdegree : 0 ≤ degree := by dsimp [degree]; positivity
  have hmenu : ∀ s ∈ E, menus s ⊆ alphabet := by
    intro s _hs
    exact (hrich s.val s.property).2
  have hdeg : ∀ s ∈ E, degree ≤ ((menus s).card : ℝ) := by
    intro s _hs
    apply (div_le_iff₀ (sq_pos_of_pos hU)).mpr
    simpa only [menus,M,mul_comm] using (hrich s.val s.property).1
  have hnext : ∀ s ∈ E, ∀ j ∈ menus s,
      successor s j ∈ E ∧ grain (successor s j) ∈ neighborCells (grain s) := by
    intro s hs j hj
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_attach S _,?_⟩
      exact (next_preserves_height I height (terminalGrid q theta) (scalarAngle q theta) S s j).trans
        (Finset.mem_filter.mp hs).2
    · apply grainCell_neighbor hwidth
      exact (scalar_constructed_successor_grain_drift I height x y offset baseU baseV v theta F Z S hSV
        hA hB hInc hDir hLip hd hrho hrho1 hdscale hq hqρ
        hincU hincV hdir hu hF hcluster hheight hdiam s j hj).trans hdrift
  obtain ⟨k,pick,hgraph⟩ := exists_maximal_window_graph E hE grain phase alphabet menus successor
    hdegree hmenu hdeg hnext
  exact ⟨S,hSV,⟨s,hs⟩,hhalf,z,hz,k,pick,hgraph⟩

end NativeOriginalPhaseWindowGraph
