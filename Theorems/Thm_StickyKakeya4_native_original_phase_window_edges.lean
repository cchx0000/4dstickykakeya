import Theorems.Thm_StickyKakeya4_native_original_phase_window_population
import Theorems.Thm_StickyKakeya4_original_w_normalized_phase

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalPhaseWindowEdges
open Classical OriginalPhaseWindowGraph OriginalWCoreDynamics
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWPhysicalDisplacement
open OriginalWNormalizedPhase

variable {P T L K A : Type*} [DecidableEq P] [DecidableEq T]
  [DecidableEq L] [DecidableEq K] [DecidableEq A]

/-- Every finite graph edge carries the selected genuine original W witness.
 Both representatives are original incidence points on the correct endpoint
 tubes and at the original endpoint heights. -/
theorem graph_edge_original_witness
    (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → A)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (labels : Finset L) (pick : L → Core S) (a : L) (g : (ℝ × ℝ) × (A × A))
    (hEdge : (a,g) ∈ menuGraph labels pick (M I height cell angle S)) :
    ∃ w ∈ witnesses I height cell,
      endpoint height w.1=(pick a).val ∧
      endpoint height w.2=(next I height cell angle S (pick a) g).val ∧
      menu height angle w=g ∧
      (rep I height S hSV (pick a),w.1.tube₂) ∈ I ∧
      (rep I height S hSV (next I height cell angle S (pick a) g),w.2.tube₂) ∈ I ∧
      height (rep I height S hSV (pick a))=height w.1.point₂ ∧
      height (rep I height S hSV (next I height cell angle S (pick a) g))=height w.2.point₂ := by
  have hg := ((mem_menuGraph _ _ _ a g).mp hEdge).2
  obtain ⟨_hh,w,hw,hl,hr,hm⟩ := next_spec I height cell angle S (pick a) g hg
  have hlt : w.1.tube₂=(pick a).val.2 := congrArg Prod.snd hl
  have hrt : w.2.tube₂=(next I height cell angle S (pick a) g).val.2 := congrArg Prod.snd hr
  have hs := rep_spec I height S hSV (pick a)
  have ht := rep_spec I height S hSV (next I height cell angle S (pick a) g)
  refine ⟨w,hw,hl,hr,hm,?_,?_,?_,?_⟩
  · simpa only [hlt] using hs.1
  · simpa only [hrt] using ht.1
  · exact hs.2.trans (congrArg Prod.fst hl).symm
  · exact ht.2.trans (congrArg Prod.fst hr).symm

/-- The actual sparse phase-menu graph satisfies the signed, anisotropically
 normalized Section21 relation with its own original menu coordinates. No
 approximate-additive graph condition is supplied. -/
theorem graph_edge_normalized_phase_error
    (I : Finset (P × T)) (height x : P → ℝ) (base : T → ℝ)
    (theta : T → Fin 3 → ℝ) (offset : P → ℝ × ℝ) (v : T → ℝ × ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    (labels : Finset L) (pick : L → Core S)
    (x₀ z₀ : ℝ) (xi₀ f₀ : ℝ × ℝ)
    {delta rho q IncErr DirErr Lip : ℝ}
    (hrho : 0 < rho) (hq : 0 < q) (hqρ : q ≤ rho)
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
    ‖phaseCoordinates rho Lip x₀ xi₀ (x target) (offset target)-
      phaseCoordinates rho Lip x₀ xi₀ (x source) (offset source)-
      c • (graphCoordinates rho Lip z₀ f₀ g.1.2 (F g.1.2)-
        graphCoordinates rho Lip z₀ f₀ g.1.1 (F g.1.1))‖ ≤
      max (3+12*IncErr) (3+8*DirErr)*rho := by
  obtain ⟨w,hw,_hl,_hr,hm,hp₁,hp₂,hz₁,hz₂⟩ :=
    graph_edge_original_witness I height (terminalGrid q theta) (scalarAngle q theta)
      S hSV labels pick a g hEdge
  have he := scalar_original_normalized_phase I height x base theta offset v F Z x₀ z₀ xi₀ f₀
    hrho hq hqρ hInc hDir hLip hdelta hinc hdir hheight hdiam hcluster w hw
    (rep I height S hSV (pick a))
    (rep I height S hSV (next I height (terminalGrid q theta) (scalarAngle q theta) S (pick a) g))
    hp₁ hp₂ hz₁ hz₂
  have hm₀ : height w.1.point₀=g.1.1 := congrArg (fun j => j.1.1) hm
  have hm₁ : height w.1.point₁=g.1.2 := congrArg (fun j => j.1.2) hm
  have ha₀ : scalarAngle q theta w.1.tube₁=g.2.1 := congrArg (fun j => j.2.1) hm
  have ha₁ : scalarAngle q theta w.2.tube₁=g.2.2 := congrArg (fun j => j.2.2) hm
  simpa only [hm₀,hm₁,ha₀,ha₁] using he

end NativeOriginalPhaseWindowEdges
