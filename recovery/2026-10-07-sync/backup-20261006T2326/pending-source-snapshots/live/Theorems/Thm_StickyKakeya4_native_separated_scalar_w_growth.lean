import Theorems.Thm_StickyKakeya4_native_original_w_end_to_end
import Theorems.Thm_StickyKakeya4_original_separated_height_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

namespace NativeSeparatedScalarWGrowth
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWPhysicalDisplacement
open OriginalWPhysicalGrowth NativeOriginalWEndToEnd Classical
noncomputable section

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

/-- Physical tube thickness and the literal separation of original heights
are independent inputs; no origin shift or point relabeling is performed. -/
/-- Apply native a=1 growth to the constructed original core dynamics. The
successor, representative, displacement, and time cap are all DERIVED. The
escape bound is the already-proved output of the original fine-Frostman core. -/
theorem scalar_growth_of_constructed_core
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ)
    (base : T → ℝ) (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height) (root : OriginalWCoreDynamics.Core S)
    {delta rho q Err h beta timeMesh : ℝ} (hI : I.Nonempty)
    (_hdeltapos : 0 < delta) (hrhopos : 0 < rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hErr : 0 ≤ Err) (hdelta : delta ≤ rho^2) (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta) (hTime : 0 < timeMesh)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (scalarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hsep : ∀ z∈Z, ∀ w∈Z, z≠w → timeMesh ≤ |z-w|)
    (hescape : ∀ v ∈ S, ∀ L : Submodule ℝ ℝ, L ≠ ⊤ →
      beta*(Z.card : ℝ)^2*(OriginalWCoreDynamics.angles I (scalarAngle q theta)).card^2 ≤
        ((escapingMenus I height (terminalGrid q theta) (scalarAngle q theta)
          (scalarDecode q) S v L h).card : ℝ)) :
    beta*h*(Z.card : ℝ) ≤
      (4+4*(3+12*Err))*(rho^2/timeMesh+2)*(scalarCells I height position theta q rho S hSV root).card := by
  apply FiniteTransverseMenuGrowth.scalar_menu_growth_from_subspaces
    Z (OriginalWCoreDynamics.angles I (scalarAngle q theta))
    (OriginalWCoreDynamics.M I height (terminalGrid q theta) (scalarAngle q theta) S)
    (OriginalWCoreDynamics.next I height (terminalGrid q theta) (scalarAngle q theta) S)
    (coordinates I height position S hSV) (scalarDecode q) root
    (original_heights_nonempty I height Z hI hheight)
    (OriginalWCoreDynamics.angles_nonempty I (scalarAngle q theta) hI)
    (sq_pos_of_pos hrhopos) (by positivity) (by positivity) hh hhone hbeta
  · exact OriginalWCoreDynamics.M_subset_alphabet I height (terminalGrid q theta)
      (scalarAngle q theta) S Z hheight
  · intro c
    exact OriginalSeparatedHeightCap.separated_interval_cap Z hTime hsep c (rho^2) (sq_nonneg rho)
  · intro v g hg
    exact scalar_constructed_step_displacement I height position base theta Z S hSV
      hrhopos.le hq hqρ hErr hdelta hinc hheight hdiam v g hg
  · intro v L hL
    exact hescape v.val v.property L hL


/-- Native a=1 endpoint from ORIGINAL fine interval Frostman and graph data.
The core, original-menu successors, incident representatives, displacement,
and time cap are all constructed internally. -/
theorem scalar_original_w_growth
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ) (base : T → ℝ)
    (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (Phi : P → Finset ℝ) (fine : P → T → ℝ) (realizer : P → ℝ → T)
    {delta rho q Err DirErr C D U alpha mu nu F gamma R h beta timeMesh : ℝ}
    (hI : I.Nonempty) (hdeltapos : 0 < delta) (hrhopos : 0 < rho)
    (hq : 0 < q) (hqρ : q ≤ rho) (hErr : 0 ≤ Err) (hscale : delta ≤ rho^2)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta) (hTime : 0 < timeMesh)
    (hC : 0 < C) (hD : 0 ≤ D) (hU : 0 < U) (halpha : 0 ≤ alpha)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hF : 0 ≤ F) (hdeltaR : delta ≤ R) (hRone : R ≤ 1)
    (hslabBudget : mu*nu*F*R^gamma ≤ alpha/8)
    (hwidth : h+2*(DirErr*delta+q) ≤ R)
    (hbetaBudget : 8*beta*U^2*(OriginalWCoreDynamics.angles I (scalarAngle q theta)).card^2 ≤ alpha*D^2)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (scalarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hsep : ∀ z∈Z, ∀ w∈Z, z≠w → timeMesh ≤ |z-w|)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hdegree : ∀ p, ((tubesAt I p).card : ℝ) ≤ D)
    (hterminal : ∀ p c,
      (((tubesAt I p).filter (fun t => terminalGrid q theta t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a,
      (((tubesAt I p).filter (fun t => scalarAngle q theta t=a)).card : ℝ) ≤ U)
    (hmaps : ∀ p t, (p,t) ∈ I → fine p t ∈ Phi p)
    (hfiber : ∀ p u, u ∈ Phi p →
      (((tubesAt I p).filter (fun t => fine p t=u)).card : ℝ) ≤ mu)
    (hrealizer : ∀ p u, u ∈ Phi p → (p,realizer p u) ∈ I)
    (hrealizerFiber : ∀ p t, t ∈ tubesAt I p →
      (((Phi p).filter (fun u => realizer p u=t)).card : ℝ) ≤ nu)
    (hFineError : ∀ p t, (p,t) ∈ I → dist (fine p t) (scalarSlope theta t) ≤ DirErr*delta)
    (hslab : ∀ p c r, delta ≤ r → r ≤ 1 →
      (((Phi p).filter (fun u => |u-c| ≤ r)).card : ℝ) ≤ F*r^gamma*((Phi p).card : ℝ))
    (hmass : alpha*(C^5*D^2*U*(Z.card : ℝ)^2)*(vertices I height).card ≤
      (witnesses I height (terminalGrid q theta)).card) :
    ∃ S : Finset (ℝ × T), ∃ hSV : S ⊆ vertices I height,
      S.Nonempty ∧
      ((witnesses I height (terminalGrid q theta)).card : ℝ) ≤
        2*((RichWitnessCore.retained (witnesses I height (terminalGrid q theta))
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∀ root : OriginalWCoreDynamics.Core S,
        beta*h*(Z.card : ℝ) ≤ (4+4*(3+12*Err))*(rho^2/timeMesh+2)*
          (scalarCells I height position theta q rho S hSV root).card := by
  have hslabF : ∀ p, ∀ f : ℝ →L[ℝ] ℝ, ‖f‖=1 → ∀ c r : ℝ, delta ≤ r → r ≤ 1 →
      (((Phi p).filter (fun u => |f u-c| ≤ r)).card : ℝ) ≤ F*r^gamma*((Phi p).card : ℝ) := by
    intro p f hf c r hdr hr
    exact scalar_unit_functional_slab (Phi p) (hslab p) f hf c r hdr hr
  obtain ⟨S,hSV,hS,hhalf,hescape⟩ := exists_escaping_core_of_fine_frostman
    I height (terminalGrid q theta) (scalarAngle q theta) Phi fine realizer
    (scalarSlope theta) (scalarDecode q) Z hI hC hD hU halpha hmu hnu hF
    (hdeltapos.trans_le hdeltaR) hdeltaR hRone hslabBudget hwidth hheight hpoints hdegree
    hterminal hangular hmaps hfiber hrealizer hrealizerFiber hFineError
    (by intro p t _hpt; simpa only [dist_eq_norm] using scalar_grid_approximation q hq theta t)
    hslabF hmass
  refine ⟨S,hSV,hS,hhalf,?_⟩
  intro root
  apply scalar_growth_of_constructed_core I height position base theta Z S hSV root hI
    hdeltapos hrhopos hq hqρ hErr hscale hh hhone hbeta hTime hinc hheight hdiam hsep
  intro v hv L hL
  exact normalize_original_escape hU hbetaBudget (hescape v hv L hL)


end
end NativeSeparatedScalarWGrowth
