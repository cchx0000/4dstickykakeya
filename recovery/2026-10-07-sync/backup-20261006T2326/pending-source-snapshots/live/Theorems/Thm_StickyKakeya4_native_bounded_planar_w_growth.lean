import Theorems.Thm_StickyKakeya4_native_original_w_end_to_end
import Theorems.Thm_StickyKakeya4_original_separated_height_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

namespace NativeBoundedPlanarWGrowth
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWPhysicalDisplacement
open OriginalWPhysicalGrowth Classical
noncomputable section

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

/-- A fixed chart bound is retained explicitly. Orthonormal coordinate
changes do not preserve the original coordinate cube. -/
omit [DecidableEq P] in
theorem decoded_alphabet_bound (I : Finset (P × T)) (theta : T → Fin 3 → ℝ)
    {q DirBound : ℝ} (hq : 0 < q) (hqone : q ≤ 1)
    (hslope : ∀ t j, |theta t j| ≤ DirBound) :
    ∀ a ∈ OriginalWCoreDynamics.angles I (planarAngle q theta),
      ‖planarDecode q a‖ ≤ DirBound+1 := by
  intro a ha
  obtain ⟨t,_ht,rfl⟩ := Finset.mem_image.mp ha
  have hu : ‖planarSlope theta t‖ ≤ DirBound := max_le (hslope t 0) (hslope t 1)
  have hg : ‖planarDecode q (planarAngle q theta t)-planarSlope theta t‖ ≤ q := by
    rw [norm_sub_rev]
    exact planar_grid_approximation q hq theta t
  have ht := norm_add_le (planarDecode q (planarAngle q theta t)-planarSlope theta t)
    (planarSlope theta t)
  rw [sub_add_cancel] at ht
  linarith

/-- Native a=2 growth with actual graph displacements, actual original-height
cap, and an angular bound derived from the original bounded tube slopes. -/
theorem planar_growth_of_constructed_core
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ × ℝ)
    (base : T → ℝ × ℝ) (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height) (root : OriginalWCoreDynamics.Core S)
    {delta rho q Err h beta DirBound timeMesh : ℝ} (hI : I.Nonempty)
    (_hdeltapos : 0 < delta) (hrhopos : 0 < rho) (hrhoone : rho ≤ 1)
    (hq : 0 < q) (hqρ : q ≤ rho) (hErr : 0 ≤ Err) (hdelta : delta ≤ rho^2)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta) (hDirBound : 0 ≤ DirBound) (hTime : 0 < timeMesh)
    (hslope : ∀ t j, |theta t j| ≤ DirBound)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (planarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hsep : ∀ z∈Z, ∀ w∈Z, z≠w → timeMesh ≤ |z-w|)
    (hescape : ∀ v ∈ S, ∀ L : Submodule ℝ (ℝ × ℝ), L ≠ ⊤ →
      beta*(Z.card : ℝ)^2*(OriginalWCoreDynamics.angles I (planarAngle q theta)).card^2 ≤
        ((escapingMenus I height (terminalGrid q theta) (planarAngle q theta)
          (planarDecode q) S v L h).card : ℝ)) :
    beta^2*h^4*(Z.card : ℝ)^2 ≤
      (4*(2*(DirBound+1))*(1+4*(3+12*Err))+2)^2*(rho^2/timeMesh+2)^2*
        (planarCells I height position theta q rho S hSV root).card := by
  apply FiniteTransverseMenuGrowth.planar_menu_growth
    Z (OriginalWCoreDynamics.angles I (planarAngle q theta))
    (OriginalWCoreDynamics.M I height (terminalGrid q theta) (planarAngle q theta) S)
    (OriginalWCoreDynamics.next I height (terminalGrid q theta) (planarAngle q theta) S)
    (coordinates I height position S hSV) (planarDecode q) root
    (original_heights_nonempty I height Z hI hheight)
    (OriginalWCoreDynamics.angles_nonempty I (planarAngle q theta) hI)
    (sq_pos_of_pos hrhopos) (by positivity) (by positivity) hh hhone hbeta (show 0 < 2*(DirBound+1) by positivity)
  · intro a ha b hb
    have hbound := decoded_alphabet_bound I theta hq (hqρ.trans hrhoone) hslope
    have hn : ‖planarDecode q b-planarDecode q a‖ ≤ 2*(DirBound+1) := by
      have ht := norm_sub_le (planarDecode q b) (planarDecode q a)
      have ha₂ := hbound a ha
      have hb₂ := hbound b hb
      linarith
    change max |(planarDecode q b).1-(planarDecode q a).1|
      |(planarDecode q b).2-(planarDecode q a).2| ≤ 2*(DirBound+1) at hn
    exact ⟨(le_max_left _ _).trans hn,(le_max_right _ _).trans hn⟩
  · exact OriginalWCoreDynamics.M_subset_alphabet I height (terminalGrid q theta)
      (planarAngle q theta) S Z hheight
  · intro c
    exact OriginalSeparatedHeightCap.separated_interval_cap Z hTime hsep c (rho^2) (sq_nonneg rho)
  · intro v g hg
    have hd := planar_constructed_step_displacement I height position base theta Z S hSV
      hrhopos.le hq hqρ hErr hdelta hinc hheight hdiam v g hg
    simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
      Real.norm_eq_abs,smul_eq_mul,FiniteTransverseMenuGrowth.angularDifference] using hd
  · intro v L hL
    exact hescape v.val v.property L hL


/-- Native a=2 endpoint. The fine input is literally Euclidean unit-normal
slab Frostman on the unchanged original Phi_p. Its conversion to the max-norm
growth coordinates is paid explicitly by the factor 2^gamma. -/
theorem planar_original_w_growth
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ × ℝ) (base : T → ℝ × ℝ)
    (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (Phi : P → Finset (ℝ × ℝ)) (fine : P → T → ℝ × ℝ) (realizer : P → (ℝ × ℝ) → T)
    {delta rho q Err DirErr C D U alpha mu nu F gamma R h beta DirBound timeMesh : ℝ}
    (hI : I.Nonempty) (hdeltapos : 0 < delta) (hrhopos : 0 < rho) (hrhoone : rho ≤ 1)
    (hq : 0 < q) (hqρ : q ≤ rho) (hErr : 0 ≤ Err) (hscale : delta ≤ rho^2)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta) (hDirBound : 0 ≤ DirBound) (hTime : 0 < timeMesh)
    (hC : 0 < C) (hD : 0 ≤ D) (hU : 0 < U) (halpha : 0 ≤ alpha)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hF : 1 ≤ F) (hgamma : 0 ≤ gamma)
    (hdeltaR : delta ≤ R) (hRone : R ≤ 1)
    (hslabBudget : mu*nu*((2 : ℝ)^gamma*F)*R^gamma ≤ alpha/8)
    (hwidth : h+2*(DirErr*delta+q) ≤ R)
    (hbetaBudget : 8*beta*U^2*(OriginalWCoreDynamics.angles I (planarAngle q theta)).card^2 ≤ alpha*D^2)
    (hslope : ∀ t j, |theta t j| ≤ DirBound)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (planarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hsep : ∀ z∈Z, ∀ w∈Z, z≠w → timeMesh ≤ |z-w|)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hdegree : ∀ p, ((tubesAt I p).card : ℝ) ≤ D)
    (hterminal : ∀ p c,
      (((tubesAt I p).filter (fun t => terminalGrid q theta t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a,
      (((tubesAt I p).filter (fun t => planarAngle q theta t=a)).card : ℝ) ≤ U)
    (hmaps : ∀ p t, (p,t) ∈ I → fine p t ∈ Phi p)
    (hfiber : ∀ p u, u ∈ Phi p →
      (((tubesAt I p).filter (fun t => fine p t=u)).card : ℝ) ≤ mu)
    (hrealizer : ∀ p u, u ∈ Phi p → (p,realizer p u) ∈ I)
    (hrealizerFiber : ∀ p t, t ∈ tubesAt I p →
      (((Phi p).filter (fun u => realizer p u=t)).card : ℝ) ≤ nu)
    (hFineError : ∀ p t, (p,t) ∈ I → dist (fine p t) (planarSlope theta t) ≤ DirErr*delta)
    (hslab : ∀ p n₁ n₂ c r, n₁^2+n₂^2=1 → delta ≤ r → r ≤ 1 →
      (((Phi p).filter (fun u => |n₁*u.1+n₂*u.2-c| ≤ r)).card : ℝ) ≤ F*r^gamma*((Phi p).card : ℝ))
    (hmass : alpha*(C^5*D^2*U*(Z.card : ℝ)^2)*(vertices I height).card ≤
      (witnesses I height (terminalGrid q theta)).card) :
    ∃ S : Finset (ℝ × T), ∃ hSV : S ⊆ vertices I height,
      S.Nonempty ∧
      ((witnesses I height (terminalGrid q theta)).card : ℝ) ≤
        2*((RichWitnessCore.retained (witnesses I height (terminalGrid q theta))
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∀ root : OriginalWCoreDynamics.Core S,
        beta^2*h^4*(Z.card : ℝ)^2 ≤ (4*(2*(DirBound+1))*(1+4*(3+12*Err))+2)^2*(rho^2/timeMesh+2)^2*
          (planarCells I height position theta q rho S hSV root).card := by
  have hFzero : 0 ≤ F := by linarith
  have hslabF : ∀ p, ∀ f : (ℝ × ℝ) →L[ℝ] ℝ, ‖f‖=1 → ∀ c r : ℝ, delta ≤ r → r ≤ 1 →
      (((Phi p).filter (fun u => |f u-c| ≤ r)).card : ℝ) ≤
        ((2 : ℝ)^gamma*F)*r^gamma*((Phi p).card : ℝ) := by
    intro p f hf c r hdr hr
    exact NativePlanarSlabNormConversion.slab_law_conversion (Phi p) delta F gamma
      hdeltapos hF hgamma (hslab p) f c r hf hdr hr
  obtain ⟨S,hSV,hS,hhalf,hescape⟩ := exists_escaping_core_of_fine_frostman
    I height (terminalGrid q theta) (planarAngle q theta) Phi fine realizer
    (planarSlope theta) (planarDecode q) Z hI hC hD hU halpha hmu hnu (by positivity)
    (hdeltapos.trans_le hdeltaR) hdeltaR hRone hslabBudget hwidth hheight hpoints hdegree
    hterminal hangular hmaps (by
      intro p u hu
      convert hfiber p u hu using 1
      apply congrArg (fun s : Finset T => (s.card : ℝ))
      exact Finset.filter_congr_decidable _ _ _) hrealizer hrealizerFiber hFineError
    (by intro p t _hpt; simpa only [dist_eq_norm] using planar_grid_approximation q hq theta t)
    hslabF hmass
  refine ⟨S,hSV,hS,hhalf,?_⟩
  intro root
  apply planar_growth_of_constructed_core I height position base theta Z S hSV root hI
    hdeltapos hrhopos hrhoone hq hqρ hErr hscale hh hhone hbeta hDirBound hTime hslope hinc hheight hdiam hsep
  intro v hv L hL
  exact normalize_original_escape hU hbetaBudget (hescape v hv L hL)


end
end NativeBoundedPlanarWGrowth
