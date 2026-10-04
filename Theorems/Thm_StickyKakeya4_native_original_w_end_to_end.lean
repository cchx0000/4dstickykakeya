import Theorems.Thm_StickyKakeya4_original_w_physical_growth

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace NativeOriginalWEndToEnd
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWPhysicalDisplacement
open OriginalWPhysicalGrowth Classical
noncomputable section

theorem scalar_unit_functional_slab (Phi : Finset ℝ) {delta F gamma : ℝ}
    (hslab : ∀ c r : ℝ, delta ≤ r → r ≤ 1 →
      ((Phi.filter (fun u => |u-c| ≤ r)).card : ℝ) ≤ F*r^gamma*(Phi.card : ℝ))
    (f : ℝ →L[ℝ] ℝ) (hf : ‖f‖=1) (c r : ℝ) (hdr : delta ≤ r) (hr : r ≤ 1) :
    ((Phi.filter (fun u => |f u-c| ≤ r)).card : ℝ) ≤ F*r^gamma*(Phi.card : ℝ) := by
  let a := f 1
  have hexp : ∀ x : ℝ, f x=x*a := by
    intro x
    simpa only [smul_eq_mul,mul_one] using f.map_smul x (1 : ℝ)
  have hu : |a| ≤ 1 := by
    have hp := f.le_opNorm (1 : ℝ)
    simpa only [hf,norm_one,mul_one,Real.norm_eq_abs,a] using hp
  have hl : 1 ≤ |a| := by
    have hop : ‖f‖ ≤ |a| := f.opNorm_le_bound (abs_nonneg a) (by
      intro x
      rw [hexp,Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
      exact le_of_eq (mul_comm _ _))
    rwa [hf] at hop
  have habs : |a|=1 := le_antisymm hu hl
  have ha : a ≠ 0 := by intro hzero; rw [hzero,abs_zero] at habs; norm_num at habs
  have hid : ∀ u : ℝ, |f u-c|=|u-c/a| := by
    intro u
    have heq : f u-c=(u-c/a)*a := by rw [hexp]; field_simp
    rw [heq,abs_mul,habs,mul_one]
  have hfilter : Phi.filter (fun u => |f u-c| ≤ r)=Phi.filter (fun u => |u-c/a| ≤ r) := by
    ext u
    simp only [Finset.mem_filter,hid]
  rw [hfilter]
  exact hslab (c/a) r hdr hr

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

/-- Native a=1 endpoint from ORIGINAL fine interval Frostman and graph data.
The core, original-menu successors, incident representatives, displacement,
and time cap are all constructed internally. -/
theorem scalar_original_w_growth
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ) (base : T → ℝ)
    (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (Phi : P → Finset ℝ) (fine : P → T → ℝ) (realizer : P → ℝ → T)
    {delta rho q Err DirErr C D U alpha mu nu F gamma R h beta : ℝ}
    (hI : I.Nonempty) (hdeltapos : 0 < delta) (hrhopos : 0 < rho)
    (hq : 0 < q) (hqρ : q ≤ rho) (hErr : 0 ≤ Err) (hscale : delta ≤ rho^2)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta)
    (hC : 0 < C) (hD : 0 ≤ D) (hU : 0 < U) (halpha : 0 ≤ alpha)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hF : 0 ≤ F) (hdeltaR : delta ≤ R) (hRone : R ≤ 1)
    (hslabBudget : mu*nu*F*R^gamma ≤ alpha/8)
    (hwidth : h+2*(DirErr*delta+q) ≤ R)
    (hbetaBudget : 8*beta*U^2*(OriginalWCoreDynamics.angles I (scalarAngle q theta)).card^2 ≤ alpha*D^2)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (scalarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hmesh : ∀ z ∈ Z, ∃ k : ℤ, z=delta*(k : ℝ))
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
        beta*h*(Z.card : ℝ) ≤ (4+4*(3+12*Err))*(3*rho^2/delta)*
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
    hdeltapos hrhopos hq hqρ hErr hscale hh hhone hbeta hinc hheight hdiam hmesh
  intro v hv L hL
  exact normalize_original_escape hU hbetaBudget (hescape v hv L hL)

/-- Native a=2 endpoint. The fine input is literally Euclidean unit-normal
slab Frostman on the unchanged original Phi_p. Its conversion to the max-norm
growth coordinates is paid explicitly by the factor 2^gamma. -/
theorem planar_original_w_growth
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ × ℝ) (base : T → ℝ × ℝ)
    (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (Phi : P → Finset (ℝ × ℝ)) (fine : P → T → ℝ × ℝ) (realizer : P → (ℝ × ℝ) → T)
    {delta rho q Err DirErr C D U alpha mu nu F gamma R h beta : ℝ}
    (hI : I.Nonempty) (hdeltapos : 0 < delta) (hrhopos : 0 < rho) (hrhoone : rho ≤ 1)
    (hq : 0 < q) (hqρ : q ≤ rho) (hErr : 0 ≤ Err) (hscale : delta ≤ rho^2)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta)
    (hC : 0 < C) (hD : 0 ≤ D) (hU : 0 < U) (halpha : 0 ≤ alpha)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hF : 1 ≤ F) (hgamma : 0 ≤ gamma)
    (hdeltaR : delta ≤ R) (hRone : R ≤ 1)
    (hslabBudget : mu*nu*((2 : ℝ)^gamma*F)*R^gamma ≤ alpha/8)
    (hwidth : h+2*(DirErr*delta+q) ≤ R)
    (hbetaBudget : 8*beta*U^2*(OriginalWCoreDynamics.angles I (planarAngle q theta)).card^2 ≤ alpha*D^2)
    (hslope : ∀ t j, |theta t j| ≤ 1)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (planarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hmesh : ∀ z ∈ Z, ∃ k : ℤ, z=delta*(k : ℝ))
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
        beta^2*h^4*(Z.card : ℝ)^2 ≤ (4*4*(1+4*(3+12*Err))+2)^2*(3*rho^2/delta)^2*
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
    hdeltapos hrhopos hrhoone hq hqρ hErr hscale hh hhone hbeta hslope hinc hheight hdiam hmesh
  intro v hv L hL
  exact normalize_original_escape hU hbetaBudget (hescape v hv L hL)

end
end NativeOriginalWEndToEnd
