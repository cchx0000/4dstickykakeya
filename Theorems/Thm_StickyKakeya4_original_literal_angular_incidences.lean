import Theorems.Thm_StickyKakeya4_original_literal_angular_readback
import Theorems.Thm_StickyKakeya4_original_selected_angular_incidences
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace OriginalLiteralAngularIncidences
open Classical Finset NativeScalarCoverAD FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open OriginalLiteralCommonAlphabet OriginalAngularSourcePopulation OriginalWWitnessCounts
/-- Simultaneous original fine alphabets, obtained from the literal cover
 laws at every original point. No source separation is assumed. -/
theorem exists_literal_fine_family {P : Type*} (E : Finset P) (raw : P → Finset ℝ)
    {delta K kappa : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (hK : 1 ≤ K)
    (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hne : ∀ p ∈ E, (raw p).Nonempty)
    (H : ∀ p ∈ E, CoverADBounds (raw p) delta K kappa)
    (hbox : ∀ p ∈ E, ∀ phi ∈ raw p, |phi| ≤ 1) :
    ∃ fine : P → Finset ℝ, ∀ p ∈ E,
      (fine p).Nonempty ∧ fine p ⊆ raw p ∧ Separated (fine p) delta ∧
      (∀ phi ∈ raw p, ∃ c ∈ fine p, dist phi c < delta) ∧
      (∀ c ∈ fine p, |c| ≤ 1) ∧ ADBounds (fine p) delta (192*K^2) kappa := by
  have hex : ∀ p ∈ E, ∃ C : Finset ℝ, C.Nonempty ∧ C ⊆ raw p ∧ Separated C delta ∧
      (∀ phi ∈ raw p, ∃ c ∈ C, dist phi c < delta) ∧
      (∀ c ∈ C, |c| ≤ 1) ∧ ADBounds C delta (192*K^2) kappa :=
    fun p hp => exists_actual_fine_alphabet (raw p) (hne p hp) hd hd1 hK hk hk2 (H p hp) (hbox p hp)
  let fine : P → Finset ℝ := fun p => if hp : p ∈ E then Classical.choose (hex p hp) else ∅
  refine ⟨fine,?_⟩
  intro p hp
  simpa only [fine,dif_pos hp] using Classical.choose_spec (hex p hp)
/-- Literal Definition 17.2(4) cover alphabets and original per-angle tube
 existence produce the actual selected incidence family and all angular
 populations needed by the W construction. Every tube remains in original I.
 The exponent range is derived from the original bounded coarse cover law. -/
theorem exists_literal_angular_population_supplier {P T : Type*} [DecidableEq P] [DecidableEq T]
    (E : Finset P) (raw : P → Finset ℝ) (I : Finset (P × T)) (u : T → ℝ) (rawPhi : Finset ℝ)
    {delta q K kappa C0 : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1) (hK : 1 ≤ K)
    (hk : 0 ≤ kappa) (hsmall : K*q ≤ 1/8) (hC0 : 0 ≤ C0) (hE : E.Nonempty)
    (hne : ∀ p ∈ E, (raw p).Nonempty)
    (hfAD : ∀ p ∈ E, CoverADBounds (raw p) delta K kappa)
    (hfbox : ∀ p ∈ E, ∀ phi ∈ raw p, |phi| ≤ 1)
    (hsource : ∀ p ∈ E, ∀ phi ∈ raw p, ∃ t, (p,t) ∈ I ∧ |u t-phi| ≤ C0*delta)
    (hcAD : CoverADBounds rawPhi q K kappa) (hcbox : ∀ phi ∈ rawPhi, |phi| ≤ 1)
    (hcover : ∀ p ∈ E, ∀ phi ∈ raw p, ∃ a ∈ rawPhi, dist phi a ≤ q) :
    ∃ fine : P → Finset ℝ, ∃ Phi : Finset ℝ,
      (∀ p ∈ E, (fine p).Nonempty ∧ fine p ⊆ raw p ∧ Separated (fine p) delta ∧
        (∀ phi ∈ raw p, ∃ c ∈ fine p, dist phi c < delta) ∧
        (∀ c ∈ fine p, |c| ≤ 1) ∧ ADBounds (fine p) delta (192*K^2) kappa) ∧
      Phi ⊆ E.biUnion raw ∧ Separated Phi q ∧ (∀ phi ∈ Phi, |phi| ≤ 1) ∧
      ADBounds Phi q (192*K^2) kappa ∧
      ∃ source : P → ℝ → T,
        OriginalSelectedAngularIncidences.incidences E fine source ⊆ I ∧
        (OriginalSelectedAngularIncidences.incidences E fine source).Nonempty ∧
        TwoTubePathCollisionCount.points (OriginalSelectedAngularIncidences.incidences E fine source)=E ∧
        (∀ p ∈ E, ∀ phi ∈ fine p, (p,source p phi) ∈ I ∧ |u (source p phi)-phi| ≤ C0*delta) ∧
        (∀ p ∈ E, degree delta (192*K^2) kappa C0 ≤
          ((tubesAt (OriginalSelectedAngularIncidences.incidences E fine source) p).card:ℝ)) ∧
        (∀ p a, (((tubesAt (OriginalSelectedAngularIncidences.incidences E fine source) p).filter
          (fun t => |u t-a| ≤ q)).card:ℝ) ≤ ballCap delta q (192*K^2) kappa C0) ∧
        (∀ p a, (((tubesAt (OriginalSelectedAngularIncidences.incidences E fine source) p).filter
          (fun t => |u t-a| ≤ C0*delta+q)).card:ℝ) ≤ ballCap delta q (192*K^2) kappa (2*C0)) ∧
        (∀ t ∈ TwoTubePathCollisionCount.tubes (OriginalSelectedAngularIncidences.incidences E fine source),
          ∃ a ∈ Phi, |u t-a| ≤ C0*delta+q) ∧
        Phi.Nonempty ∧ (Phi.card:ℝ) ≤ 4*(192*K^2)*(1/q)^kappa ∧
        ballCap delta q (192*K^2) kappa C0*(Phi.card:ℝ)/degree delta (192*K^2) kappa C0 ≤
          128*(192*K^2)^2*(192*K^2)*(1+C0)^3 ∧
        ballCap delta q (192*K^2) kappa (2*C0)*(Phi.card:ℝ)/degree delta (192*K^2) kappa C0 ≤
          512*(192*K^2)^2*(192*K^2)*(1+C0)^3 := by
  have hq : 0 < q := hd.trans_le hdq
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hrawPhi : rawPhi.Nonempty := by
    obtain ⟨p,hp⟩ := hE
    obtain ⟨phi,hphi⟩ := hne p hp
    obtain ⟨a,ha,_⟩ := hcover p hp phi hphi
    exact ⟨a,ha⟩
  have hk2 := (OriginalLiteralAngularReadback.cover_exponent_lt_two rawPhi hrawPhi hq hq1 hK hsmall hcAD hcbox).le
  obtain ⟨fine,hfine⟩ := exists_literal_fine_family E raw hd (hdq.trans hq1) hK hk hk2 hne hfAD hfbox
  obtain ⟨Phi,_hPhi,hPhisub,hPhisep,hPhicover,hPhibox,hPhiAD⟩ := exists_actual_common_alphabet
    E hE raw rawPhi hd hdq hq1 hK hk hk2 hne hfAD hfbox hcAD hcbox hcover
  refine ⟨fine,Phi,hfine,hPhisub,hPhisep,hPhibox,hPhiAD,?_⟩
  apply OriginalSelectedAngularIncidences.exists_original_angular_population_supplier E fine I u Phi
    hd hdq hq1 (by positivity : 0 < 192*K^2) (by positivity : 0 ≤ 192*K^2) hk hk2 hC0 hE
    (fun p hp => (hfine p hp).1)
    (fun p hp => (hfine p hp).2.2.2.2.2)
    (fun p hp => (hfine p hp).2.2.1)
    (fun p hp => (hfine p hp).2.2.2.2.1)
    (fun p hp phi hphi => hsource p hp phi ((hfine p hp).2.1 hphi)) hPhiAD hPhibox
  intro p hp phi hphi
  obtain ⟨a,ha,hpa⟩ := hPhicover p hp phi ((hfine p hp).2.1 hphi)
  exact ⟨a,ha,by simpa only [Real.dist_eq] using hpa.le⟩
end OriginalLiteralAngularIncidences
