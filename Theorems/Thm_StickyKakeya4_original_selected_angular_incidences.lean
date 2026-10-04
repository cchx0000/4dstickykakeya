import Theorems.Thm_StickyKakeya4_original_angular_source_population
import Theorems.Thm_StickyKakeya4_original_reference_angle_selection
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalSelectedAngularIncidences
open Classical FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open OriginalAngularSourcePopulation OriginalWWitnessCounts
variable {P T : Type*} [DecidableEq P] [DecidableEq T]

/-- The actual incidence family selected from the fine angular alphabets. -/
def incidences (E : Finset P) (fine : P → Finset ℝ) (source : P → ℝ → T) : Finset (P × T) :=
  E.biUnion (fun p => (selectedTubes (fine p) (source p)).image (fun t => (p,t)))

@[simp] lemma mem_incidences (E : Finset P) (fine : P → Finset ℝ) (source : P → ℝ → T)
    (p : P) (t : T) : (p,t) ∈ incidences E fine source ↔
      p ∈ E ∧ t ∈ selectedTubes (fine p) (source p) := by
  simp only [incidences,Finset.mem_biUnion,Finset.mem_image,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,hap,hbt⟩
    subst a
    subst b
    exact ⟨ha,hb⟩
  · rintro ⟨hp,ht⟩
    exact ⟨p,hp,t,ht,rfl,rfl⟩

theorem tubesAt_eq_selected (E : Finset P) (fine : P → Finset ℝ) (source : P → ℝ → T)
    (p : P) (hp : p ∈ E) :
    tubesAt (incidences E fine source) p = selectedTubes (fine p) (source p) := by
  ext t
  simp only [mem_tubesAt,mem_incidences,hp,true_and]

theorem tubesAt_eq_empty (E : Finset P) (fine : P → Finset ℝ) (source : P → ℝ → T)
    (p : P) (hp : p ∉ E) : tubesAt (incidences E fine source) p = ∅ := by
  ext t
  simp only [mem_tubesAt,mem_incidences,hp,false_and,Finset.notMem_empty]

theorem incidences_subset_source (E : Finset P) (fine : P → Finset ℝ) (source : P → ℝ → T)
    (I : Finset (P × T)) (hsource : ∀ p ∈ E, ∀ phi ∈ fine p, (p,source p phi) ∈ I) :
    incidences E fine source ⊆ I := by
  rintro ⟨p,t⟩ hpt
  obtain ⟨hp,ht⟩ := (mem_incidences E fine source p t).mp hpt
  obtain ⟨phi,hphi,rfl⟩ := Finset.mem_image.mp ht
  exact hsource p hp phi hphi

theorem incidences_nonempty (E : Finset P) (fine : P → Finset ℝ) (source : P → ℝ → T)
    (hE : E.Nonempty) (hf : ∀ p ∈ E, (fine p).Nonempty) : (incidences E fine source).Nonempty := by
  obtain ⟨p,hp⟩ := hE
  obtain ⟨phi,hphi⟩ := hf p hp
  exact ⟨(p,source p phi),(mem_incidences E fine source _ _).mpr
    ⟨hp,Finset.mem_image_of_mem _ hphi⟩⟩

theorem points_eq (E : Finset P) (fine : P → Finset ℝ) (source : P → ℝ → T)
    (hf : ∀ p ∈ E, (fine p).Nonempty) : TwoTubePathCollisionCount.points (incidences E fine source)=E := by
  ext p
  constructor
  · intro hp
    obtain ⟨pt,hpt,hp⟩ := Finset.mem_image.mp hp
    have hh := (mem_incidences E fine source pt.1 pt.2).mp hpt
    exact hp ▸ hh.1
  · intro hp
    obtain ⟨phi,hphi⟩ := hf p hp
    exact Finset.mem_image.mpr ⟨(p,source p phi),
      (mem_incidences E fine source _ _).mpr ⟨hp,Finset.mem_image_of_mem _ hphi⟩,rfl⟩

/-- Every member of the constructed incidence family has its original fine
label and the original O(delta) realization estimate. -/
theorem incidence_realization (E : Finset P) (fine : P → Finset ℝ) (source : P → ℝ → T)
    (u : T → ℝ) {delta C : ℝ}
    (hrealize : ∀ p ∈ E, ∀ phi ∈ fine p, |u (source p phi)-phi| ≤ C*delta) :
    ∀ p t, (p,t) ∈ incidences E fine source → ∃ phi ∈ fine p, |u t-phi| ≤ C*delta := by
  intro p t hpt
  obtain ⟨hp,ht⟩ := (mem_incidences E fine source _ _).mp hpt
  obtain ⟨phi,hphi,rfl⟩ := Finset.mem_image.mp ht
  exact ⟨phi,hphi,hrealize p hp phi hphi⟩

/-- Pointwise original populations of the constructed incidence family. The
degree and ball cap are conclusions of fine AD, separation and realization. -/
theorem selected_populations (E : Finset P) (fine : P → Finset ℝ)
    (source : P → ℝ → T) (u : T → ℝ) {delta q K kappa C : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hK : 0 < K) (hk : 0 ≤ kappa) (hC : 0 ≤ C)
    (hne : ∀ p ∈ E, (fine p).Nonempty)
    (hAD : ∀ p ∈ E, ADBounds (fine p) delta K kappa)
    (hsep : ∀ p ∈ E, Separated (fine p) delta)
    (hbox : ∀ p ∈ E, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hrealize : ∀ p ∈ E, ∀ phi ∈ fine p, |u (source p phi)-phi| ≤ C*delta) :
    (∀ p ∈ E, degree delta K kappa C ≤ ((tubesAt (incidences E fine source) p).card : ℝ)) ∧
    (∀ p a, (((tubesAt (incidences E fine source) p).filter (fun t => |u t-a| ≤ q)).card : ℝ) ≤
      ballCap delta q K kappa C) := by
  constructor
  · intro p hp
    rw [tubesAt_eq_selected E fine source p hp]
    exact selected_degree_lower (fine p) (source p) u hd (hdq.trans hq1) hK hC
      (hne p hp) (hAD p hp) (hsep p hp) (hrealize p hp)
  · intro p a
    by_cases hp : p ∈ E
    · rw [tubesAt_eq_selected E fine source p hp]
      exact selected_ball_cap (fine p) (source p) u hd hdq hq1 hK.le hk hC
        (hAD p hp) (hbox p hp) (hrealize p hp) a
    · rw [tubesAt_eq_empty E fine source p hp,Finset.filter_empty,Finset.card_empty,Nat.cast_zero]
      exact (ballCap_pos hd (hd.trans_le hdq) hK hC).le

/-- The reference-angle radius is q+C delta, with no uncharged assumption
that the original realization error is smaller than q. -/
theorem reference_ball_cap (E : Finset P) (fine : P → Finset ℝ)
    (source : P → ℝ → T) (u : T → ℝ) {delta q K kappa C : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hK : 0 < K) (hk : 0 ≤ kappa) (hC : 0 ≤ C)
    (hAD : ∀ p ∈ E, ADBounds (fine p) delta K kappa)
    (hbox : ∀ p ∈ E, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hrealize : ∀ p ∈ E, ∀ phi ∈ fine p, |u (source p phi)-phi| ≤ C*delta) :
    ∀ p a, (((tubesAt (incidences E fine source) p).filter
        (fun t => |u t-a| ≤ C*delta+q)).card : ℝ) ≤ ballCap delta q K kappa (2*C) := by
  intro p a
  by_cases hp : p ∈ E
  · rw [tubesAt_eq_selected E fine source p hp]
    simpa only [add_comm] using selected_reference_ball_cap (fine p) (source p) u
      hd hdq hq1 hK.le hk hC (hAD p hp) (hbox p hp) (hrealize p hp) a
  · rw [tubesAt_eq_empty E fine source p hp,Finset.filter_empty,Finset.card_empty,Nat.cast_zero]
    exact (ballCap_pos hd (hd.trans_le hdq) hK (by positivity : 0 ≤ 2*C)).le

/-- The original fine-to-coarse covering law produces reference angles for
the actual selected tubes, with its exact realization-plus-cover error. -/
theorem common_angle_near (E : Finset P) (fine : P → Finset ℝ)
    (source : P → ℝ → T) (u : T → ℝ) (Phi : Finset ℝ) {delta q C : ℝ}
    (hrealize : ∀ p ∈ E, ∀ phi ∈ fine p, |u (source p phi)-phi| ≤ C*delta)
    (hcover : ∀ p ∈ E, ∀ phi ∈ fine p, ∃ a ∈ Phi, |phi-a| ≤ q) :
    ∀ t ∈ TwoTubePathCollisionCount.tubes (incidences E fine source),
      ∃ a ∈ Phi, |u t-a| ≤ C*delta+q := by
  apply OriginalReferenceAngleSelection.source_common_angle_near (incidences E fine source) u fine Phi
    (C*delta) q (incidence_realization E fine source u hrealize)
  intro p hp phi hphi
  obtain ⟨pt,hpt,hp⟩ := Finset.mem_image.mp hp
  have hh := (mem_incidences E fine source pt.1 pt.2).mp hpt
  exact hcover p (hp ▸ hh.1) phi hphi

section Selection
variable [Nonempty T]

/-- Choice is made from the literal source incidence relation in Definition
17.2(4), once for every fine angular label; collisions are allowed. -/
def chooseSource (E : Finset P) (fine : P → Finset ℝ) (I : Finset (P × T))
    (u : T → ℝ) (delta C : ℝ)
    (hsource : ∀ p ∈ E, ∀ phi ∈ fine p, ∃ t, (p,t) ∈ I ∧ |u t-phi| ≤ C*delta)
    (p : P) (phi : ℝ) : T :=
  if hp : p ∈ E then
    if hphi : phi ∈ fine p then Classical.choose (hsource p hp phi hphi)
    else Classical.choice inferInstance
  else Classical.choice inferInstance

omit [DecidableEq T] in
lemma chooseSource_spec (E : Finset P) (fine : P → Finset ℝ) (I : Finset (P × T))
    (u : T → ℝ) (delta C : ℝ)
    (hsource : ∀ p ∈ E, ∀ phi ∈ fine p, ∃ t, (p,t) ∈ I ∧ |u t-phi| ≤ C*delta)
    (p : P) (hp : p ∈ E) (phi : ℝ) (hphi : phi ∈ fine p) :
    (p,chooseSource E fine I u delta C hsource p phi) ∈ I ∧
      |u (chooseSource E fine I u delta C hsource p phi)-phi| ≤ C*delta := by
  simpa only [chooseSource,dif_pos hp,dif_pos hphi] using Classical.choose_spec (hsource p hp phi hphi)

omit [Nonempty T] in
/-- This existential supplier starts with the source's per-angle tube
existence, and returns the actual selected source incidence family and its
derived fine populations. It takes no final degree or cap certificate. -/
theorem exists_selected_source_populations (E : Finset P) (fine : P → Finset ℝ)
    (I : Finset (P × T)) (u : T → ℝ) {delta q K kappa C : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hK : 0 < K) (hk : 0 ≤ kappa) (hC : 0 ≤ C) (hE : E.Nonempty)
    (hne : ∀ p ∈ E, (fine p).Nonempty)
    (hAD : ∀ p ∈ E, ADBounds (fine p) delta K kappa)
    (hsep : ∀ p ∈ E, Separated (fine p) delta)
    (hbox : ∀ p ∈ E, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hsource : ∀ p ∈ E, ∀ phi ∈ fine p, ∃ t, (p,t) ∈ I ∧ |u t-phi| ≤ C*delta) :
    ∃ source : P → ℝ → T,
      incidences E fine source ⊆ I ∧ (incidences E fine source).Nonempty ∧
      TwoTubePathCollisionCount.points (incidences E fine source)=E ∧
      (∀ p ∈ E, ∀ phi ∈ fine p, (p,source p phi) ∈ I ∧ |u (source p phi)-phi| ≤ C*delta) ∧
      (∀ p ∈ E, degree delta K kappa C ≤ ((tubesAt (incidences E fine source) p).card : ℝ)) ∧
      (∀ p a, (((tubesAt (incidences E fine source) p).filter (fun t => |u t-a| ≤ q)).card : ℝ) ≤
        ballCap delta q K kappa C) := by
  have hT : Nonempty T := by
    obtain ⟨p,hp⟩ := hE
    obtain ⟨phi,hphi⟩ := hne p hp
    obtain ⟨t,_⟩ := hsource p hp phi hphi
    exact ⟨t⟩
  let : Nonempty T := hT
  let source := chooseSource E fine I u delta C hsource
  have hs := chooseSource_spec E fine I u delta C hsource
  have hmem : ∀ p ∈ E, ∀ phi ∈ fine p, (p,source p phi) ∈ I :=
    fun p hp phi hphi => (hs p hp phi hphi).1
  have herr : ∀ p ∈ E, ∀ phi ∈ fine p, |u (source p phi)-phi| ≤ C*delta :=
    fun p hp phi hphi => (hs p hp phi hphi).2
  exact ⟨source,incidences_subset_source E fine source I hmem,incidences_nonempty E fine source hE hne,
    points_eq E fine source hne,hs,selected_populations E fine source u hd hdq hq1 hK hk hC hne hAD hsep hbox herr⟩

omit [Nonempty T] in
/-- Full original angular supplier: source tube existence, fine separated AD
alphabets and the literal common q-AD alphabet produce the actual selected
incidences, both angular caps, and the scale-free population ratio. -/
theorem exists_original_angular_population_supplier (E : Finset P) (fine : P → Finset ℝ)
    (I : Finset (P × T)) (u : T → ℝ) (Phi : Finset ℝ)
    {delta q Kfine Kcoarse kappa C : ℝ}
    (hd : 0 < delta) (hdq : delta ≤ q) (hq1 : q ≤ 1)
    (hf : 0 < Kfine) (hc : 0 ≤ Kcoarse) (hk : 0 ≤ kappa) (hk2 : kappa ≤ 2)
    (hC : 0 ≤ C) (hE : E.Nonempty) (hne : ∀ p ∈ E, (fine p).Nonempty)
    (hfAD : ∀ p ∈ E, ADBounds (fine p) delta Kfine kappa)
    (hsep : ∀ p ∈ E, Separated (fine p) delta)
    (hfbox : ∀ p ∈ E, ∀ phi ∈ fine p, |phi| ≤ 1)
    (hsource : ∀ p ∈ E, ∀ phi ∈ fine p, ∃ t, (p,t) ∈ I ∧ |u t-phi| ≤ C*delta)
    (hcAD : ADBounds Phi q Kcoarse kappa) (hcbox : ∀ phi ∈ Phi, |phi| ≤ 1)
    (hcover : ∀ p ∈ E, ∀ phi ∈ fine p, ∃ a ∈ Phi, |phi-a| ≤ q) :
    ∃ source : P → ℝ → T,
      incidences E fine source ⊆ I ∧ (incidences E fine source).Nonempty ∧
      TwoTubePathCollisionCount.points (incidences E fine source)=E ∧
      (∀ p ∈ E, ∀ phi ∈ fine p, (p,source p phi) ∈ I ∧ |u (source p phi)-phi| ≤ C*delta) ∧
      (∀ p ∈ E, degree delta Kfine kappa C ≤ ((tubesAt (incidences E fine source) p).card : ℝ)) ∧
      (∀ p a, (((tubesAt (incidences E fine source) p).filter (fun t => |u t-a| ≤ q)).card : ℝ) ≤
        ballCap delta q Kfine kappa C) ∧
      (∀ p a, (((tubesAt (incidences E fine source) p).filter (fun t => |u t-a| ≤ C*delta+q)).card : ℝ) ≤
        ballCap delta q Kfine kappa (2*C)) ∧
      (∀ t ∈ TwoTubePathCollisionCount.tubes (incidences E fine source),
        ∃ a ∈ Phi, |u t-a| ≤ C*delta+q) ∧
      Phi.Nonempty ∧ (Phi.card : ℝ) ≤ 4*Kcoarse*(1/q)^kappa ∧
      ballCap delta q Kfine kappa C*(Phi.card : ℝ)/degree delta Kfine kappa C ≤
        128*Kfine^2*Kcoarse*(1+C)^3 ∧
      ballCap delta q Kfine kappa (2*C)*(Phi.card : ℝ)/degree delta Kfine kappa C ≤
        512*Kfine^2*Kcoarse*(1+C)^3 := by
  obtain ⟨source,hsub,hnon,hpts,hs,hdeg,hball⟩ := exists_selected_source_populations
    E fine I u hd hdq hq1 hf hk hC hE hne hfAD hsep hfbox hsource
  have herr : ∀ p ∈ E, ∀ phi ∈ fine p, |u (source p phi)-phi| ≤ C*delta :=
    fun p hp phi hphi => (hs p hp phi hphi).2
  have hPhi : Phi.Nonempty := by
    obtain ⟨p,hp⟩ := hE
    obtain ⟨phi,hphi⟩ := hne p hp
    obtain ⟨a,ha,_⟩ := hcover p hp phi hphi
    exact ⟨a,ha⟩
  exact ⟨source,hsub,hnon,hpts,hs,hdeg,hball,
    reference_ball_cap E fine source u hd hdq hq1 hf hk hC hfAD hfbox herr,
    common_angle_near E fine source u Phi herr hcover,hPhi,
    boxed_AD_card Phi (hd.trans_le hdq) hq1 hc hcAD hcbox,
    original_population_ratio Phi hd hdq hq1 hf hc hC hk2 hcAD hcbox,
    original_reference_population_ratio Phi hd hdq hq1 hf hc hC hk hk2 hcAD hcbox⟩

end Selection
end OriginalSelectedAngularIncidences
