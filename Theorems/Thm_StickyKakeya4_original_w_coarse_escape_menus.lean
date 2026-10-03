import Theorems.Thm_StickyKakeya4_original_w_witness_counts
import Theorems.Thm_StickyKakeya4_fine_point_slab_geometry
import Theorems.Thm_StickyKakeya4_rich_witness_real_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace OriginalWCoarseEscapeMenus
open OriginalWWitnessCounts
open Classical
noncomputable section

variable {P T H A K E : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
  [DecidableEq A] [DecidableEq K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def coreOutgoing (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (S : Finset (H × T)) (v : H × T) : Finset (Path P T × Path P T) :=
  RichWitnessCore.outgoing
    (RichWitnessCore.retained (witnesses I height cell)
      (fun w => endpoint height w.1) (fun w => endpoint height w.2) S)
    (fun w => endpoint height w.1) v

lemma mem_coreOutgoing (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (S : Finset (H × T)) (v : H × T) (w : Path P T × Path P T) :
    w ∈ coreOutgoing I height cell S v ↔
      w ∈ witnesses I height cell ∧ endpoint height w.1 ∈ S ∧
      endpoint height w.2 ∈ S ∧ endpoint height w.1=v := by
  simp only [coreOutgoing,RichWitnessCore.outgoing,RichWitnessCore.retained,
    Finset.mem_filter,and_assoc]

def coarseMenus (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (angle : T → A) (S : Finset (H × T)) (v : H × T) : Finset ((H × H) × (A × A)) :=
  (coreOutgoing I height cell S v).image (menu height angle)

def menuDifference (phi : A → E) (g : (H × H) × (A × A)) : E := phi g.2.2-phi g.2.1

def escapingMenus (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (angle : T → A) (phi : A → E) (S : Finset (H × T)) (v : H × T)
    (L : Submodule ℝ E) (h : ℝ) : Finset ((H × H) × (A × A)) :=
  (coarseMenus I height cell angle S v).filter
    (fun g => h ≤ Metric.infDist (menuDifference phi g) (L : Set E))

def badCoreWitnesses (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (angle : T → A) (phi : A → E) (S : Finset (H × T)) (v : H × T)
    (L : Submodule ℝ E) (h : ℝ) : Finset (Path P T × Path P T) :=
  (coreOutgoing I height cell S v).filter
    (fun w => Metric.infDist (menuDifference phi (menu height angle w)) (L : Set E) < h)

/-- Every coarse menu retains an ORIGINAL pair of incidence paths, whose
actual partner remains in the same core. A fixed representative may therefore
be chosen independently of the subspace used by later growth. -/
theorem coarse_menu_has_original_partner (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (S : Finset (H × T)) (v : H × T)
    {g : (H × H) × (A × A)} (hg : g ∈ coarseMenus I height cell angle S v) :
    ∃ w ∈ witnesses I height cell,
      endpoint height w.1=v ∧ endpoint height w.2 ∈ S ∧ menu height angle w=g := by
  obtain ⟨w,hw,hg⟩ := Finset.mem_image.mp hg
  have hm := (mem_coreOutgoing I height cell S v w).mp hw
  exact ⟨w,hm.1,hm.2.2.2,hm.2.2.1,hg⟩

omit [DecidableEq A] in
/-- Bad coarse witnesses are charged to one fine affine slab at their SAME
original starting point. The pointwise slab upper bound is on the FULL
reference incidences; the retained core is used only for the subset inclusion. -/
theorem badCoreWitnesses_card_le (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (phi : A → E) (fine : P → T → E)
    (Z : Finset H) (S : Finset (H × T)) (v : H × T)
    (L : Submodule ℝ E) (hL : L ≠ ⊤)
    {C D U Q e h R : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hwidth : h+2*e ≤ R)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hdegree : ∀ p, ((tubesAt I p).card : ℝ) ≤ D)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (herror : ∀ p t, (p,t) ∈ I → dist (fine p t) (phi (angle t)) ≤ e)
    (hslab : ∀ p, ∀ f : E →L[ℝ] ℝ, ‖f‖=1 → ∀ c : ℝ,
      (((tubesAt I p).filter (fun t => |f (fine p t)-c| ≤ R)).card : ℝ) ≤ Q*D) :
    ((badCoreWitnesses I height cell angle phi S v L h).card : ℝ)
      ≤ Q*(C^5*D^2*U*(Z.card : ℝ)^2) := by
  obtain ⟨f,hunit,hzero⟩ := FinePointSlabGeometry.exists_unit_annihilator L hL
  let test : Path P T → T → Prop := fun a t =>
    |f (fine a.point₀ t)-f (fine a.point₀ a.tube₁)| ≤ R
  have hsub : badCoreWitnesses I height cell angle phi S v L h ⊆
      outgoingTest I height cell v test := by
    intro w hw
    obtain ⟨hwcore,hbad⟩ := Finset.mem_filter.mp hw
    have hm := (mem_coreOutgoing I height cell S v w).mp hwcore
    obtain ⟨ha,hb,hp,_hz₁,_hz₂,_hc⟩ := witness_conditions I height cell hm.1
    have haI := (TwoTubePathCollisionCount.mem_paths I w.1).mp ha
    have hbI := (TwoTubePathCollisionCount.mem_paths I w.2).mp hb
    have hb₀ : (w.1.point₀,w.2.tube₁) ∈ I := by simpa only [hp] using hbI.1
    have hslabmem := FinePointSlabGeometry.coarse_bad_implies_fine_affine_slab
      L f hunit hzero (fine w.1.point₀ w.1.tube₁) (fine w.1.point₀ w.2.tube₁)
      (phi (angle w.1.tube₁)) (phi (angle w.2.tube₁))
      (herror _ _ haI.1) (herror _ _ hb₀) hbad hwidth
    exact Finset.mem_filter.mpr ⟨hm.1,hm.2.2.2,hslabmem⟩
  have hcount := outgoingTest_card_le I height cell Z v test
    hC hD (mul_nonneg hQ hD) hU hheight hpoints hdegree hterminal
    (fun a => hslab a.point₀ f hunit (f (fine a.point₀ a.tube₁)))
  calc
    ((badCoreWitnesses I height cell angle phi S v L h).card : ℝ) ≤ _ := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ C^5*D*(Q*D)*U*(Z.card : ℝ)^2 := hcount
    _ = Q*(C^5*D^2*U*(Z.card : ℝ)^2) := by ring

omit [FiniteDimensional ℝ E] in
/-- Quantitative menu escape from original surviving witnesses. The only
menu-fiber bound used here is derived from actual incidence fibers. -/
theorem escapingMenus_card_bound (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (phi : A → E)
    (S : Finset (H × T)) (v : H × T) (L : Submodule ℝ E) (h : ℝ)
    {C U q : ℝ} (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a, (((tubesAt I p).filter (fun t => angle t=a)).card : ℝ) ≤ U)
    (hdegree : q ≤ ((coreOutgoing I height cell S v).card : ℝ))
    (hbad : ((badCoreWitnesses I height cell angle phi S v L h).card : ℝ) ≤ q/2) :
    q/2 ≤ C^5*U^3*((escapingMenus I height cell angle phi S v L h).card : ℝ) := by
  let W := coreOutgoing I height cell S v
  let Good := W.filter
    (fun w => h ≤ Metric.infDist (menuDifference phi (menu height angle w)) (L : Set E))
  let Menus := escapingMenus I height cell angle phi S v L h
  have hpart :
      ((badCoreWitnesses I height cell angle phi S v L h).card : ℝ)+(Good.card : ℝ)
        = (W.card : ℝ) := by
    have hp := Finset.card_filter_add_card_filter_not (s := W)
      (fun w => Metric.infDist (menuDifference phi (menu height angle w)) (L : Set E) < h)
    have hGood : W.filter (fun w => ¬ Metric.infDist
        (menuDifference phi (menu height angle w)) (L : Set E) < h)=Good := by
      ext w
      simp only [Good,Finset.mem_filter,not_lt]
    rw [hGood] at hp
    change (badCoreWitnesses I height cell angle phi S v L h).card+Good.card=W.card at hp
    exact_mod_cast hp
  have hgood : q/2 ≤ (Good.card : ℝ) := by linarith
  have hmaps : ∀ w ∈ Good, menu height angle w ∈ Menus := by
    intro w hw
    obtain ⟨hwW,hwgood⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hwW,hwgood⟩
  have hfib : ∀ g ∈ Menus,
      ((Good.filter (fun w => menu height angle w=g)).card : ℝ) ≤ C^5*U^3 := by
    intro g _hg
    have hsub : Good.filter (fun w => menu height angle w=g) ⊆ menuFiber I height cell angle v g := by
      intro w hw
      obtain ⟨hwG,hmenu⟩ := Finset.mem_filter.mp hw
      have hm := (mem_coreOutgoing I height cell S v w).mp (Finset.mem_filter.mp hwG).1
      exact Finset.mem_filter.mpr ⟨hm.1,hm.2.2.2,hmenu⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (menuFiber_card_le I height cell angle v g hC hU hpoints hterminal hangular)
  have hcount := FinePointSlabGeometry.card_le_real_mul_of_fibers
    Good Menus (menu height angle) (C^5*U^3) hmaps hfib
  calc
    q/2 ≤ (Good.card : ℝ) := hgood
    _ ≤ (Menus.card : ℝ)*(C^5*U^3) := hcount
    _ = C^5*U^3*(Menus.card : ℝ) := by ring

def vertices (I : Finset (P × T)) (height : P → H) : Finset (H × T) :=
  (TwoTubePathCollisionCount.paths I).image (endpoint height)

theorem witnesses_nonempty (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (hI : I.Nonempty) : (witnesses I height cell).Nonempty := by
  obtain ⟨⟨p,t⟩,he⟩ := hI
  let a : Path P T := ⟨p,t,p,t,p⟩
  have ha : a ∈ TwoTubePathCollisionCount.paths I :=
    (TwoTubePathCollisionCount.mem_paths I a).mpr ⟨he,he,he,he⟩
  exact ⟨(a,a),(TwoTubePathCollisionCount.mem_collisions _ _ _).mpr ⟨ha,ha,rfl⟩⟩

/-- Apply the exact REAL rich-core constructor to actual path-pair collisions.
The involution is the literal exchange of the two original branches. -/
theorem exists_original_rich_core (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (hI : I.Nonempty) {alpha B : ℝ} (halpha : 0 ≤ alpha) (hB : 0 ≤ B)
    (hmass : alpha*B*(vertices I height).card ≤ (witnesses I height cell).card) :
    ∃ S ⊆ vertices I height, S.Nonempty ∧
      (∀ v ∈ S, alpha*B/4 ≤ ((coreOutgoing I height cell S v).card : ℝ)) ∧
      ((witnesses I height cell).card : ℝ) ≤
        2*((RichWitnessCore.retained (witnesses I height cell)
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) := by
  have hbudget : 4*(alpha*B/4)*((vertices I height).card : ℝ)
      ≤ ((witnesses I height cell).card : ℝ) := by nlinarith
  obtain ⟨S,hSV,hS,_hW,hdeg,hhalf⟩ := RichWitnessRealCore.exists_half_mass_collision_core
    (TwoTubePathCollisionCount.paths I) (collisionLabel height cell) (endpoint height)
    (vertices I height) (fun a ha => Finset.mem_image_of_mem _ ha)
    (alpha*B/4) (by positivity) hbudget
    (Finset.card_pos.mpr (witnesses_nonempty I height cell hI))
  exact ⟨S,hSV,hS,hdeg,hhalf⟩

/-- Assemble original rich witnesses, full-reference pointwise slab bounds,
and actual projected-menu fibers. The resulting count is equivalent to
alpha/8 * |Z|² * (D/U)² escaping menus at EVERY core vertex and proper subspace. -/
theorem exists_escaping_core_of_point_slabs (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (phi : A → E) (fine : P → T → E)
    (Z : Finset H) (hI : I.Nonempty)
    {C D U alpha Q e h R : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hU : 0 < U)
    (halpha : 0 ≤ alpha) (hQ : 0 ≤ Q) (hbudget : Q ≤ alpha/8)
    (hwidth : h+2*e ≤ R)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hdegree : ∀ p, ((tubesAt I p).card : ℝ) ≤ D)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a, (((tubesAt I p).filter (fun t => angle t=a)).card : ℝ) ≤ U)
    (herror : ∀ p t, (p,t) ∈ I → dist (fine p t) (phi (angle t)) ≤ e)
    (hslab : ∀ p, ∀ f : E →L[ℝ] ℝ, ‖f‖=1 → ∀ c : ℝ,
      (((tubesAt I p).filter (fun t => |f (fine p t)-c| ≤ R)).card : ℝ) ≤ Q*D)
    (hmass : alpha*(C^5*D^2*U*(Z.card : ℝ)^2)*(vertices I height).card
      ≤ (witnesses I height cell).card) :
    ∃ S ⊆ vertices I height, S.Nonempty ∧
      ((witnesses I height cell).card : ℝ) ≤
        2*((RichWitnessCore.retained (witnesses I height cell)
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∀ v ∈ S, ∀ L : Submodule ℝ E, L ≠ ⊤ →
        (alpha/8)*D^2*(Z.card : ℝ)^2 ≤
          U^2*((escapingMenus I height cell angle phi S v L h).card : ℝ) := by
  let B := C^5*D^2*U*(Z.card : ℝ)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨S,hSV,hS,hdeg,hhalf⟩ := exists_original_rich_core I height cell hI halpha hB hmass
  refine ⟨S,hSV,hS,hhalf,?_⟩
  intro v hv L hL
  have hbad₀ := badCoreWitnesses_card_le I height cell angle phi fine Z S v L hL
    hC.le hD hU.le hQ hwidth hheight hpoints hdegree hterminal herror hslab
  have hbudgetB := mul_le_mul_of_nonneg_right hbudget hB
  have hbad : ((badCoreWitnesses I height cell angle phi S v L h).card : ℝ)
      ≤ (alpha*B/4)/2 := by
    change ((badCoreWitnesses I height cell angle phi S v L h).card : ℝ) ≤ Q*B at hbad₀
    linarith
  have hg := escapingMenus_card_bound I height cell angle phi S v L h hC.le hU.le
    hpoints hterminal hangular (hdeg v hv) hbad
  apply (mul_le_mul_iff_left₀ (mul_pos (pow_pos hC 5) hU)).mp
  calc
    ((alpha/8)*D^2*(Z.card : ℝ)^2)*(C^5*U) = (alpha*B/4)/2 := by dsimp [B]; ring
    _ ≤ C^5*U^3*((escapingMenus I height cell angle phi S v L h).card : ℝ) := hg
    _ = (U^2*((escapingMenus I height cell angle phi S v L h).card : ℝ))*(C^5*U) := by ring

/-- Native fine-label Frostman interface. It starts with original fine direction
sets, their bounded original tube-label fibers, graph approximation, and the
actual deterministic grid approximation. No coarse-union Frostman hypothesis
or selected-W directional law is present. All retained witnesses are original. -/
theorem exists_escaping_core_of_fine_frostman
    (I : Finset (P × T)) (height : P → H) (cell : T → K) (angle : T → A)
    (Phi : P → Finset E) (fine : P → T → E) (realizer : P → E → T)
    (actual : T → E) (phi : A → E)
    (Z : Finset H) (hI : I.Nonempty)
    {C D U alpha mu nu F gamma delta R eFine eGrid h : ℝ}
    (hC : 0 < C) (hD : 0 ≤ D) (hU : 0 < U) (halpha : 0 ≤ alpha)
    (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) (hF : 0 ≤ F) (hR : 0 < R)
    (hdelta : delta ≤ R) (hRone : R ≤ 1)
    (hbudget : mu*nu*F*R^gamma ≤ alpha/8) (hwidth : h+2*(eFine+eGrid) ≤ R)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hdegree : ∀ p, ((tubesAt I p).card : ℝ) ≤ D)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a, (((tubesAt I p).filter (fun t => angle t=a)).card : ℝ) ≤ U)
    (hmaps : ∀ p t, (p,t) ∈ I → fine p t ∈ Phi p)
    (hfiber : ∀ p u, u ∈ Phi p →
      (((tubesAt I p).filter (fun t => fine p t=u)).card : ℝ) ≤ mu)
    (hrealizer : ∀ p u, u ∈ Phi p → (p,realizer p u) ∈ I)
    (hrealizerFiber : ∀ p t, t ∈ tubesAt I p →
      (((Phi p).filter (fun u => realizer p u=t)).card : ℝ) ≤ nu)
    (hFineError : ∀ p t, (p,t) ∈ I → dist (fine p t) (actual t) ≤ eFine)
    (hGridError : ∀ p t, (p,t) ∈ I → dist (actual t) (phi (angle t)) ≤ eGrid)
    (hslab : ∀ p, ∀ f : E →L[ℝ] ℝ, ‖f‖=1 → ∀ c r : ℝ, delta ≤ r → r ≤ 1 →
      (((Phi p).filter (fun u => |f u-c| ≤ r)).card : ℝ) ≤ F*r^gamma*((Phi p).card : ℝ))
    (hmass : alpha*(C^5*D^2*U*(Z.card : ℝ)^2)*(vertices I height).card
      ≤ (witnesses I height cell).card) :
    ∃ S ⊆ vertices I height, S.Nonempty ∧
      ((witnesses I height cell).card : ℝ) ≤
        2*((RichWitnessCore.retained (witnesses I height cell)
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∀ v ∈ S, ∀ L : Submodule ℝ E, L ≠ ⊤ →
        (alpha/8)*D^2*(Z.card : ℝ)^2 ≤
          U^2*((escapingMenus I height cell angle phi S v L h).card : ℝ) := by
  have herror : ∀ p t, (p,t) ∈ I → dist (fine p t) (phi (angle t)) ≤ eFine+eGrid := by
    intro p t hpt
    exact FinePointSlabGeometry.fine_coarse_error_of_actual_direction _ _ _
      (hFineError p t hpt) (hGridError p t hpt)
  have hpointSlab : ∀ p, ∀ f : E →L[ℝ] ℝ, ‖f‖=1 → ∀ c : ℝ,
      (((tubesAt I p).filter (fun t => |f (fine p t)-c| ≤ R)).card : ℝ) ≤ (mu*nu*F*R^gamma)*D := by
    intro p f hf c
    exact FinePointSlabGeometry.tube_slab_with_original_degree
      (tubesAt I p) (Phi p) (fine p) (realizer p) f c hmu hnu hF hR hdelta hRone hf
      (hdegree p) (fun t ht => hmaps p t ((mem_tubesAt I p t).mp ht)) (hfiber p)
      (fun u hu => (mem_tubesAt I p (realizer p u)).mpr (hrealizer p u hu))
      (hrealizerFiber p) (hslab p)
  exact exists_escaping_core_of_point_slabs I height cell angle phi fine Z hI
    hC hD hU halpha (by positivity) hbudget hwidth hheight hpoints hdegree
    hterminal hangular herror hpointSlab hmass

end
end OriginalWCoarseEscapeMenus
