import Theorems.Thm_StickyKakeya4_original_w_core_dynamics

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalCoreMenuDensity
open Classical OriginalWWitnessCounts OriginalWCoarseEscapeMenus

variable {P T H K A : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
  [DecidableEq K] [DecidableEq A]

/-- All actual menus, rather than escaping menus, inherit the original core
 degree divided by the derived original witness fiber C0^5 U^3. -/
theorem all_menus_card_bound (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (S : Finset (H × T)) (v : H × T)
    {C U q : ℝ} (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a, (((tubesAt I p).filter (fun t => angle t=a)).card : ℝ) ≤ U)
    (hdegree : q ≤ ((coreOutgoing I height cell S v).card : ℝ)) :
    q ≤ C^5*U^3*((coarseMenus I height cell angle S v).card : ℝ) := by
  let W := coreOutgoing I height cell S v
  let Menus := coarseMenus I height cell angle S v
  have hmaps : ∀ w ∈ W, menu height angle w ∈ Menus :=
    fun w hw => Finset.mem_image_of_mem _ hw
  have hfib : ∀ g ∈ Menus, ((W.filter (fun w => menu height angle w=g)).card : ℝ) ≤ C^5*U^3 := by
    intro g _hg
    have hsub : W.filter (fun w => menu height angle w=g) ⊆ menuFiber I height cell angle v g := by
      intro w hw
      obtain ⟨hwW,hmenu⟩ := Finset.mem_filter.mp hw
      have hm := (mem_coreOutgoing I height cell S v w).mp hwW
      exact Finset.mem_filter.mpr ⟨hm.1,hm.2.2.2,hmenu⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (menuFiber_card_le I height cell angle v g hC hU hpoints hterminal hangular)
  have hc := FinePointSlabGeometry.card_le_real_mul_of_fibers W Menus (menu height angle)
    (C^5*U^3) hmaps hfib
  calc
    q ≤ (W.card : ℝ) := hdegree
    _ ≤ (Menus.card : ℝ)*(C^5*U^3) := hc
    _ = C^5*U^3*(Menus.card : ℝ) := by ring

/-- Phase-menu richness from original W collision mass, with no slab or
 subspace-escape hypothesis and no gamma loss. The genuine original core and
 both original height/angular alphabets are constructed. -/
theorem exists_original_menu_rich_core
    (I : Finset (P × T)) (height : P → H) (cell : T → K) (angle : T → A)
    (Z : Finset H) (hI : I.Nonempty)
    {C D U alpha : ℝ} (hC : 0 < C) (hU : 0 < U) (halpha : 0 ≤ alpha)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a, (((tubesAt I p).filter (fun t => angle t=a)).card : ℝ) ≤ U)
    (hmass : alpha*(C^5*D^2*U*(Z.card : ℝ)^2)*(vertices I height).card ≤ (witnesses I height cell).card) :
    ∃ S ⊆ vertices I height, S.Nonempty ∧
      ((witnesses I height cell).card : ℝ) ≤
        2*((RichWitnessCore.retained (witnesses I height cell)
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∀ v ∈ S,
        (alpha/4)*D^2*(Z.card : ℝ)^2 ≤ U^2*((coarseMenus I height cell angle S v).card : ℝ) ∧
        coarseMenus I height cell angle S v ⊆ (Z ×ˢ Z) ×ˢ
          ((OriginalWCoreDynamics.angles I angle) ×ˢ (OriginalWCoreDynamics.angles I angle)) := by
  let B := C^5*D^2*U*(Z.card : ℝ)^2
  obtain ⟨S,hSV,hS,hdeg,hhalf⟩ := exists_original_rich_core I height cell hI halpha
    (show 0 ≤ B by dsimp [B]; positivity) hmass
  refine ⟨S,hSV,hS,hhalf,?_⟩
  intro v hv
  constructor
  · have hc := all_menus_card_bound I height cell angle S v hC.le hU.le hpoints hterminal hangular (hdeg v hv)
    apply (mul_le_mul_iff_left₀ (mul_pos (pow_pos hC 5) hU)).mp
    calc
      ((alpha/4)*D^2*(Z.card : ℝ)^2)*(C^5*U) = alpha*B/4 := by dsimp [B]; ring
      _ ≤ C^5*U^3*((coarseMenus I height cell angle S v).card : ℝ) := hc
      _ = (U^2*((coarseMenus I height cell angle S v).card : ℝ))*(C^5*U) := by ring
  · intro g hg
    obtain ⟨w,hw,_hl,_hr,hm⟩ := coarse_menu_has_original_partner I height cell angle S v hg
    rw [← hm]
    exact OriginalWCoreDynamics.witness_menu_mem_alphabet I height cell angle Z hheight hw

/-- Explicit normalization against the ORIGINAL angular alphabet size. -/
theorem normalize_phase_menu_degree {alpha beta D U N m M : ℝ}
    (hU : 0 < U) (hscale : 4*beta*U^2*m^2 ≤ alpha*D^2)
    (hdegree : (alpha/4)*D^2*N^2 ≤ U^2*M) :
    beta*N^2*m^2 ≤ M := by
  have hh := mul_le_mul_of_nonneg_right hscale (sq_nonneg N)
  have hp : 0 < U^2 := sq_pos_of_pos hU
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

end OriginalCoreMenuDensity
