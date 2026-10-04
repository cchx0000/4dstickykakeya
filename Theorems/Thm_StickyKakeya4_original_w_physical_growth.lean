import Theorems.Thm_StickyKakeya4_original_w_core_dynamics
import Theorems.Thm_StickyKakeya4_original_w_physical_displacement
import Theorems.Thm_StickyKakeya4_original_height_interval_cap
import Theorems.Thm_StickyKakeya4_native_planar_slab_norm_conversion

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace OriginalWPhysicalGrowth
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWPhysicalDisplacement
open Classical
noncomputable section

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

def coordinates {E : Type*} (I : Finset (P × T)) (height : P → ℝ) (position : P → E)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height) (v : OriginalWCoreDynamics.Core S) : E :=
  position (OriginalWCoreDynamics.rep I height S hSV v)

def scalarCells (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ)
    (theta : T → Fin 3 → ℝ) (q rho : ℝ) (S : Finset (ℝ × T))
    (hSV : S ⊆ vertices I height) (root : OriginalWCoreDynamics.Core S) : Finset ℤ :=
  FiniteTransverseMenuGrowth.oneStepCells
    (OriginalWCoreDynamics.M I height (terminalGrid q theta) (scalarAngle q theta) S)
    (OriginalWCoreDynamics.next I height (terminalGrid q theta) (scalarAngle q theta) S)
    (coordinates I height position S hSV) root (rho^2)

def planarCells (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ × ℝ)
    (theta : T → Fin 3 → ℝ) (q rho : ℝ) (S : Finset (ℝ × T))
    (hSV : S ⊆ vertices I height) (root : OriginalWCoreDynamics.Core S) : Finset (ℤ × ℤ) :=
  FiniteTransverseMenuGrowth.planarTwoStepCells
    (OriginalWCoreDynamics.M I height (terminalGrid q theta) (planarAngle q theta) S)
    (OriginalWCoreDynamics.next I height (terminalGrid q theta) (planarAngle q theta) S)
    (coordinates I height position S hSV) root (rho^2)

theorem scalar_constructed_step_displacement
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ)
    (base : T → ℝ) (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    {delta rho q Err : ℝ} (hrho : 0 ≤ rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hErr : 0 ≤ Err) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (scalarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (v : OriginalWCoreDynamics.Core S) (g : (ℝ × ℝ) × (ℤ × ℤ))
    (hg : g ∈ OriginalWCoreDynamics.M I height (terminalGrid q theta) (scalarAngle q theta) S v) :
    |coordinates I height position S hSV
        (OriginalWCoreDynamics.next I height (terminalGrid q theta) (scalarAngle q theta) S v g)-
      coordinates I height position S hSV v-(g.1.2-g.1.1)*(scalarDecode q g.2.2-scalarDecode q g.2.1)|
        ≤ (3+12*Err)*rho^2 := by
  obtain ⟨w,hw,hl,hr,hm⟩ :=
    (OriginalWCoreDynamics.next_spec I height (terminalGrid q theta) (scalarAngle q theta) S v g hg).2
  have hpl := OriginalWCoreDynamics.rep_spec I height S hSV v
  have hpr := OriginalWCoreDynamics.rep_spec I height S hSV
    (OriginalWCoreDynamics.next I height (terminalGrid q theta) (scalarAngle q theta) S v g)
  have htl : w.1.tube₂=v.val.2 := congrArg Prod.snd hl
  have htr : w.2.tube₂=(OriginalWCoreDynamics.next I height (terminalGrid q theta)
      (scalarAngle q theta) S v g).val.2 := congrArg Prod.snd hr
  have hd := scalar_native_witness_displacement I height position base theta Z
    hrho hq hqρ hErr hdelta hinc hheight hdiam w hw
    (OriginalWCoreDynamics.rep I height S hSV v)
    (OriginalWCoreDynamics.rep I height S hSV
      (OriginalWCoreDynamics.next I height (terminalGrid q theta) (scalarAngle q theta) S v g))
    (by rw [htl]; exact hpl.1) (by rw [htr]; exact hpr.1)
    (hpl.2.trans (congrArg Prod.fst hl).symm) (hpr.2.trans (congrArg Prod.fst hr).symm)
  have htime := congrArg Prod.fst hm
  have hangle := congrArg Prod.snd hm
  have hz₀ : height w.1.point₀=g.1.1 := congrArg Prod.fst htime
  have hz₁ : height w.1.point₁=g.1.2 := congrArg Prod.snd htime
  have ha₁ : scalarAngle q theta w.1.tube₁=g.2.1 := congrArg Prod.fst hangle
  have ha₂ : scalarAngle q theta w.2.tube₁=g.2.2 := congrArg Prod.snd hangle
  rw [hz₀,hz₁,ha₁,ha₂] at hd
  simpa only [coordinates,Real.norm_eq_abs,smul_eq_mul] using hd

theorem planar_constructed_step_displacement
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ × ℝ)
    (base : T → ℝ × ℝ) (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height)
    {delta rho q Err : ℝ} (hrho : 0 ≤ rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hErr : 0 ≤ Err) (hdelta : delta ≤ rho^2)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (planarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (v : OriginalWCoreDynamics.Core S) (g : (ℝ × ℝ) × ((ℤ × ℤ) × (ℤ × ℤ)))
    (hg : g ∈ OriginalWCoreDynamics.M I height (terminalGrid q theta) (planarAngle q theta) S v) :
    ‖coordinates I height position S hSV
        (OriginalWCoreDynamics.next I height (terminalGrid q theta) (planarAngle q theta) S v g)-
      coordinates I height position S hSV v-(g.1.2-g.1.1) • (planarDecode q g.2.2-planarDecode q g.2.1)‖
        ≤ (3+12*Err)*rho^2 := by
  obtain ⟨w,hw,hl,hr,hm⟩ :=
    (OriginalWCoreDynamics.next_spec I height (terminalGrid q theta) (planarAngle q theta) S v g hg).2
  have hpl := OriginalWCoreDynamics.rep_spec I height S hSV v
  have hpr := OriginalWCoreDynamics.rep_spec I height S hSV
    (OriginalWCoreDynamics.next I height (terminalGrid q theta) (planarAngle q theta) S v g)
  have htl : w.1.tube₂=v.val.2 := congrArg Prod.snd hl
  have htr : w.2.tube₂=(OriginalWCoreDynamics.next I height (terminalGrid q theta)
      (planarAngle q theta) S v g).val.2 := congrArg Prod.snd hr
  have hd := planar_native_witness_displacement I height position base theta Z
    hrho hq hqρ hErr hdelta hinc hheight hdiam w hw
    (OriginalWCoreDynamics.rep I height S hSV v)
    (OriginalWCoreDynamics.rep I height S hSV
      (OriginalWCoreDynamics.next I height (terminalGrid q theta) (planarAngle q theta) S v g))
    (by rw [htl]; exact hpl.1) (by rw [htr]; exact hpr.1)
    (hpl.2.trans (congrArg Prod.fst hl).symm) (hpr.2.trans (congrArg Prod.fst hr).symm)
  have htime := congrArg Prod.fst hm
  have hangle := congrArg Prod.snd hm
  have hz₀ : height w.1.point₀=g.1.1 := congrArg Prod.fst htime
  have hz₁ : height w.1.point₁=g.1.2 := congrArg Prod.snd htime
  have ha₁ : planarAngle q theta w.1.tube₁=g.2.1 := congrArg Prod.fst hangle
  have ha₂ : planarAngle q theta w.2.tube₁=g.2.2 := congrArg Prod.snd hangle
  rw [hz₀,hz₁,ha₁,ha₂] at hd
  exact hd

omit [DecidableEq T] in
theorem original_heights_nonempty (I : Finset (P × T)) (height : P → ℝ) (Z : Finset ℝ)
    (hI : I.Nonempty)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z) : Z.Nonempty := by
  obtain ⟨pt,hpt⟩ := hI
  exact ⟨height pt.1,hheight _ (Finset.mem_image_of_mem Prod.fst hpt)⟩

/-- Apply native a=1 growth to the constructed original core dynamics. The
successor, representative, displacement, and time cap are all DERIVED. The
escape bound is the already-proved output of the original fine-Frostman core. -/
theorem scalar_growth_of_constructed_core
    (I : Finset (P × T)) (height : P → ℝ) (position : P → ℝ)
    (base : T → ℝ) (theta : T → Fin 3 → ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height) (root : OriginalWCoreDynamics.Core S)
    {delta rho q Err h beta : ℝ} (hI : I.Nonempty)
    (hdeltapos : 0 < delta) (hrhopos : 0 < rho) (hq : 0 < q) (hqρ : q ≤ rho)
    (hErr : 0 ≤ Err) (hdelta : delta ≤ rho^2) (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (scalarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hmesh : ∀ z ∈ Z, ∃ k : ℤ, z=delta*(k : ℝ))
    (hescape : ∀ v ∈ S, ∀ L : Submodule ℝ ℝ, L ≠ ⊤ →
      beta*(Z.card : ℝ)^2*(OriginalWCoreDynamics.angles I (scalarAngle q theta)).card^2 ≤
        ((escapingMenus I height (terminalGrid q theta) (scalarAngle q theta)
          (scalarDecode q) S v L h).card : ℝ)) :
    beta*h*(Z.card : ℝ) ≤
      (4+4*(3+12*Err))*(3*rho^2/delta)*(scalarCells I height position theta q rho S hSV root).card := by
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
    exact OriginalHeightIntervalCap.original_interval_cap Z hdeltapos hmesh c (rho^2) hdelta
  · intro v g hg
    exact scalar_constructed_step_displacement I height position base theta Z S hSV
      hrhopos.le hq hqρ hErr hdelta hinc hheight hdiam v g hg
  · intro v L hL
    exact hescape v.val v.property L hL

omit [DecidableEq P] in
theorem planar_decoded_alphabet_bound (I : Finset (P × T)) (theta : T → Fin 3 → ℝ)
    {q : ℝ} (hq : 0 < q) (hqone : q ≤ 1)
    (hslope : ∀ t j, |theta t j| ≤ 1) :
    ∀ a ∈ OriginalWCoreDynamics.angles I (planarAngle q theta),
      ‖planarDecode q a‖ ≤ 2 := by
  intro a ha
  obtain ⟨t,_ht,rfl⟩ := Finset.mem_image.mp ha
  have hu : ‖planarSlope theta t‖ ≤ 1 := max_le (hslope t 0) (hslope t 1)
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
    {delta rho q Err h beta : ℝ} (hI : I.Nonempty)
    (hdeltapos : 0 < delta) (hrhopos : 0 < rho) (hrhoone : rho ≤ 1)
    (hq : 0 < q) (hqρ : q ≤ rho) (hErr : 0 ≤ Err) (hdelta : delta ≤ rho^2)
    (hh : 0 < h) (hhone : h ≤ 1) (hbeta : 0 < beta)
    (hslope : ∀ t j, |theta t j| ≤ 1)
    (hinc : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height position base (planarSlope theta) p t‖ ≤ Err*delta)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hmesh : ∀ z ∈ Z, ∃ k : ℤ, z=delta*(k : ℝ))
    (hescape : ∀ v ∈ S, ∀ L : Submodule ℝ (ℝ × ℝ), L ≠ ⊤ →
      beta*(Z.card : ℝ)^2*(OriginalWCoreDynamics.angles I (planarAngle q theta)).card^2 ≤
        ((escapingMenus I height (terminalGrid q theta) (planarAngle q theta)
          (planarDecode q) S v L h).card : ℝ)) :
    beta^2*h^4*(Z.card : ℝ)^2 ≤
      (4*4*(1+4*(3+12*Err))+2)^2*(3*rho^2/delta)^2*
        (planarCells I height position theta q rho S hSV root).card := by
  apply FiniteTransverseMenuGrowth.planar_menu_growth
    Z (OriginalWCoreDynamics.angles I (planarAngle q theta))
    (OriginalWCoreDynamics.M I height (terminalGrid q theta) (planarAngle q theta) S)
    (OriginalWCoreDynamics.next I height (terminalGrid q theta) (planarAngle q theta) S)
    (coordinates I height position S hSV) (planarDecode q) root
    (original_heights_nonempty I height Z hI hheight)
    (OriginalWCoreDynamics.angles_nonempty I (planarAngle q theta) hI)
    (sq_pos_of_pos hrhopos) (by positivity) (by positivity) hh hhone hbeta (by norm_num)
  · intro a ha b hb
    have hbound := planar_decoded_alphabet_bound I theta hq (hqρ.trans hrhoone) hslope
    have hn : ‖planarDecode q b-planarDecode q a‖ ≤ 4 := by
      have ht := norm_sub_le (planarDecode q b) (planarDecode q a)
      have ha₂ := hbound a ha
      have hb₂ := hbound b hb
      linarith
    change max |(planarDecode q b).1-(planarDecode q a).1|
      |(planarDecode q b).2-(planarDecode q a).2| ≤ 4 at hn
    exact ⟨(le_max_left _ _).trans hn,(le_max_right _ _).trans hn⟩
  · exact OriginalWCoreDynamics.M_subset_alphabet I height (terminalGrid q theta)
      (planarAngle q theta) S Z hheight
  · intro c
    exact OriginalHeightIntervalCap.original_interval_cap Z hdeltapos hmesh c (rho^2) hdelta
  · intro v g hg
    have hd := planar_constructed_step_displacement I height position base theta Z S hSV
      hrhopos.le hq hqρ hErr hdelta hinc hheight hdiam v g hg
    simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
      Real.norm_eq_abs,smul_eq_mul,FiniteTransverseMenuGrowth.angularDifference] using hd
  · intro v L hL
    exact hescape v.val v.property L hL

/-- Numerical conversion of the ORIGINAL reference normalization. This lemma
does not assert any selected-family angular uniformity. -/
lemma normalize_original_escape {alpha beta D U N m M : ℝ} (hU : 0 < U)
    (hbudget : 8*beta*U^2*m^2 ≤ alpha*D^2)
    (hescape : (alpha/8)*D^2*N^2 ≤ U^2*M) : beta*N^2*m^2 ≤ M := by
  have hb := mul_le_mul_of_nonneg_right hbudget (sq_nonneg N)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hU)).mp
  nlinarith

end
end OriginalWPhysicalGrowth
