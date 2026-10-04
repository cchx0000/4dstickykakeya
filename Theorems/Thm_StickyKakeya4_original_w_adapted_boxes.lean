import Theorems.Thm_StickyKakeya4_original_w_physical_displacement
import Theorems.Thm_StickyKakeya4_original_w_core_dynamics
import Theorems.Thm_StickyKakeya4_two_walk_box_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalWAdaptedBoxes
open OriginalWWitnessCounts OriginalWPhysicalDisplacement TwoWalkBoxComparison
open Classical

variable {P T K U V : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The terminal point is any genuine representative on the original terminal
 tube at its exact original height; the original intermediate point is retained. -/
def originalWalk (x : P → U) (y offset : P → V) (u : T → U) (v : T → V)
    (a : Path P T) (p : P) : Walk U V where
  u := u a.tube₁
  v := v a.tube₁
  terminalU := u a.tube₂
  terminalV := v a.tube₂
  offset := offset a.point₁
  middleX := x a.point₁
  middleY := y a.point₁
  terminalX := x p
  terminalY := y p

/-- Literal original W coordinates, with no geometric conclusion as a field. -/
def originalData (height : P → ℝ) (x : P → U) (y offset : P → V)
    (u : T → U) (v : T → V) (F : ℝ → U →L[ℝ] V)
    (w : Path P T × Path P T) (p₁ p₂ : P) : Data U V where
  F₀ := F (height w.1.point₀)
  F₁ := F (height w.1.point₁)
  F₂ := F (height w.1.point₂)
  commonOffset := offset w.1.point₀
  startX := x w.1.point₀
  startY := y w.1.point₀
  z₀ := height w.1.point₀
  z₁ := height w.1.point₁
  z₂ := height w.1.point₂
  first := originalWalk x y offset u v w.1 p₁
  second := originalWalk x y offset u v w.2 p₂

/-- Primitive original incidence and same-point direction laws supply all
 inputs of Claim 19.3. In particular, shared starts and times are recovered
 from the actual W collision label, rather than separately assumed. -/
theorem original_data_bounds (I : Finset (P × T)) (height : P → ℝ)
    (cell : T → K) (x : P → U) (y offset : P → V)
    (baseU u : T → U) (baseV v : T → V) (F : ℝ → U →L[ℝ] V)
    (Z : Finset ℝ) {A B S epsilon IncErr DirErr rho : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S) (he : 0 ≤ epsilon) (hrho : 0 ≤ rho)
    (hInc : 2*IncErr ≤ epsilon) (hDir : DirErr ≤ epsilon)
    (hincU : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height x baseU u p t‖ ≤ IncErr)
    (hincV : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height y baseV v p t‖ ≤ IncErr)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖u t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ A)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ S)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hcell : ∀ s t, cell s=cell t → ‖u s-u t‖ ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell)
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂) :
    (originalData height x y offset u v F w p₁ p₂).Bounds A B S epsilon rho := by
  obtain ⟨ha,hb,hp,hzmid,hzend,hc⟩ := witness_conditions I height cell hw
  obtain ⟨ha₀,ha₁,ha₂,ha₃⟩ := (TwoTubePathCollisionCount.mem_paths I w.1).mp ha
  obtain ⟨hb₀,hb₁,hb₂,hb₃⟩ := (TwoTubePathCollisionCount.mem_paths I w.2).mp hb
  have z₀ := hheight _ (Finset.mem_image_of_mem Prod.fst ha₀)
  have z₁ := hheight _ (Finset.mem_image_of_mem Prod.fst ha₁)
  have z₂ := hheight _ (Finset.mem_image_of_mem Prod.fst ha₃)
  have eU₁ := (incidence_chord_error I height x baseU u hincU ha₀ ha₁).trans hInc
  have eV₁ := (incidence_chord_error I height y baseV v hincV ha₀ ha₁).trans hInc
  have eU₂ := (incidence_chord_error I height x baseU u hincU ha₂ hp₁).trans hInc
  have eV₂ := (incidence_chord_error I height y baseV v hincV ha₂ hp₁).trans hInc
  have eU₃ := (incidence_chord_error I height x baseU u hincU hb₀ hb₁).trans hInc
  have eV₃ := (incidence_chord_error I height y baseV v hincV hb₀ hb₁).trans hInc
  have eU₄ := (incidence_chord_error I height x baseU u hincU hb₂ hp₂).trans hInc
  have eV₄ := (incidence_chord_error I height y baseV v hincV hb₂ hp₂).trans hInc
  refine ⟨hA,hB,hS,he,hrho,hF _ z₂,hcluster _ z₀ _ z₁,hcluster _ z₁ _ z₂,
    hcluster _ z₀ _ z₂,hdiam _ z₁ _ z₀,hdiam _ z₂ _ z₁,?_,?_,hcell _ _ hc⟩
  · refine ⟨hu _ (Finset.mem_image_of_mem Prod.snd ha₀),
      (hdir _ _ ha₀).trans hDir,(hdir _ _ ha₁).trans hDir,(hdir _ _ ha₂).trans hDir,
      eU₁,eV₁,?_,?_⟩
    · simpa only [originalData,originalWalk,Data.secondErrorX,Data.s,hz₁] using eU₂
    · simpa only [originalData,originalWalk,Data.secondErrorY,Data.s,hz₁] using eV₂
  · refine ⟨hu _ (Finset.mem_image_of_mem Prod.snd hb₀),?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [originalData,originalWalk,Data.initialResidual,hp] using (hdir _ _ hb₀).trans hDir
    · simpa only [originalData,originalWalk,Data.middleResidual,hzmid] using (hdir _ _ hb₁).trans hDir
    · simpa only [originalData,originalWalk,Data.terminalResidual,hzmid] using (hdir _ _ hb₂).trans hDir
    · simpa only [originalData,originalWalk,Data.firstErrorX,Data.t,hp,hzmid] using eU₃
    · simpa only [originalData,originalWalk,Data.firstErrorY,Data.t,hp,hzmid] using eV₃
    · simpa only [originalData,originalWalk,Data.secondErrorX,Data.s,hz₂,hzend,hzmid] using eU₄
    · simpa only [originalData,originalWalk,Data.secondErrorY,Data.s,hz₂,hzend,hzmid] using eV₄

/-- Actual original witnesses give mutual containment of their explicitly
 constructed physical boxes. Error constants retain their full dependence. -/
theorem original_witness_box_comparison (I : Finset (P × T)) (height : P → ℝ)
    (cell : T → K) (x : P → U) (y offset : P → V)
    (baseU u : T → U) (baseV v : T → V) (F : ℝ → U →L[ℝ] V)
    (Z : Finset ℝ) {A B S₀ E IncErr DirErr delta sigma rho : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S₀) (hE : 0 ≤ E)
    (hd : 0 ≤ delta) (hdσ : delta ≤ sigma) (hσρ : sigma ≤ rho) (hrho : rho ≤ 1)
    (hInc : 2*IncErr ≤ E) (hDir : DirErr ≤ E)
    (hincU : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖u t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ A)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ S₀*sigma)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hcell : ∀ s t, cell s=cell t → ‖u s-u t‖ ≤ rho)
    (w : Path P T × Path P T) (hw : w ∈ witnesses I height cell)
    (p₁ p₂ : P) (hp₁ : (p₁,w.1.tube₂) ∈ I) (hp₂ : (p₂,w.2.tube₂) ∈ I)
    (hz₁ : height p₁=height w.1.point₂) (hz₂ : height p₂=height w.2.point₂)
    (L : ℝ) (hL : 1 ≤ L) :
    let D := originalData height x y offset u v F w p₁ p₂
    box D.F₂ D.first D.z₂ rho sigma L ⊆
        box D.F₂ D.second D.z₂ rho sigma (comparisonConstant A B E S₀*L) ∧
      box D.F₂ D.second D.z₂ rho sigma L ⊆
        box D.F₂ D.first D.z₂ rho sigma (comparisonConstant A B E S₀*L) := by
  have hsigma : 0 ≤ sigma := hd.trans hdσ
  have he : 2*(IncErr*delta) ≤ E*delta := by nlinarith [mul_le_mul_of_nonneg_right hInc hd]
  have hb := original_data_bounds I height cell x y offset baseU u baseV v F Z
    hA hB (mul_nonneg hS hsigma) (mul_nonneg hE hd) (hsigma.trans hσρ)
    he (mul_le_mul_of_nonneg_right hDir hd) hincU hincV hdir hu hF hcluster
    hheight hdiam hcell w hw p₁ p₂ hp₁ hp₂ hz₁ hz₂
  exact two_walk_box_comparison _ A B E S₀ delta sigma rho hb hE hS hd hdσ hσρ hrho L hL

/-- A box attached to an actual original point and its incident tube. The
 unused walk fields are zero; its defining inequalities use only the terminal
 point, slope and exact terminal height. -/
def terminalWalk (x : P → U) (y : P → V) (u : T → U) (v : T → V)
    (p : P) (t : T) : Walk U V where
  u := 0
  v := 0
  terminalU := u t
  terminalV := v t
  offset := 0
  middleX := 0
  middleY := 0
  terminalX := x p
  terminalY := y p

def coreBox (I : Finset (P × T)) (height : P → ℝ) (x : P → U) (y : P → V)
    (u : T → U) (v : T → V) (F : ℝ → U →L[ℝ] V)
    (S : Finset (ℝ × T)) (hSV : S ⊆ OriginalWCoarseEscapeMenus.vertices I height)
    (state : OriginalWCoreDynamics.Core S) (rho sigma L : ℝ) : Set (SpaceTime U V) :=
  box (F state.val.1)
    (terminalWalk x y u v (OriginalWCoreDynamics.rep I height S hSV state) state.val.2)
    state.val.1 rho sigma L

/-- Each deterministic occupied menu gives the actual adapted-box comparison.
 The caller supplies original incidence geometry, rather than a successor or
 endpoint-gap certificate. -/
theorem constructed_successor_box_comparison {Angle : Type*} [DecidableEq Angle]
    (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (angle : T → Angle)
    (x : P → U) (y offset : P → V) (baseU u : T → U) (baseV v : T → V)
    (F : ℝ → U →L[ℝ] V) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ OriginalWCoarseEscapeMenus.vertices I height)
    {A B S₀ E IncErr DirErr delta sigma rho : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 ≤ S₀) (hE : 0 ≤ E)
    (hd : 0 ≤ delta) (hdσ : delta ≤ sigma) (hσρ : sigma ≤ rho) (hrho : rho ≤ 1)
    (hInc : 2*IncErr ≤ E) (hDir : DirErr ≤ E)
    (hincU : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height y baseV v p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I → ‖v t-offset p-F (height p) (u t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖u t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ A)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ S₀*sigma)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hcell : ∀ s t, cell s=cell t → ‖u s-u t‖ ≤ rho)
    (state : OriginalWCoreDynamics.Core S)
    (g : (ℝ × ℝ) × (Angle × Angle))
    (hg : g ∈ OriginalWCoreDynamics.M I height cell angle S state)
    (L : ℝ) (hL : 1 ≤ L) :
    let next := OriginalWCoreDynamics.next I height cell angle S state g
    coreBox I height x y u v F S hSV state rho sigma L ⊆
      coreBox I height x y u v F S hSV next rho sigma (comparisonConstant A B E S₀*L) ∧
    coreBox I height x y u v F S hSV next rho sigma L ⊆
      coreBox I height x y u v F S hSV state rho sigma (comparisonConstant A B E S₀*L) := by
  obtain ⟨hn,w,hw,hl,hr,_hm⟩ := OriginalWCoreDynamics.next_spec I height cell angle S state g hg
  let target := OriginalWCoreDynamics.next I height cell angle S state g
  have hlz : height w.1.point₂=state.val.1 := congrArg Prod.fst hl
  have hlt : w.1.tube₂=state.val.2 := congrArg Prod.snd hl
  have hrz : height w.2.point₂=target.val.1 := congrArg Prod.fst hr
  have hrt : w.2.tube₂=target.val.2 := congrArg Prod.snd hr
  have hp := OriginalWCoreDynamics.rep_spec I height S hSV state
  have hq := OriginalWCoreDynamics.rep_spec I height S hSV target
  have hpI : (OriginalWCoreDynamics.rep I height S hSV state,w.1.tube₂) ∈ I := by
    simpa only [hlt] using hp.1
  have hqI : (OriginalWCoreDynamics.rep I height S hSV target,w.2.tube₂) ∈ I := by
    simpa only [hrt] using hq.1
  have hpz : height (OriginalWCoreDynamics.rep I height S hSV state)=height w.1.point₂ := hp.2.trans hlz.symm
  have hqz : height (OriginalWCoreDynamics.rep I height S hSV target)=height w.2.point₂ := hq.2.trans hrz.symm
  have hc := original_witness_box_comparison I height cell x y offset baseU u baseV v F Z
    hA hB hS hE hd hdσ hσρ hrho hInc hDir hincU hincV hdir hu hF hcluster hheight hdiam
    hcell w hw (OriginalWCoreDynamics.rep I height S hSV state)
    (OriginalWCoreDynamics.rep I height S hSV target) hpI hqI hpz hqz L hL
  simpa only [coreBox,box,tangentResidual,normalResidual,originalData,originalWalk,
    terminalWalk,hlt,hrt,hlz,hn] using hc

end OriginalWAdaptedBoxes
