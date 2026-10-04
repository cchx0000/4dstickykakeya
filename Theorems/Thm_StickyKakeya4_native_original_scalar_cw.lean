import Theorems.Thm_StickyKakeya4_native_original_ancestor_counts
import Theorems.Thm_StickyKakeya4_original_carrier_image_count
import Theorems.Thm_StickyKakeya4_original_cw_scale_cancellation
import Theorems.Thm_StickyKakeya4_original_core_box_paths
import Theorems.Thm_StickyKakeya4_adapted_box_volume

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeOriginalScalarCW
open Classical MeasureTheory Metric
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWCoreDynamics
open OriginalWPhysicalDisplacement OriginalWAdaptedBoxes OriginalTubeAncestorSaturation
open OriginalAncestorCounting OriginalCoreEndpointLifting TwoWalkBoxComparison

abbrev Space := SpaceTime ℝ (ℝ × ℝ)

/-- Literal full-original-family convex-Wolff counting law. The set ranges
 over all convex measurable sets, not one box with a supplied count. -/
def OriginalConvexWolffLaw {T : Type*} (Tfull : Finset T) (tube : T → Set Space) (CW : ℝ) : Prop :=
  ∀ B : Set Space, Convex ℝ B → MeasurableSet B →
    ((Tfull.filter (fun t => tube t ⊆ B)).card : ENNReal) ≤
      ENNReal.ofReal CW*volume B*(Tfull.card : ENNReal)

def normalSlope {T : Type*} (theta : T → Fin 3 → ℝ) (t : T) : ℝ × ℝ := (theta t 1,theta t 2)

def ancestorDilation (A IncErr DirErr FineErr : ℝ) : ℝ :=
  max 2 (max (3+IncErr+2*(1+2*FineErr)) ((1+A)*(3+IncErr)+4*DirErr))

lemma adapted_box_measurable (F : ℝ →L[ℝ] ℝ × ℝ) (w : Walk ℝ (ℝ × ℝ))
    (z rho sigma L : ℝ) : MeasurableSet (box F w z rho sigma L) := by
  rw [AdaptedBoxVolume.box_eq_preimage]
  have hc : Continuous (AdaptedBoxVolume.residualCoordinates F w z) := by
    unfold AdaptedBoxVolume.residualCoordinates normalResidual tangentResidual
    fun_prop
  exact (isClosed_closedBall.measurableSet.prod
    (isClosed_closedBall.measurableSet.prod isClosed_closedBall.measurableSet)).preimage hc.measurable

variable {P T D : Type*} [DecidableEq P] [DecidableEq T]

/-- Native scalar original-CW concentration. The actual endpoint points,
 original fine-label ancestor image, both image fibers, full carrier saturation,
 common physical box, its convexity and its exact volume are all constructed.
 The remaining quantitative hypotheses are primitive ORIGINAL reference laws. -/
theorem scalar_original_CW_concentration
    (I : Finset (P × T)) (height : P → ℝ) (x : P → ℝ) (y offset : P → ℝ × ℝ)
    (baseU : T → ℝ) (baseV : T → ℝ × ℝ) (theta : T → Fin 3 → ℝ)
    (F : ℝ → ℝ →L[ℝ] ℝ × ℝ) (Z : Finset ℝ)
    (S : Finset (ℝ × T)) (hSV : S ⊆ vertices I height) (root : Core S)
    (Phi : P → Finset D) (fine : D → ℝ) (label : P → T → D) (realizer : P → D → T)
    (Tfull : Finset T) (tube : T → Set Space)
    {delta rho sigma q A B S₀ IncErr DirErr FineErr Lrho Cdir Lcarrier Kcarrier Kglobal
      KPhi Cang kappa CW : ℝ}
    (hd : 0 < delta) (hrho : 0 < rho) (hdscale : delta ≤ rho^2)
    (hscale : rho^2 ≤ sigma) (hσρ : sigma ≤ rho) (hrho1 : rho ≤ 1)
    (hq : 0 < q) (hqρ : q ≤ rho)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hS₀ : 0 ≤ S₀)
    (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr) (hFine : 0 ≤ FineErr)
    (hLrho : 0 ≤ Lrho) (hCdir : 0 < Cdir) (hLcarrier : 0 < Lcarrier)
    (hKcarrier : 0 ≤ Kcarrier) (hKPhi : 0 ≤ KPhi) (hCang : 0 ≤ Cang) (hCW : 0 ≤ CW)
    (hincU : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height x baseU (scalarSlope theta) p t‖ ≤ IncErr*delta)
    (hincV : ∀ p t, (p,t) ∈ I →
      ‖incidenceResidual height y baseV (normalSlope theta) p t‖ ≤ IncErr*delta)
    (hdir : ∀ p t, (p,t) ∈ I →
      ‖normalSlope theta t-offset p-F (height p) (scalarSlope theta t)‖ ≤ DirErr*delta)
    (hu : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ‖scalarSlope theta t‖ ≤ B)
    (hF : ∀ z ∈ Z, ‖F z‖ ≤ A)
    (hcluster : ∀ s ∈ Z, ∀ t ∈ Z, ‖F s-F t‖ ≤ S₀*sigma)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hbounded : ∀ z ∈ Z, |z| ≤ 1)
    (hdiam : ∀ s ∈ Z, ∀ t ∈ Z, |s-t| ≤ rho)
    (hlabel : ∀ p t, (p,t) ∈ I → label p t ∈ Phi p)
    (hlabelFit : ∀ p t, (p,t) ∈ I → ‖scalarSlope theta t-fine (label p t)‖ ≤ FineErr*delta)
    (hrealizer : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ d ∈ Phi p, (p,realizer p d) ∈ I)
    (hrealizerFit : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ d ∈ Phi p,
      ‖scalarSlope theta (realizer p d)-fine d‖ ≤ FineErr*delta)
    (hnear : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ d₀ ∈ Phi p,
      Lrho ≤ (((Phi p).filter (fun d => ‖fine d-fine d₀‖ ≤ rho)).card : ℝ))
    (hball : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ c : ℝ,
      (((Phi p).filter (fun d => ‖fine d-c‖ ≤ (1+FineErr)*sigma)).card : ℝ) ≤ Cdir)
    (hFineLower : (rho/delta)^kappa ≤ KPhi*Lrho)
    (hFineUpper : Cdir ≤ KPhi*Cang^kappa*(sigma/delta)^kappa)
    (hfull : ∀ p t, (p,t) ∈ I → t ∈ Tfull)
    (htube : ∀ t ∈ Tfull, tube t ⊆ graphTube baseU (scalarSlope theta) baseV (normalSlope theta) delta t)
    (hcarrier : ∀ t ∈ Tfull,
      Lcarrier ≤ ((Tfull.filter (fun s =>
        parameterAncestor (grid₁ sigma) (grid₂ sigma) baseU (scalarSlope theta) baseV (normalSlope theta) s=
        parameterAncestor (grid₁ sigma) (grid₂ sigma) baseU (scalarSlope theta) baseV (normalSlope theta) t)).card : ℝ))
    (hcarrierScale : sigma^3 ≤ Kcarrier*Lcarrier*delta^3)
    (hglobal : (Tfull.card : ℝ)*delta^3 ≤ Kglobal)
    (hCWlaw : OriginalConvexWolffLaw Tfull tube CW) :
    let C := comparisonConstant A B (max DirErr (2*IncErr)) S₀
    let L := ancestorDilation A IncErr DirErr FineErr
    ((OriginalWPhysicalGrowth.scalarCells I height x theta q rho S hSV root).card : ℝ)*rho*(rho/sigma)^kappa ≤
      (3*(6+2*IncErr)*(2*(C*L))^4*(Kcarrier*Kglobal))*(KPhi^2*Cang^kappa)*CW := by
  let u := scalarSlope theta
  let v := normalSlope theta
  let Err := max DirErr (2*IncErr)
  let C := comparisonConstant A B Err S₀
  let L := ancestorDilation A IncErr DirErr FineErr
  let ancestor := parameterAncestor (grid₁ sigma) (grid₂ sigma) baseU u baseV v
  let Boxes := coreBox I height x y u v F S hSV
  let RootBox := Boxes root rho sigma (C*L)
  have hσ : 0 < sigma := (sq_pos_of_pos hrho).trans_le hscale
  have hdσ : delta ≤ sigma := hdscale.trans hscale
  have hdρ : delta ≤ rho := hdσ.trans hσρ
  have hErr : 0 ≤ Err := hDir.trans (le_max_left _ _)
  have hC : 1 ≤ C := le_max_left _ _
  have hL2 : 2 ≤ L := le_max_left _ _
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hCLpos : 0 < C*L := mul_pos (by linarith) hLpos
  have hLx : 3+IncErr+2*(1+2*FineErr) ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hLn : (1+A)*(3+IncErr)+4*DirErr ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hrSpec := rep_spec I height S hSV root
  have hzRoot : root.val.1 ∈ Z := by
    simpa only [hrSpec.2] using hheight _ (Finset.mem_image_of_mem Prod.fst hrSpec.1)
  obtain ⟨Epoints,hpoints,hpointHeight,hgrid,_himages,hendpoint,hcoarse⟩ :=
    exists_scalar_original_endpoint_points I height x theta q rho sigma S hSV root hrho hscale
  let endpoint : P → Core S := fun p => if hp : p ∈ Epoints then Classical.choose (hendpoint p hp) else root
  have endpoint_spec : ∀ p ∈ Epoints,
      endpoint p ∈ oneStates I height (terminalGrid q theta) (scalarAngle q theta) S root ∧
      rep I height S hSV (endpoint p)=p ∧ (p,(endpoint p).val.2) ∈ I := by
    intro p hp
    simpa only [endpoint,dif_pos hp] using Classical.choose_spec (hendpoint p hp)
  let center : P → ℝ := fun p => fine (label p (endpoint p).val.2)
  have hrealizerE : ∀ p ∈ Epoints, ∀ d ∈ Phi p, (p,realizer p d) ∈ I :=
    fun p hp => hrealizer p (hpoints hp)
  have hpairs := NativeOriginalAncestorCounts.scalar_original_ancestor_count I Epoints height x baseU u baseV v
    Phi fine center rho realizer hσ hdσ hInc hFine hCdir.le (hbounded _ hzRoot) hpointHeight
    hincU hrealizerE
    (fun p hp d hdmem => by simpa only [norm_sub_rev] using hrealizerFit p (hpoints hp) d hdmem)
    (fun p hp => hnear p (hpoints hp) _ (hlabel p _ (endpoint_spec p hp).2.2))
    (fun p hp => hball p (hpoints hp)) hgrid
  have hstep : ∀ state g, g ∈ M I height (terminalGrid q theta) (scalarAngle q theta) S state →
      ∀ L₀, 1 ≤ L₀ →
      Boxes state rho sigma L₀ ⊆ Boxes (next I height (terminalGrid q theta) (scalarAngle q theta) S state g) rho sigma (C*L₀) ∧
      Boxes (next I height (terminalGrid q theta) (scalarAngle q theta) S state g) rho sigma L₀ ⊆ Boxes state rho sigma (C*L₀) := by
    intro state g hg L₀ hL₀
    exact constructed_successor_box_comparison I height (terminalGrid q theta) (scalarAngle q theta)
      x y offset baseU u baseV v F Z S hSV hA hB hS₀ hErr hd.le hdσ hσρ hrho1
      (le_max_right _ _) (le_max_left _ _) hincU hincV hdir hu hF hcluster hheight hdiam
      (fun s t heq => (scalar_terminal_grid_gap q hq theta s t heq).trans hqρ)
      state g hg L₀ hL₀
  have hcontains : ∀ p ∈ Epoints, ∀ d ∈ nearDirections Phi fine center rho p,
      ∀ t ∈ Tfull, ancestor t=ancestor (realizer p d) → tube t ⊆ RootBox := by
    intro p hp d hdnear t ht heq
    have hspec := endpoint_spec p hp
    have hdPhi := (Finset.mem_filter.mp hdnear).1
    have hR := hrealizerE p hp d hdPhi
    have hstateZ := one_state_height I height (terminalGrid q theta) (scalarAngle q theta) S root (endpoint p) hspec.1
    have hgap := scalar_parameter_ancestor_gaps baseU u baseV v hσ t (realizer p d) heq
    have htangent : ‖u (realizer p d)-u (endpoint p).val.2‖ ≤ (1+2*FineErr)*rho :=
      fine_label_realizer_tangent_gap _ _ _ _ hdρ hFine
        (hlabelFit p _ hspec.2.2) (hrealizerFit p (hpoints hp) d hdPhi) (Finset.mem_filter.mp hdnear).2
    have hsaturate := ancestor_fiber_inside_adapted_box baseU u baseV v (F root.val.1)
      (x p) (y p) (offset p) root.val.1 (endpoint p).val.2 (realizer p d) t
      hd.le hdσ hσρ hA hInc hDir (hF _ hzRoot) (hbounded _ hzRoot)
      (by simpa only [incidenceResidual,hpointHeight p hp] using hincU p _ hR)
      (by simpa only [incidenceResidual,hpointHeight p hp] using hincV p _ hR)
      (by simpa only [hpointHeight p hp] using hdir p _ hspec.2.2)
      (by simpa only [hpointHeight p hp] using hdir p _ hR)
      htangent hgap.1 hgap.2.1 hgap.2.2.1 hgap.2.2.2 hL2 hLx hLn
    have htoEndpoint : tube t ⊆ Boxes (endpoint p) rho sigma L := by
      apply (htube t ht).trans
      simpa only [Boxes,coreBox,terminalWalk,box,tangentResidual,normalResidual,
        hspec.2.1,hstateZ] using hsaturate
    have hpath := OriginalCoreBoxPaths.oneStates_box_comparison I height (terminalGrid q theta)
      (scalarAngle q theta) S (fun state L₀ => Boxes state rho sigma L₀) C hC
      (fun state L₁ L₂ hle => OriginalCoreBoxPaths.coreBox_mono I height x y u v F S hSV state
        rho sigma L₁ L₂ hrho.le hσ.le hle) hstep root (endpoint p) hspec.1 L hL1
    exact htoEndpoint.trans hpath.2
  have hconvex : Convex ℝ RootBox := AdaptedBoxVolume.convex_box _ _ _ _ _ _
  have hmeas : MeasurableSet RootBox := adapted_box_measurable _ _ _ _ _ _
  have hvolume : volume RootBox=ENNReal.ofReal ((2*(C*L))^4*rho*sigma^2) :=
    AdaptedBoxVolume.volume_box_a1 _ _ _ rho sigma (C*L) hrho.le hσ.le hCLpos.le
  have hCWboxE := hCWlaw RootBox hconvex hmeas
  rw [hvolume] at hCWboxE
  have hCWbox : ((Tfull.filter (fun t => tube t ⊆ RootBox)).card : ℝ) ≤
      CW*((2*(C*L))^4*rho*sigma^2)*Tfull.card := by
    have hreal := ENNReal.toReal_mono (by finiteness) hCWboxE
    simpa only [ENNReal.toReal_natCast,ENNReal.toReal_mul,ENNReal.toReal_ofReal hCW,
      ENNReal.toReal_ofReal (show 0 ≤ (2*(C*L))^4*rho*sigma^2 by positivity)] using hreal
  have hancCount := OriginalCarrierImageCount.original_realizer_carrier_CW_count Epoints Phi fine center rho
    ancestor realizer Tfull tube RootBox
    (fun p hp d hdmem => hfull p _ (hrealizerE p hp d hdmem)) hcarrier hcontains hCWbox
  have hnormalize := OriginalCWScaleCancellation.carrier_global_normalization
    (show (0:ℝ) ≤ Tfull.card by positivity) hKcarrier hLcarrier.le hglobal hcarrierScale
  have hcount := OriginalCWScaleCancellation.original_count_scale_cancellation 1 2 (by norm_num)
    hrho hσ.le hLrho hLcarrier (show 0 ≤ 6+2*IncErr by positivity) hCdir.le
    (show 0 ≤ (2*(C*L))^4 by positivity) hCW
    (by simpa only [pow_one] using hcoarse) hpairs
    (by simpa only [pow_one] using hancCount) hnormalize
  have hratio := OriginalCWScaleCancellation.original_fine_AD_ratio hrho hσ hd hKPhi hCang hFineLower hFineUpper
  have hfinal := OriginalCWScaleCancellation.original_CW_ratio_lower 1
    (show (0:ℝ) ≤ (OriginalWPhysicalGrowth.scalarCells I height x theta q rho S hSV root).card by positivity)
    hrho.le hCdir (show 0 ≤ KPhi^2*Cang^kappa by positivity)
    (show ((OriginalWPhysicalGrowth.scalarCells I height x theta q rho S hSV root).card : ℝ)*rho^1*Lrho ≤
      (3*(6+2*IncErr)*(2*(C*L))^4*(Kcarrier*Kglobal))*Cdir*CW by convert hcount using 1; ring) hratio
  simpa only [pow_one] using hfinal

end NativeOriginalScalarCW
