import Theorems.Thm_StickyKakeya4_original_ancestor_fiber_geometry
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalAncestorCounts
open Classical OriginalAncestorCounting OriginalAncestorFiberGeometry
open OriginalTubeAncestorSaturation OriginalWPhysicalDisplacement

variable {P T D : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq D]

omit [DecidableEq T] [DecidableEq D] in
/-- Native scalar point/fine-label to original ancestor count. Every fiber
 estimate is derived from the unchanged original incidences, fine-point ball
 law, and literal six-coordinate tube parameter ancestor. -/
theorem scalar_original_ancestor_count
    (I : Finset (P × T)) (E : Finset P) (height : P → ℝ) (x : P → ℝ)
    (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ)
    (Phi : P → Finset D) (fine : D → ℝ) (center : P → ℝ)
    (rho : ℝ) (realizer : P → D → T)
    {delta sigma IncErr FineErr z Lrho Cdir : ℝ}
    (hsigma : 0 < sigma) (hd : delta ≤ sigma)
    (hInc : 0 ≤ IncErr) (hFine : 0 ≤ FineErr) (hCdir : 0 ≤ Cdir)
    (hz : |z| ≤ 1) (hheight : ∀ p ∈ E, height p=z)
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hrealizer : ∀ p ∈ E, ∀ d ∈ Phi p, (p,realizer p d) ∈ I)
    (hfit : ∀ p ∈ E, ∀ d ∈ Phi p, ‖fine d-u (realizer p d)‖ ≤ FineErr*delta)
    (hlower : ∀ p ∈ E, Lrho ≤ ((nearDirections Phi fine center rho p).card : ℝ))
    (hball : ∀ p ∈ E, ∀ c : ℝ,
      (((Phi p).filter (fun d => ‖fine d-c‖ ≤ (1+FineErr)*sigma)).card : ℝ) ≤ Cdir)
    (hgrid : Set.InjOn (fun p => ⌊x p/sigma⌋) (↑E)) :
    let ancestor := parameterAncestor (grid₁ sigma) (grid₂ sigma) baseU u baseV v
    (E.card : ℝ)*Lrho ≤
      ((occupiedAncestors E Phi fine center rho ancestor realizer).card : ℝ)*((6+2*IncErr)*Cdir) := by
  let ancestor := parameterAncestor (grid₁ sigma) (grid₂ sigma) baseU u baseV v
  have hparam : ∀ s t, ancestor s=ancestor t →
      ‖baseU s-baseU t‖ ≤ sigma ∧ ‖u s-u t‖ ≤ sigma := by
    intro s t heq
    have h := scalar_parameter_ancestor_gaps baseU u baseV v hsigma s t heq
    exact ⟨h.1,h.2.2.1⟩
  apply original_pair_ancestor_count E Phi fine center rho ancestor realizer hCdir hlower
  · intro k hk
    obtain ⟨p₀,_hp₀,d₀,_hd₀,href⟩ := occupied_ancestor_has_original_realizer E Phi fine center rho ancestor realizer hk
    let ref := realizer p₀ d₀
    let S := activePoints E Phi fine center rho ancestor realizer k
    have hgridS : Set.InjOn (fun p => ⌊x p/sigma⌋) (↑S) := by
      intro p hp q hq heq
      exact hgrid (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 heq
    have hnear : ∀ p ∈ S, ‖x p-(baseU ref+z • u ref)‖ ≤ (2+IncErr)*sigma := by
      intro p hp
      exact active_points_in_ancestor_ball I E height x baseU u Phi fine center rho ancestor realizer
        hd hInc hz hheight hinc hrealizer hparam k ref href p hp
    have hc := NativeTangentGridCoarsening.scalar_injective_grid_centered_card S x hsigma
      (show 0 ≤ 2+IncErr by positivity) hgridS hnear
    simpa only [show 2*(2+IncErr)+2=6+2*IncErr by ring] using hc
  · intro p hp k hk
    exact original_direction_fiber_bound E Phi fine center rho ancestor realizer u hd hFine hfit
      (fun s t heq => (hparam s t heq).2) hball p hp k hk

omit [DecidableEq T] [DecidableEq D] in
/-- Native planar point/fine-label to original ancestor count. Every fiber
 estimate is derived from the unchanged original incidences, fine-point ball
 law, and literal six-coordinate tube parameter ancestor. -/
theorem planar_original_ancestor_count
    (I : Finset (P × T)) (E : Finset P) (height : P → ℝ) (x : P → ℝ × ℝ)
    (baseU u : T → ℝ × ℝ) (baseV v : T → ℝ)
    (Phi : P → Finset D) (fine : D → ℝ × ℝ) (center : P → ℝ × ℝ)
    (rho : ℝ) (realizer : P → D → T)
    {delta sigma IncErr FineErr z Lrho Cdir : ℝ}
    (hsigma : 0 < sigma) (hd : delta ≤ sigma)
    (hInc : 0 ≤ IncErr) (hFine : 0 ≤ FineErr) (hCdir : 0 ≤ Cdir)
    (hz : |z| ≤ 1) (hheight : ∀ p ∈ E, height p=z)
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x baseU u p t‖ ≤ IncErr*delta)
    (hrealizer : ∀ p ∈ E, ∀ d ∈ Phi p, (p,realizer p d) ∈ I)
    (hfit : ∀ p ∈ E, ∀ d ∈ Phi p, ‖fine d-u (realizer p d)‖ ≤ FineErr*delta)
    (hlower : ∀ p ∈ E, Lrho ≤ ((nearDirections Phi fine center rho p).card : ℝ))
    (hball : ∀ p ∈ E, ∀ c : ℝ × ℝ,
      (((Phi p).filter (fun d => ‖fine d-c‖ ≤ (1+FineErr)*sigma)).card : ℝ) ≤ Cdir)
    (hgrid : Set.InjOn (fun p => (⌊(x p).1/sigma⌋,⌊(x p).2/sigma⌋)) (↑E)) :
    let ancestor := parameterAncestor (grid₂ sigma) (grid₁ sigma) baseU u baseV v
    (E.card : ℝ)*Lrho ≤
      ((occupiedAncestors E Phi fine center rho ancestor realizer).card : ℝ)*((6+2*IncErr)^2*Cdir) := by
  let ancestor := parameterAncestor (grid₂ sigma) (grid₁ sigma) baseU u baseV v
  have hparam : ∀ s t, ancestor s=ancestor t →
      ‖baseU s-baseU t‖ ≤ sigma ∧ ‖u s-u t‖ ≤ sigma := by
    intro s t heq
    have h := planar_parameter_ancestor_gaps baseU u baseV v hsigma s t heq
    exact ⟨h.1,h.2.2.1⟩
  apply original_pair_ancestor_count E Phi fine center rho ancestor realizer hCdir hlower
  · intro k hk
    obtain ⟨p₀,_hp₀,d₀,_hd₀,href⟩ := occupied_ancestor_has_original_realizer E Phi fine center rho ancestor realizer hk
    let ref := realizer p₀ d₀
    let S := activePoints E Phi fine center rho ancestor realizer k
    have hgridS : Set.InjOn (fun p => (⌊(x p).1/sigma⌋,⌊(x p).2/sigma⌋)) (↑S) := by
      intro p hp q hq heq
      exact hgrid (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 heq
    have hnear : ∀ p ∈ S, ‖x p-(baseU ref+z • u ref)‖ ≤ (2+IncErr)*sigma := by
      intro p hp
      exact active_points_in_ancestor_ball I E height x baseU u Phi fine center rho ancestor realizer
        hd hInc hz hheight hinc hrealizer hparam k ref href p hp
    have hcoords : ∀ p ∈ S,
        |(x p).1-(baseU ref+z • u ref).1| ≤ (2+IncErr)*sigma ∧
        |(x p).2-(baseU ref+z • u ref).2| ≤ (2+IncErr)*sigma := by
      intro p hp
      exact max_le_iff.mp (hnear p hp)
    have hc := NativeTangentGridCoarsening.planar_injective_grid_centered_card S x
      (baseU ref+z • u ref) hsigma (show 0 ≤ 2+IncErr by positivity) hgridS hcoords
    simpa only [show 2*(2+IncErr)+2=6+2*IncErr by ring] using hc
  · intro p hp k hk
    exact original_direction_fiber_bound E Phi fine center rho ancestor realizer u hd hFine hfit
      (fun s t heq => (hparam s t heq).2) hball p hp k hk

end NativeOriginalAncestorCounts
