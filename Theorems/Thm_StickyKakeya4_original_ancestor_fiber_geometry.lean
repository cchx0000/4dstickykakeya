import Theorems.Thm_StickyKakeya4_original_ancestor_counting

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalAncestorFiberGeometry
open Classical OriginalAncestorCounting OriginalTubeAncestorSaturation
open OriginalWPhysicalDisplacement

variable {P T K D U : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]
  [DecidableEq D] [NormedAddCommGroup U] [NormedSpace ℝ U]

omit [DecidableEq P] [DecidableEq T] [DecidableEq D] [NormedSpace ℝ U] in
/-- An occupied ancestor has an original point/fine-label realizer. -/
lemma occupied_ancestor_has_original_realizer
    (E : Finset P) (Phi : P → Finset D) (fine : D → U) (center : P → U)
    (rho : ℝ) (ancestor : T → K) (realizer : P → D → T) {k : K}
    (hk : k ∈ occupiedAncestors E Phi fine center rho ancestor realizer) :
    ∃ p ∈ E, ∃ d ∈ nearDirections Phi fine center rho p, ancestor (realizer p d)=k := by
  obtain ⟨w,hw,hk⟩ := Finset.mem_image.mp hk
  obtain ⟨hp,hd⟩ := Finset.mem_sigma.mp hw
  exact ⟨w.1,hp,w.2,hd,hk⟩

omit [DecidableEq P] [DecidableEq T] [DecidableEq D] [NormedSpace ℝ U] in
/-- Derive the fine-direction fiber bound at each original point from its
 ORIGINAL fine-set ball law and original realization error. -/
theorem original_direction_fiber_bound
    (E : Finset P) (Phi : P → Finset D) (fine : D → U) (center : P → U)
    (rho : ℝ) (ancestor : T → K) (realizer : P → D → T) (u : T → U)
    {delta sigma Error Cdir : ℝ} (hd : delta ≤ sigma) (hE : 0 ≤ Error)
    (hfit : ∀ p ∈ E, ∀ d ∈ Phi p, ‖fine d-u (realizer p d)‖ ≤ Error*delta)
    (hparam : ∀ s t, ancestor s=ancestor t → ‖u s-u t‖ ≤ sigma)
    (hball : ∀ p ∈ E, ∀ c : U,
      (((Phi p).filter (fun d => ‖fine d-c‖ ≤ (1+Error)*sigma)).card : ℝ) ≤ Cdir)
    (p : P) (hp : p ∈ E) (k : K)
    (hk : k ∈ occupiedAncestors E Phi fine center rho ancestor realizer) :
    (((nearDirections Phi fine center rho p).filter (fun d => ancestor (realizer p d)=k)).card : ℝ) ≤ Cdir := by
  obtain ⟨p₀,_hp₀,d₀,_hd₀,href⟩ := occupied_ancestor_has_original_realizer E Phi fine center rho ancestor realizer hk
  let t₀ := realizer p₀ d₀
  have hsub : (nearDirections Phi fine center rho p).filter (fun d => ancestor (realizer p d)=k) ⊆
      (Phi p).filter (fun d => ‖fine d-u t₀‖ ≤ (1+Error)*sigma) := by
    intro d hdmem
    obtain ⟨hdnear,hdk⟩ := Finset.mem_filter.mp hdmem
    have hdPhi := (Finset.mem_filter.mp hdnear).1
    refine Finset.mem_filter.mpr ⟨hdPhi,?_⟩
    exact fine_label_in_ancestor_ball (fine d) (u (realizer p d)) (u t₀) hd hE (hfit p hp d hdPhi)
      (hparam _ _ (hdk.trans href.symm))
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hball p hp (u t₀))

omit [DecidableEq P] [DecidableEq T] [DecidableEq D] in
/-- At one original terminal height, all actual endpoint realizers belonging
 to an ancestor lie in its explicit tangent ball. The bound is derived from
 graph incidence and original parameter-cell diameter. -/
theorem active_points_in_ancestor_ball
    (I : Finset (P × T)) (E : Finset P) (height : P → ℝ) (x : P → U)
    (base u : T → U) (Phi : P → Finset D) (fine : D → U) (center : P → U)
    (rho : ℝ) (ancestor : T → K) (realizer : P → D → T)
    {delta sigma Error z : ℝ} (hd : delta ≤ sigma) (hE : 0 ≤ Error) (hz : |z| ≤ 1)
    (hheight : ∀ p ∈ E, height p=z)
    (hinc : ∀ p t, (p,t) ∈ I → ‖incidenceResidual height x base u p t‖ ≤ Error*delta)
    (hrealizer : ∀ p ∈ E, ∀ d ∈ Phi p, (p,realizer p d) ∈ I)
    (hparam : ∀ s t, ancestor s=ancestor t → ‖base s-base t‖ ≤ sigma ∧ ‖u s-u t‖ ≤ sigma)
    (k : K) (reference : T) (href : ancestor reference=k)
    (p : P) (hp : p ∈ activePoints E Phi fine center rho ancestor realizer k) :
    ‖x p-(base reference+z • u reference)‖ ≤ (2+Error)*sigma := by
  obtain ⟨hpE,d,hdnear,hdk⟩ := Finset.mem_filter.mp hp
  have hdPhi := (Finset.mem_filter.mp hdnear).1
  have hi := hinc p (realizer p d) (hrealizer p hpE d hdPhi)
  have hgap := hparam _ _ (hdk.trans href.symm)
  apply same_ancestor_fixed_height_ball (x p) (base (realizer p d)) (base reference)
    (u (realizer p d)) (u reference) hz hd hE
  · simpa only [incidenceResidual,hheight p hpE] using hi
  · exact hgap.1
  · exact hgap.2

end OriginalAncestorFiberGeometry
