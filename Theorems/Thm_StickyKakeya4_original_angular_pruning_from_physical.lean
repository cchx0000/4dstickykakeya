import Theorems.Thm_StickyKakeya4_original_angular_class_population
import Theorems.Thm_StickyKakeya4_original_annular_graph_deletion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

noncomputable section
namespace OriginalAngularPruningFromPhysical
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open OriginalAngularClassPopulation OriginalAnnularGraphDeletion PlanarFrostmanBallConversion

/-- Reversal preserves the actual original pair law and physical tube;
no symmetry of the original graph is assumed. -/
theorem original_reverse_class_population (P : Finset Point) (G : Finset Pair)
    {rho tau m : ℝ} (hrho : 0<rho) (htau : 0<tau) (htau1 : tau≤1) (hm : 0≤m)
    (hG : G ⊆ P.product P) (hne : ∀ z∈G, z.1≠z.2)
    (hmass : ∀ z∈G, m≤(((physicalPairTube P rho z).filter
      (fun v => tau≤euclideanDistance z.2 v)).card : ℝ)) :
    m*((G.image (reverseClass rho)).card : ℝ) ≤100/tau*(P.card : ℝ)^2 := by
  let Gs := G.image Prod.swap
  have hGs : Gs ⊆ P.product P := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    have hp := Finset.mem_product.mp (hG hw)
    exact Finset.mem_product.mpr ⟨hp.2,hp.1⟩
  have hns : ∀ z∈Gs, z.1≠z.2 := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact (hne w hw).symm
  have hms : ∀ z∈Gs, m≤(((physicalPairTube P rho z).filter
      (fun v => tau≤euclideanDistance z.1 v)).card : ℝ) := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    simpa only [physical_pair_tube_swap,Prod.fst_swap] using hmass w hw
  have hh := original_forward_class_population P Gs hrho htau htau1 hm hGs hns hms
  have heq : Gs.image (forwardClass rho)=G.image (reverseClass rho) := by
    simp only [Gs,Finset.image_image]
    rfl
  simpa only [heq] using hh

/-- Native Step3 pruning with its class budget derived from ORIGINAL
physical far mass. The density classes on BOTH sides concern this same H. -/
theorem exists_original_angular_core (P : Finset Point) (G : Finset Pair)
    {rho tau m : ℝ} (hrho : 0<rho) (htau : 0<tau) (htau1 : tau≤1) (hm : 0≤m)
    (hG : G ⊆ P.product P) (hne : ∀ z∈G, z.1≠z.2)
    (hmass : ∀ z∈G,
      m≤(((physicalPairTube P rho z).filter (fun v => tau≤euclideanDistance z.1 v)).card : ℝ) ∧
      m≤(((physicalPairTube P rho z).filter (fun v => tau≤euclideanDistance z.2 v)).card : ℝ)) :
    ∃ H : Finset Pair, H⊆G ∧ (G.card : ℝ)≤H.card+400*tau*(P.card : ℝ)^2 ∧
      ∀ z∈H,
        2*tau^2*m≤((H.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
        2*tau^2*m≤((H.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ) := by
  have hf := original_forward_class_population P G hrho htau htau1 hm hG hne
    (fun z hz => (hmass z hz).1)
  have hr := original_reverse_class_population P G hrho htau htau1 hm hG hne
    (fun z hz => (hmass z hz).2)
  let k := tau^2*m
  obtain ⟨H,hHG,hsize,hdegree⟩ := exists_original_radial_class_core G rho k
    (mul_nonneg (sq_nonneg _) hm)
  have hsum : m*(((G.image (forwardClass rho)).card : ℝ)+
      (G.image (reverseClass rho)).card)≤200/tau*(P.card : ℝ)^2 := by
    calc
      _ = m*((G.image (forwardClass rho)).card : ℝ)+
          m*((G.image (reverseClass rho)).card : ℝ) := by ring
      _ ≤ 100/tau*(P.card : ℝ)^2+100/tau*(P.card : ℝ)^2 := add_le_add hf hr
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hsum (show 0≤2*tau^2 by positivity)
  have heq : 2*tau^2*(200/tau*(P.card : ℝ)^2)=400*tau*(P.card : ℝ)^2 := by
    field_simp
    ring
  rw [heq] at hscaled
  have hcharge : 2*k*(((G.image (forwardClass rho)).card : ℝ)+
      (G.image (reverseClass rho)).card)≤400*tau*(P.card : ℝ)^2 := by
    calc
      _ = 2*tau^2*(m*(((G.image (forwardClass rho)).card : ℝ)+
          (G.image (reverseClass rho)).card)) := by dsimp [k]; ring
      _ ≤ _ := hscaled
  refine ⟨H,hHG,(by linarith only [hsize,hcharge]),?_⟩
  intro z hz
  simpa only [k,mul_assoc] using hdegree z hz

end OriginalAngularPruningFromPhysical
