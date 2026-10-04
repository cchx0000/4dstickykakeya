import Theorems.Thm_StickyKakeya4_original_annular_graph_deletion
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open scoped BigOperators
noncomputable section
namespace OriginalAnnularOffRootMass
open OriginalPairStripGeometry OriginalPhysicalPairTube PlanarFrostmanBallConversion
open OriginalPhysicalTubeScaleSelection OriginalDensestTubeControl OriginalAnnularRowCover
open OriginalAnnularGraphDeletion

def annularScales (n : ℕ) (rho tau0 : ℝ) : Finset ℝ := by
  classical
  exact (scaleMenu n).filter (fun tau => rho≤tau ∧ tau≤tau0)

theorem annular_scales_card (n : ℕ) (rho tau0 : ℝ) :
    (annularScales n rho tau0).card≤n+1 := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (Finset.card_image_le.trans (by simp only [Finset.card_range]; rfl))

/-- The literal finite dyadic menu covers each original distance between
the selected tube width and the chosen endpoint exclusion radius. -/
theorem original_distance_annulus_cover (n : ℕ) (rho tau0 d : ℝ)
    (hrho : rho∈scaleMenu n) (hdrho : rho≤d) (hdtop : d≤tau0) (htop : tau0≤1) :
    ∃ tau∈annularScales n rho tau0, tau≤d ∧ d≤2*tau := by
  classical
  have hb := (scale_menu_bounds n).2.2 rho hrho
  obtain ⟨j,hjn,hjlo,hjhi⟩ := dyadic_radius_cover n (d/2)
    (by linarith only [hb.2.1,hdrho]) (by linarith only [hdtop,htop])
  have hjmem : dyadicRadius j∈scaleMenu n :=
    Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),rfl⟩
  let tau := max rho (dyadicRadius j)
  have htaumem : tau∈scaleMenu n := by
    rcases max_cases rho (dyadicRadius j) with h|h
    · simpa only [tau,h.1] using hrho
    · simpa only [tau,h.1] using hjmem
  have htaud : tau≤d := max_le hdrho (by linarith only [hjhi])
  exact ⟨tau,Finset.mem_filter.mpr ⟨htaumem,le_max_left _ _,htaud.trans hdtop⟩,
    htaud,by have hh := le_max_right rho (dyadicRadius j); dsimp only [tau]; linarith only [hjlo,hh]⟩

/-- Every endpoint-near original point is charged either to the innermost
original Frostman ball or to an actual dyadic annular support. -/
theorem original_near_root_card
    (Pts : Finset Point) (p q : Point) (n : ℕ) (rho tau0 w B A : ℝ)
    (hrho : rho∈scaleMenu n) (htop : tau0≤1)
    (hball : ((Pts.filter (fun v => euclideanDistance p v≤rho)).card : ℝ)≤B)
    (hA : 0≤A)
    (hann : ∀ tau∈annularScales n rho tau0,
      ((annularSupport Pts p q w tau).card : ℝ)≤A) :
    (((physicalPairTube Pts w (p,q)).filter
      (fun v => euclideanDistance p v≤tau0)).card : ℝ)≤B+(n+1:ℕ)*A := by
  classical
  let Ball := Pts.filter (fun v => euclideanDistance p v≤rho)
  let Ann := (annularScales n rho tau0).biUnion (annularSupport Pts p q w)
  have hcover : (physicalPairTube Pts w (p,q)).filter
      (fun v => euclideanDistance p v≤tau0)⊆Ball∪Ann := by
    intro v hv
    obtain ⟨hvT,hvnear⟩ := Finset.mem_filter.mp hv
    by_cases hlow : euclideanDistance p v≤rho
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hvT).1,hlow⟩))
    · obtain ⟨tau,htau,hlo,hhi⟩ := original_distance_annulus_cover n rho tau0
        (euclideanDistance p v) hrho (le_of_not_ge hlow) hvnear htop
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨tau,htau,Finset.mem_filter.mpr ⟨hvT,hlo,hhi⟩⟩))
  have hAnn : (Ann.card : ℝ)≤(n+1:ℕ)*A := by
    calc
      _ ≤ ∑ tau∈annularScales n rho tau0, ((annularSupport Pts p q w tau).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : Ann.card≤_)
      _ ≤ ∑ _tau∈annularScales n rho tau0, A := Finset.sum_le_sum hann
      _ = ((annularScales n rho tau0).card : ℝ)*A := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (annular_scales_card n rho tau0)) hA
  have hc : ((((physicalPairTube Pts w (p,q)).filter
      (fun v => euclideanDistance p v≤tau0)).card : ℝ))≤Ball.card+Ann.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le Ball Ann)
  linarith only [hc,hball,hAnn]

end OriginalAnnularOffRootMass
