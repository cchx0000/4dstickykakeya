import Theorems.Thm_StickyKakeya4_original_height_vertex_density
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
namespace OriginalIncidenceHeightPopulation
open Classical OriginalHeightVertexDensity OriginalScalarCollisionMass OriginalWCoarseEscapeMenus
variable {P T H : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
/-- Every original height/tube vertex uses an original height and tube. -/
theorem original_vertices_subset_product (I : Finset (P × T)) (height : P → H) (Z : Finset H)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z) :
    vertices I height ⊆ Z ×ˢ TwoTubePathCollisionCount.tubes I := by
  rw [vertices_eq_original_incidence_image]
  intro v hv
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
  apply Finset.mem_product.mpr
  exact ⟨hheight e.1 (Finset.mem_image_of_mem Prod.fst he),Finset.mem_image_of_mem Prod.snd he⟩
/-- Original incidence occupancy and height labels control total incidence
 mass by the SAME actual height and tube populations. -/
theorem original_incidence_height_product (I : Finset (P × T)) (height : P → H) (Z : Finset H)
    {C : ℝ} (hC : 0 ≤ C)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((OriginalWWitnessCounts.pointsAt I height t z).card:ℝ) ≤ C) :
    (I.card:ℝ) ≤ C*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card := by
  have hh := incidences_le_height_vertices I height hC hpoints
  have hv : ((vertices I height).card:ℝ) ≤ (Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card := by
    have hc := Finset.card_le_card (original_vertices_subset_product I height Z hheight)
    rw [Finset.card_product] at hc
    exact_mod_cast hc
  calc
    _ ≤ C*(vertices I height).card := hh
    _ ≤ C*((Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card) := mul_le_mul_of_nonneg_left hv hC
    _ = _ := by ring
/-- A retained original incidence density supplies the absolute fine-height
 mass for the B constructor. No separate height-population certificate is used. -/
theorem original_fine_height_mass (I : Finset (P × T)) (height : P → H) (Z : Finset H)
    (hI : I.Nonempty) {delta C rho incidenceDensity : ℝ} (hd : 0 ≤ delta) (hC : 0 < C)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((OriginalWWitnessCounts.pointsAt I height t z).card:ℝ) ≤ C)
    (hIncidence : incidenceDensity*rho*(TwoTubePathCollisionCount.tubes I).card ≤ delta*(I.card:ℝ)) :
    (incidenceDensity/C)*rho ≤ delta*(Z.card:ℝ) := by
  have hT : (0:ℝ)<(TwoTubePathCollisionCount.tubes I).card := by
    apply Nat.cast_pos.mpr
    apply Finset.Nonempty.card_pos
    exact hI.image Prod.snd
  have hc := mul_le_mul_of_nonneg_left (original_incidence_height_product I height Z hC.le hheight hpoints) hd
  have hh : incidenceDensity*rho ≤ delta*C*(Z.card:ℝ) := by
    apply (mul_le_mul_iff_left₀ hT).mp
    calc
      _ ≤ delta*(I.card:ℝ) := hIncidence
      _ ≤ _ := by nlinarith only [hc]
  have hdiv : (incidenceDensity*rho)/C ≤ delta*(Z.card:ℝ) :=
    (div_le_iff₀ hC).mpr (by nlinarith only [hh])
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hdiv
/-- For a working height interval of radius at most one, the global retained
 source density gives the required scale-relative original height mass. -/
theorem original_fine_height_mass_of_global_density
    (I : Finset (P × T)) (height : P → H) (Z : Finset H) (hI : I.Nonempty)
    {delta C rho incidenceDensity : ℝ} (hd : 0 ≤ delta) (hC : 0 < C)
    (hDensity : 0 ≤ incidenceDensity) (hrho : rho ≤ 1)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((OriginalWWitnessCounts.pointsAt I height t z).card:ℝ) ≤ C)
    (hIncidence : incidenceDensity*(TwoTubePathCollisionCount.tubes I).card ≤ delta*(I.card:ℝ)) :
    (incidenceDensity/C)*rho ≤ delta*(Z.card:ℝ) := by
  apply original_fine_height_mass I height Z hI hd hC hheight hpoints
  calc
    _ ≤ incidenceDensity*(TwoTubePathCollisionCount.tubes I).card := by
      have hh := mul_le_mul_of_nonneg_right hrho
        (mul_nonneg hDensity (Nat.cast_nonneg (TwoTubePathCollisionCount.tubes I).card))
      nlinarith only [hh]
    _ ≤ _ := hIncidence
end OriginalIncidenceHeightPopulation
