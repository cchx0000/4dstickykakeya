import Theorems.Thm_StickyKakeya4_native_dyadic_coarse_normalization
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeCoarseBackboneDensity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentPhysicalData NativeCoarseOriginalIncidences
open NativeSourceCoarseReadback
/-- The actual incidence tubes lie in the full original parent backbone.
 The full backbone is retained as a separate carrier for the tube AD law. -/
theorem incidence_tubes_subset_backbone {n : ℕ} (D : FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ) (p : Parent)
    (E : Finset (Fin n × ShearBinFibers.Index)) (hE : E ⊆ (data D cells a N p).incidences) :
    TwoTubePathCollisionCount.tubes (NativeCoarseOriginalIncidences.incidences (data D cells a N p) E) ⊆
      backbone D a N p := by
  have hread : TwoTubePathCollisionCount.tubes
      (NativeCoarseOriginalIncidences.incidences (data D cells a N p) E)=E.image Prod.fst := by
    simp only [TwoTubePathCollisionCount.tubes,NativeCoarseOriginalIncidences.incidences,image_image]
    ext i
    simp only [mem_image,Function.comp_apply,NativeCoarseOriginalIncidences.label]
  rw [hread]
  intro t ht
  obtain ⟨⟨i,c⟩,hz,he⟩ := mem_image.mp ht
  change i=t at he
  subst t
  obtain ⟨k,_hk,hpar,_hchart⟩ := (mem_data_incidences D cells a N p i c).mp (hE hz)
  exact mem_filter.mpr ⟨mem_univ _,hpar⟩
/-- Average incidence density survives relative to the FULL original parent
 backbone, using the actual retained incidence factor and true bin capacity.
 This statement does not assert per-tube shading density. -/
theorem full_backbone_coarse_density {n : ℕ} (D : FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ) (p : Parent) (hp : p ∈ parents D a N)
    (hP : (data D cells a N p).Hypotheses) (E : Finset (Fin n × ShearBinFibers.Index))
    (hE : E ⊆ (data D cells a N p).incidences) (F : ℕ) (hF : 0 < F)
    {lambda R : ℝ} (hR : 0 < R) (hlam : lambda ≤ (data D cells a N p).lam)
    (hret : (data D cells a N p).incidences.card ≤ F*E.card) :
    (lambda/((F:ℝ)*R))*(backbone D a N p).card ≤
      ((data D cells a N p).σ/R)*
        (NativeCoarseOriginalIncidences.incidences (data D cells a N p) E).card := by
  let P := data D cells a N p
  let I := NativeCoarseOriginalIncidences.incidences P E
  have hFr : (0:ℝ)<F := Nat.cast_pos.mpr hF
  have hretR : (P.incidences.card:ℝ) ≤ (F:ℝ)*(E.card:ℝ) := by exact_mod_cast hret
  have hcap : (E.card:ℝ) ≤ (P.N:ℝ)*(I.card:ℝ) := by
    exact_mod_cast actual_capacity P hP E hE
  have hden : lambda*(backbone D a N p).card ≤ (F:ℝ)*P.σ*(I.card:ℝ) := by
    calc
      _ ≤ P.lam*(backbone D a N p).card := mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg _)
      _ ≤ P.δ*(P.incidences.card:ℝ) := full_backbone_density D cells a N p hp
      _ ≤ P.δ*((F:ℝ)*(E.card:ℝ)) := mul_le_mul_of_nonneg_left hretR hP.delta_pos.le
      _ ≤ P.δ*((F:ℝ)*((P.N:ℝ)*(I.card:ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcap hFr.le) hP.delta_pos.le
      _ = _ := by unfold PhysicalRescalingIncidenceTransfer.Data.σ; ring
  calc
    _ = (lambda*(backbone D a N p).card)/((F:ℝ)*R) := by ring
    _ ≤ ((F:ℝ)*P.σ*(I.card:ℝ))/((F:ℝ)*R) :=
      div_le_div_of_nonneg_right hden (mul_pos hFr hR).le
    _ = _ := by
      change ((F:ℝ)*P.σ*(I.card:ℝ))/((F:ℝ)*R)=(P.σ/R)*(I.card:ℝ)
      field_simp
/-- The same full-backbone average bound is stated on the literal image of
 the SAME original cubical incidence subset E0. -/
theorem original_full_backbone_density {n : ℕ} (D : FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ) (p : Parent) (hp : p ∈ parents D a N)
    (hP : (data D cells a N p).Hypotheses) (E0 : Finset (Fin n × Index))
    (hE : chartFamily (shift D a) E0 ⊆ (data D cells a N p).incidences) (F : ℕ) (hF : 0 < F)
    {lambda R : ℝ} (hR : 0 < R) (hlam : lambda ≤ (data D cells a N p).lam)
    (hret : (data D cells a N p).incidences.card ≤ F*E0.card) :
    (lambda/((F:ℝ)*R))*(backbone D a N p).card ≤
      ((data D cells a N p).σ/R)*(originalFamily (data D cells a N p) (shift D a) E0).card := by
  rw [originalFamily_eq]
  apply full_backbone_coarse_density D cells a N p hp hP (chartFamily (shift D a) E0) hE F hF hR hlam
  rwa [chartFamily_card]
end NativeCoarseBackboneDensity
