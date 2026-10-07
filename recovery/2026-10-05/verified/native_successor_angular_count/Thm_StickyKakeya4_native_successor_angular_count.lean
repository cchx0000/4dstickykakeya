import Theorems.Thm_StickyKakeya4_native_spatial_shadow_point_menu
import Theorems.Thm_StickyKakeya4_native_two_axis_conditional_transfer
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4400000

noncomputable section
namespace NativeSuccessorAngularCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalParentDensityCore
open NativeCoarsePointMultiplicity NativeCoarseDirectionThinning NativeJointUniformCoarseRelations
open NativeSpatialAngularGeometry NativeSpatialShadowPointMenu NativeTwoAxisConditionalTransfer
open NativeIncidenceMultiplicityTower

/-- The actual original incidences in a child spatial cube and a fixed
coarser angular cell. The source labels and all representatives stay fixed. -/
def successorEdges {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m f : ℕ) (q : Index) (u : Fin 3 → ℤ) : Finset (Fin n × Index) :=
  E.filter (fun z => spatialLabel D (2^f) z.2=q ∧ angularLabel D (2^m) z.1=u)

def successorLabels {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (m f : ℕ) (q : Index) (u : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  (successorEdges D E m f q u).image (fun z => angularLabel D (2^f) z.1)

/-- Later selections only remove actual successor labels. -/
lemma successorLabels_mono {n : ℕ} (D : FiniteScaleSource n)
    {E F : Finset (Fin n × Index)} (hFE : F⊆E)
    (m f : ℕ) (q : Index) (u : Fin 3 → ℤ) :
    successorLabels D F m f q u ⊆ successorLabels D E m f q u :=
  image_subset_image (filter_subset_filter _ hFE)

/-- Any actual angular menu bound survives arbitrary later selections. -/
lemma successor_card_le_of_subset {n : ℕ} (D : FiniteScaleSource n)
    {E F : Finset (Fin n × Index)} (hFE : F⊆E)
    (m f : ℕ) (q : Index) (u : Fin 3 → ℤ) {B : ℝ}
    (H : ((successorLabels D E m f q u).card:ℝ) ≤ B) :
    ((successorLabels D F m f q u).card:ℝ) ≤ B := by
  exact (Nat.cast_le.mpr (card_le_card (successorLabels_mono D hFE m f q u))).trans H

/-- A fixed initial angular menu follows from the original north-chart
slope bound. It is independent of the source cardinality and point scale. -/
lemma root_angular_image_card {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (F : Finset (Fin n × Index)) :
    (F.image (fun z => angularLabel D 1 z.1)).card ≤ 343 := by
  have hsub : F.image (fun z => angularLabel D 1 z.1) ⊆ integerBox 3 3 0 := by
    intro u hu
    obtain ⟨z,_hz,rfl⟩ := mem_image.mp hu
    apply Fintype.mem_piFinset.mpr
    intro v
    have hs := slope_bound (D.line z.1) (h.1.2.2.2.2.1 z.1) (h.2.1.1 z.1) v
    have hh := floor_mem_interval (x:=slope (D.line z.1) v) (y:=0) 2 (by simpa only [sub_zero,Nat.cast_ofNat] using hs)
    simpa only [angularLabel,Nat.cast_one,one_mul,Int.floor_zero,Pi.zero_apply] using hh
  exact (card_le_card hsub).trans_eq (integerBox_card 3 3 0)

/-- Uniformity of a later selected incidence set is unnecessary. Actual
spatial/angular localization and the proved hereditary physical upper give
its successor angular menu directly. -/
theorem localized_angular_image_card {n : ℕ} {D : FiniteScaleSource n} {eta a loss kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E F : Finset (Fin n × Index))
    (hE : E⊆incidences original) (hER : ∀z∈E,z.1∈R) (hFE : F⊆E)
    (level m f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmf : m ≤ f) (hfl : f ≤ level)
    (q : Index) (u : Fin 3 → ℤ)
    (hspace : ∀z∈F,spatialLabel D (2^f) z.2=q)
    (hang : ∀z∈F,angularLabel D (2^m) z.1=u)
    (H : ∀p : Parent,
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) F p))).toReal ≤
        D.thickness^(-loss)*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa)) :
    ((F.image (fun z => angularLabel D (2^f) z.1)).card:ℝ) ≤
      (131^3*2401:ℝ)*D.thickness^(-loss)*
        ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa) := by
  let A := D.thickness^(-loss)*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa)
  have hdpos : 0 < D.thickness := h.1.2.1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : F⊆incidences original := hFE.trans hE
  have hFR : ∀z∈F,z.1∈R := fun z hz => hER z (hFE hz)
  have hscale : ((2^f:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hfl]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hNM : 2^m ≤ 2^f := Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hmf
  have hParents := phase_parent_image_card h original horiginal ha (2^m) (2^f)
    (by positivity) hNM hscale F hF q u hspace hang
  have hLocal : ∀p∈F.image (fun z => parentLabel D a (2^m) z.1),
      (((parentEdges D a (2^m) F p).image (fun z => angularLabel D (2^f) z.1)).card:ℝ) ≤ 2401*A := by
    intro p hp
    let Fp := parentEdges D a (2^m) F p
    let I := Fp.image (physicalPair h R a level f)
    have hFpF : Fp⊆F := filter_subset _ _
    have hFp : Fp.Nonempty := parent_nonempty F (parentLabel D a (2^m)) hp
    have hFpR : ∀z∈Fp,z.1∈R := fun z hz => hFR z (hFpF hz)
    have hMu : multiplicity I ≤ A := by
      rw [←conditional_full_eq_image h R F a level m f hFR p]
      exact H p
    have hSupport : (0:ℝ) < (I.image Prod.snd).card := by
      exact_mod_cast card_pos.mpr ((hFp.image _).image _)
    have hPairCard : (I.card:ℝ) ≤ A*(I.image Prod.snd).card := (div_le_iff₀ hSupport).mp hMu
    have hPoint := spatial_point_image_card h original horiginal ha (2^f)
      (NativeCoarseDyadicShading.block level f) (by positivity) hscale
      (NativeCoarseDyadicShading.block_mesh hdy hfl)
      (representative h R a (2^f)) Fp (hFpF.trans hF)
      (fun z hz => (representative_spec h R a (2^f) (mem_image_of_mem _ (hFpR z hz))).2)
      q (fun z hz => hspace z (hFpF hz))
    have hSupportEq : I.image Prod.snd=Fp.image
        (pointLabel D a (2^f) (NativeCoarseDyadicShading.block level f) (representative h R a (2^f))) := by
      rw [image_image]
      rfl
    have hSupportCard : ((I.image Prod.snd).card:ℝ) ≤ 2401 := by
      rw [hSupportEq]
      exact_mod_cast hPoint
    have hAngleEq : Fp.image (fun z => angularLabel D (2^f) z.1)=I.image (fun z => z.1.1) := by
      rw [image_image]
      rfl
    calc
      _ = ((I.image (fun z => z.1.1)).card:ℝ) := by rw [hAngleEq]
      _ ≤ (I.card:ℝ) := by exact_mod_cast card_image_le
      _ ≤ A*(I.image Prod.snd).card := hPairCard
      _ ≤ A*2401 := mul_le_mul_of_nonneg_left hSupportCard hA
      _ = _ := by ring
  have hCount := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images F
    (fun z => angularLabel D (2^f) z.1) (fun z => parentLabel D a (2^m) z.1) (2401*A) hLocal
  calc
    _ ≤ (2401*A)*((F.image (fun z => parentLabel D a (2^m) z.1)).card:ℝ) := hCount
    _ ≤ (2401*A)*(131^3:ℕ) := mul_le_mul_of_nonneg_left
      (by exact_mod_cast hParents) (by positivity)
    _ = _ := by dsimp [A]; push_cast; ring

/-- Actual successor labels of a source cube and angular parent, bounded by
an already-derived hereditary same-R physical upper. No successor bound,
pointwise adaptive uniformity, or candidate certificate is a premise. -/
theorem actual_successor_card {n : ℕ} {D : FiniteScaleSource n} {eta a loss kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index))
    (hE : E⊆incidences original) (hER : ∀z∈E,z.1∈R)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (H : ∀F⊆E,∀m f : ℕ,m ≤ f → f ≤ level → ∀p : Parent,
      (NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) F p))).toReal ≤
        D.thickness^(-loss)*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa))
    (m f : ℕ) (hmf : m ≤ f) (hfl : f ≤ level) (q : Index) (u : Fin 3 → ℤ) :
    ((successorLabels D E m f q u).card:ℝ) ≤
      (131^3*2401:ℝ)*D.thickness^(-loss)*
        ((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-kappa) := by
  apply localized_angular_image_card h original horiginal ha R E (successorEdges D E m f q u)
    hE hER (filter_subset _ _) level m f hdy hmf hfl q u
  · intro z hz
    exact (mem_filter.mp hz).2.1
  · intro z hz
    exact (mem_filter.mp hz).2.2
  · exact H _ (filter_subset _ _) m f hmf hfl

end NativeSuccessorAngularCount
