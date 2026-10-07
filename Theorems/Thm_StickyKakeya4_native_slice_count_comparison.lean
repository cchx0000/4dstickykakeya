import Theorems.Thm_StickyKakeya4_native_parent_slice_height_geometry
import Theorems.Thm_StickyKakeya4_native_finite_slice_homogeneity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeSliceCountComparison
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeConditionedPairMenu NativeCoarseShadingUniformity
open NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels NativeParentSliceHeightGeometry
open NativeFiniteSliceHomogeneity NativeSquaredGrainQueries SelfUniform

def points {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) : Finset Index :=
  (parentEdges D a (2^m) E p).image
    (fun z => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2)

def heightSlice (P : Finset Index) (height : ℤ) : Finset Index := P.filter (fun q => q (3:Fin 4)=height)

lemma points_coarsen {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m fine coarse : ℕ)
    (hcf : coarse ≤ fine) (E : Finset (Fin n × Index)) (p : Parent) :
    (points D a m fine E p).image (horizontalCoarsen fine coarse)=points D a m coarse E p := by
  simp only [points,image_image,Function.comp_def]
  apply image_congr
  intro z _hz
  exact columnLabel_horizontalCoarsen D a (2^m) (by positivity) p _ fine coarse hcf z.2

/-- Two actual installed column relations make distinct occupied finer
columns comparable in every occupied coarser horizontal class, across heights. -/
theorem column_class_counts_comparable {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m fine coarse : ℕ) (hcf : coarse ≤ fine) (E : Finset (Fin n × Index)) (p : Parent) (Q : ℕ)
    (HF : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^fine:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))
    (HC : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^coarse:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2)) :
    ∀x∈points D a m fine E p,∀y∈points D a m fine E p,
      ((points D a m fine E p).filter (fun z => horizontalCoarsen fine coarse z=horizontalCoarsen fine coarse x)).card ≤
        Q^4*((points D a m fine E p).filter (fun z => horizontalCoarsen fine coarse z=horizontalCoarsen fine coarse y)).card := by
  let F := parentEdges D a (2^m) E p
  let point := fun z : Fin n × Index =>
    columnLabel D a (2^m) p (64/((2^fine:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2
  have HG : HasUniformFibers F Q (fun z => horizontalCoarsen fine coarse (point z)) := by
    apply uniformity_congr F _ _ Q (fun z _hz =>
      (columnLabel_horizontalCoarsen D a (2^m) (by positivity) p _ fine coarse hcf z.2).symm)
    exact HC
  intro x hx y hy
  have hh := nested_image_fiber_card_comparable F point (horizontalCoarsen fine coarse)
    (Q^2) (Q^2) HF HG (horizontalCoarsen fine coarse x) (horizontalCoarsen fine coarse y)
    (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  simp only [show Q^2*Q^2=Q^4 by ring] at hh
  dsimp only [points,F,point] at hh ⊢
  exact hh

/-- The parent-width endpoint has at most27 spatial bins per height.
Consequently every occupied height slice at any installed width is comparable
to every other slice, with only27Q^4 loss. -/
theorem reference_height_counts_comparable {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m f : ℕ) (hmf : m ≤ f) (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent) (Q : ℕ)
    (HF : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))
    (HC : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^m:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2)) :
    ∀x∈points D a m f E p,∀y∈points D a m f E p,
      (heightSlice (points D a m f E p) (x (3:Fin 4))).card ≤
        27*Q^4*(heightSlice (points D a m f E p) (y (3:Fin 4))).card := by
  have hf := column_class_counts_comparable D a m f m hmf E p Q HF HC
  have hcap (z : ℤ) :
      (((points D a m f E p).image (horizontalCoarsen f m)).filter (fun q => q (3:Fin 4)=z)).card ≤ 27 := by
    rw [points_coarsen D a m f m hmf]
    exact endpoint_height_card_le h original horiginal ha (2^m) (by positivity) hscale E hE p _ z
  have hh := coarsen_fiber_comparison (points D a m f E p) (horizontalCoarsen f m)
    (fun q => q (3:Fin 4)) (Q^4) 27 hf hcap
  simpa only [heightSlice,horizontalCoarsen_height] using hh

theorem reference_slice_average_cross {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m f : ℕ) (hmf : m ≤ f) (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent) (Q : ℕ)
    (HF : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))
    (HC : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^m:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))
    (z : ℤ) (hz : z∈(points D a m f E p).image (fun q => q (3:Fin 4))) :
    (heightSlice (points D a m f E p) z).card*((points D a m f E p).image (fun q => q (3:Fin 4))).card ≤
        27*Q^4*(points D a m f E p).card ∧
      (points D a m f E p).card ≤
        27*Q^4*(heightSlice (points D a m f E p) z).card*
          ((points D a m f E p).image (fun q => q (3:Fin 4))).card := by
  exact fiber_card_average_cross _ _ (27*Q^4)
    (reference_height_counts_comparable h original horiginal ha m f hmf hscale E hE p Q HF HC) z hz

/-- Actual caller readback of all finite horizontal class populations.
No occupied class or slice density is supplied as a hypothesis. -/
theorem caller_local_class_counts {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depths : Fin K → ℕ) (hdepths : ∀j,depths j ≤ phaseDepth m)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depths j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depths j) E y)
    (p : Parent) (i j : Fin K) (hij : depths i ≤ depths j) :
    ∀x∈points D a m (depths j) E p,∀y∈points D a m (depths j) E p,
      ((points D a m (depths j) E p).filter
        (fun z => horizontalCoarsen (depths j) (depths i) z=horizontalCoarsen (depths j) (depths i) x)).card ≤
        Q^4*((points D a m (depths j) E p).filter
          (fun z => horizontalCoarsen (depths j) (depths i) z=horizontalCoarsen (depths j) (depths i) y)).card := by
  have HU := (caller_column_uniformities D a m depths hdepths E Q H p).2
  exact column_class_counts_comparable D a m (depths j) (depths i) hij E p Q (HU j) (HU i)

/-- Finite cross-count formulation of averaging over the occupied heights. -/
def HasSliceAverage (P : Finset Index) (C : ℕ) : Prop :=
  ∀z∈P.image (fun q => q (3:Fin 4)),
    (heightSlice P z).card*(P.image (fun q => q (3:Fin 4))).card ≤ C*P.card ∧
      P.card ≤ C*(heightSlice P z).card*(P.image (fun q => q (3:Fin 4))).card

/-- The literal finite caller relations and actual parent geometry yield
slice averages both at the finest squared mesh and at every requested width.
The endpoint entry m is used only to control occupied heights. -/
theorem caller_reference_slice_averages {n K level : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (hm6 : 6 ≤ m) (hmL : m ≤ level) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (depths : Fin K → ℕ) (hlo : ∀j,m ≤ depths j) (hhi : ∀j,depths j ≤ phaseDepth m)
    (endpoint : Fin K) (hend : depths endpoint=m)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depths j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depths j) E y)
    (p : Parent) :
    HasSliceAverage (points D a m (phaseDepth m) E p) (27*Q^4) ∧
      ∀j,HasSliceAverage (points D a m (depths j) E p) (27*Q^4) := by
  have HU := caller_column_uniformities D a m depths hhi E Q H p
  have HC : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^m:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2) := by
    simpa only [hend] using HU.2 endpoint
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hmL]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · intro z hz
    exact reference_slice_average_cross h original horiginal ha m (phaseDepth m)
      (by unfold phaseDepth; omega) hscale E hE p Q HU.1 HC z hz
  · intro j z hz
    exact reference_slice_average_cross h original horiginal ha m (depths j) (hlo j)
      hscale E hE p Q (HU.2 j) HC z hz

end NativeSliceCountComparison
