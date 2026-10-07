import Theorems.Thm_StickyKakeya4_native_slice_count_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeHeightWindowRelations
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels
open NativeParentSliceHeightGeometry NativeFiniteSliceHomogeneity NativeSliceCountComparison
open SelfUniform NativeCoarseShadingUniformity NativeCubicalIncidenceCounts

/-- Independent dyadic coarsening of the actual spatial and time labels. -/
def coarsen (fineSpace fineTime space time : ℕ) (q : Index) : Index :=
  fun v => q v / ((2^(if v=(3:Fin 4) then fineTime-time else fineSpace-space):ℕ):ℤ)

/-- Exact original-point readback. This coarsens time as well as space,
without changing the original point, tube, or parent. -/
theorem coarsen_column {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (fineSpace fineTime space time : ℕ)
    (hs : space ≤ fineSpace) (ht : time ≤ fineTime) (k : Index) :
    coarsen fineSpace fineTime space time
      (columnLabel D a N p (64/((2^fineSpace:ℕ):ℝ))
        (64/((2^fineTime:ℕ):ℝ)) k) =
      columnLabel D a N p (64/((2^space:ℕ):ℝ)) (64/((2^time:ℕ):ℝ)) k := by
  funext v
  by_cases hv : v=(3:Fin 4)
  · simp only [coarsen,columnLabel,chartWidth,hv,if_true]
    rw [←Int.floor_div_natCast]
    congr 1
    rw [NativeAnisotropicColumnCapacity.dyadic_height_eq time fineTime ht]
    push_cast
    ring
  · simp only [coarsen,columnLabel,chartWidth,if_neg hv]
    rw [←Int.floor_div_natCast]
    congr 1
    rw [NativeAnisotropicColumnCapacity.dyadic_height_eq space fineSpace hs]
    push_cast
    ring

/-- A single source-independent menu size installs arbitrary finitely many
actual height/width queries before the same second source core. -/
def relations {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m fs ft : ℕ)
    (space time : Fin K → ℕ) :
    Fin (1+K) → (Fin n × Index) → (Fin n × Index) → Prop :=
  NativeParentSliceCallerMenu.relations D a (2^m)
    (fun p k => columnLabel D a (2^m) p (64/((2^fs:ℕ):ℝ)) (64/((2^ft:ℕ):ℝ)) k)
    (fun _ j => coarsen fs ft (space j) (time j))

lemma relations_refl {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m fs ft : ℕ)
    (space time : Fin K → ℕ) : ∀j x,relations D a m fs ft space time j x x :=
  NativeParentSliceCallerMenu.relations_refl _ _ _ _ _

lemma relations_symm {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m fs ft : ℕ)
    (space time : Fin K → ℕ) :
    ∀j x y,relations D a m fs ft space time j x y →
      relations D a m fs ft space time j y x :=
  NativeParentSliceCallerMenu.relations_symm _ _ _ _ _

/-- Decode the installed menu on every original parent. No time-window
uniformity of an arbitrary later subset is inferred. -/
theorem caller_window_uniformities {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m fs ft : ℕ) (space time : Fin K → ℕ)
    (hs : ∀j,space j ≤ fs) (ht : ∀j,time j ≤ ft)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (relations D a m fs ft space time j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations D a m fs ft space time j) E y)
    (p : Parent) :
    ∀j,HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^(space j):ℕ):ℝ))
        (64/((2^(time j):ℕ):ℝ)) z.2) := by
  have HU := (NativeParentSliceCallerMenu.parent_uniformities D a (2^m)
    (fun p k => columnLabel D a (2^m) p (64/((2^fs:ℕ):ℝ)) (64/((2^ft:ℕ):ℝ)) k)
    (fun _ j => coarsen fs ft (space j) (time j)) E Q H p).2
  intro j
  apply uniformity_congr _ _ _ Q (fun z _hz => coarsen_column D a (2^m) p fs ft
    (space j) (time j) (hs j) (ht j) z.2)
  exact HU j

def points {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f ht : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) : Finset Index :=
  (parentEdges D a (2^m) E p).image
    (fun z => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^ht:ℕ):ℝ)) z.2)

lemma points_horizontal_coarsen {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m fine coarse ht : ℕ) (hcf : coarse ≤ fine)
    (E : Finset (Fin n × Index)) (p : Parent) :
    (points D a m fine ht E p).image (horizontalCoarsen fine coarse) =
      points D a m coarse ht E p := by
  simp only [points,image_image,Function.comp_def]
  apply image_congr
  intro z _hz
  exact columnLabel_horizontalCoarsen D a (2^m) (by positivity) p _ fine coarse hcf z.2

/-- Uniform original incidence degrees imply comparable occupied horizontal
classes at the same chosen coarse time-window scale. -/
theorem horizontal_class_counts {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m fine coarse ht : ℕ) (hcf : coarse ≤ fine)
    (E : Finset (Fin n × Index)) (p : Parent) (Q : ℕ)
    (HF : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^fine:ℕ):ℝ)) (64/((2^ht:ℕ):ℝ)) z.2))
    (HC : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^coarse:ℕ):ℝ)) (64/((2^ht:ℕ):ℝ)) z.2)) :
    ∀x∈points D a m fine ht E p,∀y∈points D a m fine ht E p,
      ((points D a m fine ht E p).filter
        (fun z => horizontalCoarsen fine coarse z=horizontalCoarsen fine coarse x)).card ≤
      Q^4*((points D a m fine ht E p).filter
        (fun z => horizontalCoarsen fine coarse z=horizontalCoarsen fine coarse y)).card := by
  let F := parentEdges D a (2^m) E p
  let point := fun z : Fin n × Index =>
    columnLabel D a (2^m) p (64/((2^fine:ℕ):ℝ)) (64/((2^ht:ℕ):ℝ)) z.2
  have HG : HasUniformFibers F Q (fun z => horizontalCoarsen fine coarse (point z)) := by
    apply uniformity_congr F _ _ Q (fun z _hz =>
      (columnLabel_horizontalCoarsen D a (2^m) (by positivity) p _ fine coarse hcf z.2).symm)
    exact HC
  intro x hx y hy
  have hh := nested_image_fiber_card_comparable F point (horizontalCoarsen fine coarse)
    (Q^2) (Q^2) HF HG (horizontalCoarsen fine coarse x) (horizontalCoarsen fine coarse y)
    (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  simp only [show Q^2*Q^2=Q^4 by ring] at hh
  exact hh

/-- Each occupied height WINDOW has comparable reference column population.
The height may be coarser than the final mesh. The 27-cell endpoint capacity
comes from the actual original parent, not a new ambient support assumption. -/
theorem window_height_counts_comparable {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m f ht : ℕ) (hmf : m ≤ f) (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent) (Q : ℕ)
    (HF : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^ht:ℕ):ℝ)) z.2))
    (HC : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^m:ℕ):ℝ)) (64/((2^ht:ℕ):ℝ)) z.2)) :
    ∀x∈points D a m f ht E p,∀y∈points D a m f ht E p,
      (heightSlice (points D a m f ht E p) (x (3:Fin 4))).card ≤
        27*Q^4*(heightSlice (points D a m f ht E p) (y (3:Fin 4))).card := by
  have hf := horizontal_class_counts D a m f m ht hmf E p Q HF HC
  have hcap (z : ℤ) :
      (((points D a m f ht E p).image (horizontalCoarsen f m)).filter
        (fun q => q (3:Fin 4)=z)).card ≤ 27 := by
    rw [points_horizontal_coarsen D a m f m ht hmf]
    exact endpoint_height_card_le h original horiginal ha (2^m) (by positivity) hscale E hE p _ z
  have hh := coarsen_fiber_comparison (points D a m f ht E p) (horizontalCoarsen f m)
    (fun q => q (3:Fin 4)) (Q^4) 27 hf hcap
  simpa only [heightSlice,horizontalCoarsen_height] using hh

end NativeHeightWindowRelations
