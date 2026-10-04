import Theorems.Thm_StickyKakeya4_native_coarse_original_heights
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeSourceCoarseReadback
open Classical Finset NativeCommonCubicalMesh NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCoarseOriginalIncidences NativeCoarseOriginalGeometry NativeCoarseOriginalHeights
variable {T : Type*}
def chartFamily (shift : ℤ) (E0 : Finset (T × Index)) : Finset (T × ShearBinFibers.Index) :=
  E0.image (fun e => (e.1,chartIndex shift e.2))
def originalFamily (P : PhysicalRescalingIncidenceTransfer.Data T) (shift : ℤ)
    (E0 : Finset (T × Index)) : Finset (ShearBinFibers.Index × T) :=
  E0.image (fun e => (P.cellBin (chartIndex shift e.2),e.1))
lemma chartFamily_card (shift : ℤ) (E0 : Finset (T × Index)) : (chartFamily shift E0).card=E0.card := by
  apply card_image_of_injective
  intro e f h
  apply Prod.ext
  · exact congrArg (fun v : T × ShearBinFibers.Index => v.1) h
  · exact (chartIndex_injective shift) (congrArg (fun v : T × ShearBinFibers.Index => v.2) h)
lemma originalFamily_eq (P : PhysicalRescalingIncidenceTransfer.Data T) (shift : ℤ)
    (E0 : Finset (T × Index)) : originalFamily P shift E0=incidences P (chartFamily shift E0) := by
  simp only [originalFamily,incidences,chartFamily,image_image]
  rfl
lemma originalFamily_tubes (P : PhysicalRescalingIncidenceTransfer.Data T) (shift : ℤ)
    (E0 : Finset (T × Index)) :
    TwoTubePathCollisionCount.tubes (originalFamily P shift E0)=E0.image Prod.fst := by
  simp only [TwoTubePathCollisionCount.tubes,originalFamily,image_image]
  rfl
/-- The genuine capacity bound is on the ORIGINAL E0, using injectivity of
 the actual old chart and the true N-fiber bound of physical coarsening. -/
theorem original_capacity (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (shift : ℤ) (E0 : Finset (T × Index)) (hE : chartFamily shift E0 ⊆ P.incidences) :
    E0.card ≤ P.N*(originalFamily P shift E0).card := by
  rw [originalFamily_eq,←chartFamily_card shift E0]
  exact actual_capacity P hP _ hE
/-- Density transfer on the SAME original family E0, with no intermediate
 cardinality identification assumed. -/
theorem original_density (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (shift : ℤ) (E0 : Finset (T × Index)) (hE : chartFamily shift E0 ⊆ P.incidences)
    {lambda F R : ℝ} (hF : 0 < F) (hR : 0 < R)
    (hden : lambda*(E0.image Prod.fst).card ≤ F*P.δ*(E0.card:ℝ)) :
    (lambda/(F*R))*(TwoTubePathCollisionCount.tubes (originalFamily P shift E0)).card ≤
      (P.σ/R)*(originalFamily P shift E0).card := by
  rw [originalFamily_eq]
  apply actual_density_transfer P hP _ hE hF hR
  have ht : (chartFamily shift E0).image Prod.fst=E0.image Prod.fst := by
    simp only [chartFamily,image_image]
    rfl
  simpa only [ht,chartFamily_card] using hden
/-- Actual native source constants: delta_old=thickness/8, R=28, and the
 new mesh is N*thickness/224. These are equalities of the concrete formulas. -/
theorem native_scale_readback {n : ℕ} (D : StickyKakeya4.FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ) (p : Parent) :
    let P := data D cells a N p
    P.δ=D.thickness/8 ∧ normalization P=28 ∧ P.σ/normalization P=(N:ℝ)*D.thickness/224 := by
  dsimp [data,NativeOriginalParentSelection.mesh,normalization,PhysicalRescalingIncidenceTransfer.Data.σ]
  constructor
  · ring
  constructor
  · norm_num
  · ring
/-- The source parent supplies every physical bound for the actual later
 labels. No normalized tube AD or global-grain profile is inferred here. -/
theorem native_original_geometry {n : ℕ} (D : StickyKakeya4.FiniteScaleSource n)
    (cells : Fin n → Finset Index) (a : ℝ) (N : ℕ) (p : Parent)
    (hP : (data D cells a N p).Hypotheses) (E0 : Finset (Fin n × Index))
    (hE : chartFamily (shift D a) E0 ⊆ (data D cells a N p).incidences) :
    let P := data D cells a N p
    ∀ e ∈ originalFamily P (shift D a) E0,
      |height P (normalization P) e.1| ≤ 1 ∧
      (∀ j, |(coordinates P (normalization P) e.1).1 j| ≤ 1) ∧
      (∀ j, |(coordinates P (normalization P) e.1).1 j-P.offset e.2 j/normalization P-
        P.slope e.2 j*height P (normalization P) e.1| ≤ 13*((N:ℝ)*D.thickness/224)) := by
  dsimp only
  intro e he
  rw [originalFamily_eq] at he
  let P := data D cells a N p
  have hN : 0 < N := hP.N_pos
  have hbox := normalized_coordinate_box P hP _ hE
    (original_parent_offset_bound D cells a N hN p) e.1 e.2 he
  refine ⟨hbox.1,hbox.2,?_⟩
  intro j
  have hr := normalized_residual P hP _ hE (normalization_pos P) e.1 e.2 he j
  have hscale := (native_scale_readback D cells a N p).2.2
  change P.σ/normalization P=(N:ℝ)*D.thickness/224 at hscale
  rw [hscale] at hr
  norm_num [P,data] at hr ⊢
  exact hr
end NativeSourceCoarseReadback
