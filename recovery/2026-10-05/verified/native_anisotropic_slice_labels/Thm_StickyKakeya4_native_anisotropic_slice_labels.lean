import Theorems.Thm_StickyKakeya4_native_anisotropic_column_capacity
import Theorems.Thm_StickyKakeya4_native_parent_slice_caller_menu
import Theorems.Thm_StickyKakeya4_native_squared_grain_queries

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeAnisotropicSliceLabels
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeAnisotropicShortRowGeometry NativeAnisotropicColumnCapacity NativeSquaredGrainQueries
open NativeParentSliceCallerMenu NativeConditionedPairMenu SelfUniform

/-- Only the three horizontal coordinates are coarsened. The actual
fixed-length height segment is retained literally at every menu entry. -/
def horizontalCoarsen (fine coarse : ℕ) (q : Index) : Index :=
  fun v => if v=(3:Fin 4) then q v else q v/(2^(fine-coarse):ℕ)

lemma horizontalCoarsen_height (fine coarse : ℕ) (q : Index) :
    horizontalCoarsen fine coarse q (3:Fin 4)=q (3:Fin 4) := by
  simp only [horizontalCoarsen,if_true]

/-- Exact floor quotient readback in the original parent physicalMap.
Independent horizontal and height widths are preserved throughout. -/
theorem columnLabel_horizontalCoarsen {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (H : ℝ)
    (fine coarse : ℕ) (hcf : coarse ≤ fine) (k : Index) :
    horizontalCoarsen fine coarse (columnLabel D a N p (64/((2^fine:ℕ):ℝ)) H k)=
      columnLabel D a N p (64/((2^coarse:ℕ):ℝ)) H k := by
  funext v
  by_cases hv : v=(3:Fin 4)
  · simp only [horizontalCoarsen,columnLabel,chartWidth,hv,if_true]
  · simp only [horizontalCoarsen,columnLabel,chartWidth,if_neg hv]
    rw [←Int.floor_div_natCast]
    congr 1
    rw [dyadic_height_eq coarse fine hcf]
    have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
    field_simp

def slicePoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (p : Parent) (k : Index) : Index :=
  columnLabel D a (2^m) p (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) k

def sliceClass (m f : ℕ) (q : Index) : Index := horizontalCoarsen (phaseDepth m) f q

lemma sliceClass_height (m f : ℕ) (q : Index) : sliceClass m f q (3:Fin 4)=q (3:Fin 4) :=
  horizontalCoarsen_height _ _ _

theorem sliceClass_point_eq_column {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m f : ℕ) (hf : f ≤ phaseDepth m) (p : Parent) (k : Index) :
    sliceClass m f (slicePoint D a m p k)=
      columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) k :=
  columnLabel_horizontalCoarsen D a (2^m) (by positivity) p _ _ _ hf k

/-- The actual fixed-size caller menu, selected before the same E2.
It contains one finest anisotropic point relation and K horizontal classes. -/
def sliceRelations {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depths : Fin K → ℕ) :
    Fin (1+K) → (Fin n × Index) → (Fin n × Index) → Prop :=
  NativeParentSliceCallerMenu.relations D a (2^m) (slicePoint D a m)
    (fun _p j => sliceClass m (depths j))

lemma sliceRelations_refl {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depths : Fin K → ℕ) : ∀j z,sliceRelations D a m depths j z z :=
  NativeParentSliceCallerMenu.relations_refl D a (2^m) (slicePoint D a m)
    (fun _p j => sliceClass m (depths j))

lemma sliceRelations_symm {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depths : Fin K → ℕ) :
    ∀j x y,sliceRelations D a m depths j x y → sliceRelations D a m depths j y x :=
  NativeParentSliceCallerMenu.relations_symm D a (2^m) (slicePoint D a m)
    (fun _p j => sliceClass m (depths j))

/-- Decode the literal installed relations into reference-parent point and
class uniformity. The coarse class map is the actual anisotropic column map,
not an isotropic spatial ancestor. -/
theorem caller_column_uniformities {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depths : Fin K → ℕ) (hdepths : ∀j,depths j ≤ phaseDepth m)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depths j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depths j) E y)
    (p : Parent) :
    HasUniformFibers (parentEdges D a (2^m) E p) Q (fun z => slicePoint D a m p z.2) ∧
      ∀j,HasUniformFibers (parentEdges D a (2^m) E p) Q
        (fun z => columnLabel D a (2^m) p (64/((2^(depths j):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2) := by
  obtain ⟨hPoint,hClass⟩ := parent_uniformities D a (2^m) (slicePoint D a m)
    (fun _p j => sliceClass m (depths j)) E Q H p
  refine ⟨hPoint,?_⟩
  intro j
  apply uniformity_congr _ _ _ Q (fun z _hz => sliceClass_point_eq_column D a m (depths j) (hdepths j) p z.2)
  exact hClass j

end NativeAnisotropicSliceLabels
