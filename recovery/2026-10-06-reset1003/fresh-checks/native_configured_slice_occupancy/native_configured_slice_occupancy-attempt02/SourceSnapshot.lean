import Theorems.Thm_StickyKakeya4_original_tube_slice_occupancy
import Theorems.Thm_StickyKakeya4_native_full_chart_tube_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeConfiguredSliceOccupancy
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeFullCoarseShadow OriginalWWitnessCounts

/-- The occupancy theorem's height-first Euclidean embedding is a coordinate
permutation of the literal configured point. This is not a product-norm claim. -/
lemma height_first_dist (p q : E4) :
    dist (OriginalTubeSliceOccupancy.embedding (fun x : E4 => x 3)
      (fun x => x 0) (fun x => (x 1,x 2)) p)
      (OriginalTubeSliceOccupancy.embedding (fun x : E4 => x 3)
        (fun x => x 0) (fun x => (x 1,x 2)) q) = dist p q := by
  rw [dist_eq_norm,dist_eq_norm]
  have hs :
      ‖OriginalTubeSliceOccupancy.embedding (fun x : E4 => x 3) (fun x => x 0)
          (fun x => (x 1,x 2)) p-
        OriginalTubeSliceOccupancy.embedding (fun x : E4 => x 3) (fun x => x 0)
          (fun x => (x 1,x 2)) q‖^2 = ‖p-q‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_four]
    dsimp [OriginalTubeSliceOccupancy.embedding,OriginalTubeSliceOccupancy.coordinates,
      EuclideanAlignmentPatches.euclidean]
    ring
  nlinarith only [hs,norm_nonneg (p-q),norm_nonneg
    (OriginalTubeSliceOccupancy.embedding (fun x : E4 => x 3) (fun x => x 0)
      (fun x => (x 1,x 2)) p-
     OriginalTubeSliceOccupancy.embedding (fun x : E4 => x 3) (fun x => x 0)
      (fun x => (x 1,x 2)) q)]

/-- Actual Delta-separated configured points and analytic residual8Delta
give the fixed occupancy130^3 at each actual height and output tube. -/
theorem pointsAt_card_le {T : Type*} [DecidableEq T]
    (I : Finset (E4 × T)) (base slope : T → Fin 3 → ℝ) {Delta : ℝ}
    (hDelta : 0 < Delta)
    (hsep : ∀p∈I.image Prod.fst, ∀q∈I.image Prod.fst, p≠q → Delta ≤ dist p q)
    (hinc : ∀p t, (p,t)∈I → ∀j : Fin 3,
      |p j.castSucc-base t j-p 3*slope t j| ≤ 8*Delta)
    (t : T) (z : ℝ) : ((pointsAt I (fun p => p 3) t z).card:ℝ) ≤ 130^3 := by
  have hh := OriginalTubeSliceOccupancy.pointsAt_card_le (I.image Prod.fst) I
    (fun p => p 3) (fun p => p 0) (fun p => (p 1,p 2))
    (fun t => base t 0) (fun t => slope t 0)
    (fun t => (base t 1,base t 2)) (fun t => (slope t 1,slope t 2))
    hDelta (by norm_num : (0:ℝ)≤8)
    (fun _ _ hp => mem_image_of_mem Prod.fst hp)
    (fun p hp q hq hpq => by rw [height_first_dist]; exact hsep p hp q hq hpq)
    (fun p t hp => hinc p t hp 0)
    (fun p t hp => max_le (hinc p t hp 1) (hinc p t hp 2)) t z
  have he : @pointsAt E4 T ℝ (Classical.decEq E4) (Classical.decEq T)
      inferInstance I (fun p => p 3) t z = pointsAt I (fun p => p 3) t z := by
    ext p
    simp only [mem_pointsAt]
  rw [he] at hh
  norm_num at hh ⊢
  exact hh

/-- The original admitted fine source and the same fullSource provide the
residuals internally. Only actual point separation and true tube membership
are read from the configured incidence construction. -/
theorem full_source_pointsAt {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (hb : 8 ≤ b) (E : Finset (Fin n × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (I : Finset (E4 × Fin (R.image (parentLabel D a (2^b))).card))
    (hI : ∀x i, (x,i)∈I → x∈markedUnitTube
      (MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line i))
      (64/((2^b:ℕ):ℝ)))
    (hsep : ∀x∈I.image Prod.fst, ∀y∈I.image Prod.fst, x≠y →
      64/((2^b:ℕ):ℝ) ≤ dist x y)
    (i : Fin (R.image (parentLabel D a (2^b))).card) (z : ℝ) :
    ((pointsAt I (fun p => p 3) i z).card:ℝ) ≤ 130^3 := by
  let line := fun i => MarkedIsometricChart.line O 0 ((fullSource h R a level b E).line i)
  apply pointsAt_card_le I (fun i => intercept (line i)) (fun i => slope (line i))
    (by positivity : (0:ℝ)<64/((2^b:ℕ):ℝ)) hsep ?_ i z
  intro x i hxi j
  simpa only [mul_comm] using
    (NativeFullChartTubeGraph.full_source_graph_bounds h R a level b hb E O hO i x (hI x i hxi)).2 j

end NativeConfiguredSliceOccupancy
