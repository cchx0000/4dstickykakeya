import Theorems.Thm_StickyKakeya4_native_relative_coarse_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeCurrentReferenceReadback
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeLocalParentSource NativeCubicalIncidenceCounts NativeRelativeCoarseReadback
open NativeRelativeCoarsePointMenu

/-- The native reference shading and the sparse current shading may differ.
Every coarse label still reads the same original T edge through doublePair;
no native-input proof for T is needed. -/
theorem selected_relative_incidence_image {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty) (M B : ℕ)
    (hT : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) e)
    (hmesh : (B:ℝ)*(source h R Eref a m p).thickness/128=32/(M:ℝ)) :
    NativeCoarseShadingCapacity.coarse (source h R Eref a m p) 0 M B
      (NativeCoarseDirectionThinning.representative href univ 0 M)
      (incidences (sourceCells D R T a (2^m) p))=
        T.image (doublePair h R a m p hQ M) := by
  unfold NativeCoarseShadingCapacity.coarse
  calc
    _ = ((incidences (sourceCells D R T a (2^m) p)).image
        (originalPair (parentLabels D R a (2^m) p))).image
          (roundedPair h R a m p hQ M) := by
      rw [image_image]
      apply image_congr
      intro z _hz
      exact relative_label_readback h R Eref a m p hQ M B href hmesh z
    _ = (T.image (NativeLocalCellCoherence.localPair D a (2^m) p)).image
        (roundedPair h R a m p hQ M) := by
      rw [source_incidences_readback D R T a (2^m) p hT]
    _ = _ := by rw [image_image]; rfl

/-- The selected coarse source's literal rows, on a native Eref backbone,
are read directly from the original sparse T. -/
theorem selected_relative_source_shading {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref T : Finset (Fin n × Index)) (a : ℝ) (level m b : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2^m) p).Nonempty)
    (hT : ∀z∈T,z.1∈parentLabels D R a (2^m) p)
    (href : IsWangZakharovNativeFiniteInput (source h R Eref a m p) e)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) (hb : b≤level-m+6)
    (Q : Finset Parent)
    (hsep : ∀u∈Q,∀v∈Q,u≠v → 64/((2^b:ℕ):ℝ) ≤
      dist (direction ((source h R Eref a m p).line
        (NativeCoarseDirectionThinning.representative href univ 0 (2^b) u)))
      (direction ((source h R Eref a m p).line
        (NativeCoarseDirectionThinning.representative href univ 0 (2^b) v))))
    (i : Fin Q.card) :
    (NativeCoarseCellSource.source href 0 (level-m+6) b Q
      (NativeCoarseDirectionThinning.representative href univ 0 (2^b))
      (incidences (sourceCells D R T a (2^m) p)) hsep).shading i=
        wzCellShading (32/((2^b:ℕ):ℝ))
          (fun _ : Fin 1 =>
            (((T.image (doublePair h R a m p hQ (2^b))).filter
              (fun z => z.1=NativeCoarseCellSource.parentIndex Q i)).image Prod.snd)) 0 := by
  rw [NativeCoarseCellSource.source_shading]
  have he := selected_relative_incidence_image h R Eref T a m p hQ (2^b)
    (NativeCoarseDyadicShading.block (level-m+6) b) hT href
    (NativeCoarseDyadicShading.block_mesh (local_source_dyadic h R Eref a level m p hdy hm) hb)
  simp only [NativeCoarseShadingCapacity.rows,he]

end NativeCurrentReferenceReadback
