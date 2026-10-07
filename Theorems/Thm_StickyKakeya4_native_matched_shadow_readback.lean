import Theorems.Thm_StickyKakeya4_native_current_reference_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeMatchedShadowReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeRelativeCoarseReadback NativeCubicalIncidenceCounts
open NativeCoarseShadingCapacity

/-- Literal rows on every full reference parent, with no direction color or
native-input condition on the sparse shading. -/
theorem mixed_full_shading {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref E : Finset (Fin n × Index)) (a : ℝ) (level m b : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2 ^ m) p).Nonempty)
    (hE : ∀ z ∈ E, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) e)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level) (hm : m ≤ level)
    (hb : b ≤ level - m + 6)
    (i : Fin (((univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2 ^ b))).card)) :
    (NativeFullCoarseShadow.fullSource hS univ 0 (level - m + 6) b
      (incidences (sourceCells D R E a (2 ^ m) p))).shading i =
        wzCellShading (32 / ((2 ^ b : ℕ) : ℝ))
          (fun _ : Fin 1 =>
            (((E.image (doublePair h R a m p hQ (2 ^ b))).filter
              (fun z => z.1 = NativeCoarseCellSource.parentIndex
                ((univ : Finset (Fin (parentLabels D R a (2 ^ m) p).card)).image
                  (parentLabel (source h R Eref a m p) 0 (2 ^ b))) i)).image Prod.snd)) 0 := by
  rw [NativeFullCoarseShadow.full_shading]
  have he := NativeCurrentReferenceReadback.selected_relative_incidence_image
    h R Eref E a m p hQ (2 ^ b)
    (NativeCoarseDyadicShading.block (level - m + 6) b) hE hS
    (NativeCoarseDyadicShading.block_mesh
      (local_source_dyadic h R Eref a level m p hdy hm) hb)
  simp only [NativeFullCoarseShadow.shadow, rows, he]

/-- The full shadow's multiplicity reads the selected double image, while
its native input remains the full fine reference source. -/
theorem mixed_full_multiplicity {n : ℕ} {D : FiniteScaleSource n} {eta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref E : Finset (Fin n × Index)) (a : ℝ) (level m b : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2 ^ m) p).Nonempty)
    (hE : ∀ z ∈ E, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) e)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level) (hm : m ≤ level)
    (hb : b ≤ level - m + 6) :
    (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource hS univ 0 (level - m + 6) b
        (incidences (sourceCells D R E a (2 ^ m) p)))).toReal =
      NativeIncidenceMultiplicityTower.multiplicity
        (E.image (doublePair h R a m p hQ (2 ^ b))) := by
  rw [NativeCoarsePointMultiplicity.full_source_multiplicity_real hS univ 0
    (level - m + 6) b _ (fun z _hz => mem_univ z.1)]
  rw [NativeCurrentReferenceReadback.selected_relative_incidence_image h R Eref E a m p hQ (2 ^ b)
    (NativeCoarseDyadicShading.block (level - m + 6) b) hE hS
    (NativeCoarseDyadicShading.block_mesh
      (local_source_dyadic h R Eref a level m p hdy hm) hb)]

end NativeMatchedShadowReadback
