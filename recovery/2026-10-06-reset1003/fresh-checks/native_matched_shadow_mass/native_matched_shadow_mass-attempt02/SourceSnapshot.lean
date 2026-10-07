import Theorems.Thm_StickyKakeya4_native_matched_shadow_readback

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeMatchedShadowMass
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCoarseDirectionThinning NativeCoarseShadingCapacity NativeCoarseShadingPruning
open NativeCubicalIncidenceCounts NativeLocalParentSource NativeRelativeCoarseReadback
open scoped BigOperators ENNReal

/-- A genuine retained coarse core shades only rows of the same full
reference shadow. This compares shading mass, not tube-family cardinality. -/
theorem core_mass_le_full {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (E : Finset (Fin n × Index)) (Q : Finset Parent)
    (hQP : Q ⊆ R.image (parentLabel D a (2 ^ b)))
    (hsep : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → 64 / ((2 ^ b : ℕ) : ℝ) ≤
      dist (direction (D.line (representative h R a (2 ^ b) p)))
        (direction (D.line (representative h R a (2 ^ b) q)))) :
    (wzTotalShadingVolume (NativeCoarseCellSource.source h a level b Q
      (representative h R a (2 ^ b)) E hsep)).toReal ≤
    (wzTotalShadingVolume (NativeFullCoarseShadow.fullSource h R a level b E)).toReal := by
  rw [NativeCoarseSourceMass.source_total_shading_real, NativeFullCoarseShadow.full_mass_real]
  apply sum_le_sum_of_subset_of_nonneg hQP
  intro p _hp _hpQ
  exact ENNReal.toReal_nonneg

/-- Exact total full-shadow mass at the actual cell mesh Delta/2. Each
occupied parent/cell pair is counted once, including empty family rows. -/
theorem full_pair_mass {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level b : ℕ) (E : Finset (Fin n × Index)) (hE : ∀ z ∈ E, z.1 ∈ R) :
    (wzTotalShadingVolume (NativeFullCoarseShadow.fullSource h R a level b E)).toReal =
      ((coarse D a (2 ^ b) (NativeCoarseDyadicShading.block level b)
        (representative h R a (2 ^ b)) E).card : ℝ) * (32 / ((2 ^ b : ℕ) : ℝ)) ^ 4 := by
  let P := R.image (parentLabel D a (2 ^ b))
  let rep := representative h R a (2 ^ b)
  let block := NativeCoarseDyadicShading.block level b
  have hw (p : Parent) : weight D a level b rep E p =
      ((rows D a (2 ^ b) block rep E p).card : ℝ) * (32 / ((2 ^ b : ℕ) : ℝ)) ^ 4 := by
    unfold weight
    rw [volume_wzCellShading (by positivity : 0 < 32 / ((2 ^ b : ℕ) : ℝ))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 32 / ((2 ^ b : ℕ) : ℝ))]
    rfl
  have hsum : ((coarse D a (2 ^ b) block rep E).card : ℝ) =
      ∑ p ∈ P, ((rows D a (2 ^ b) block rep E p).card : ℝ) := by
    exact_mod_cast coarse_card_sum_rows D a (2 ^ b) block rep E P
      (fun z hz => mem_image_of_mem _ (hE z hz))
  rw [NativeFullCoarseShadow.full_mass_real]
  change (∑ p ∈ P, weight D a level b rep E p) = _
  simp_rw [hw]
  rw [← sum_mul, ← hsum]

/-- The native source is Eref, while the literal pair count comes from
the selected original A. This is the exact bridge used by the lower reader. -/
theorem mixed_full_pair_mass {n : ℕ} {D : FiniteScaleSource n} {eta etaS : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref A : Finset (Fin n × Index)) (a : ℝ) (level m b : ℕ) (p : Parent)
    (hQ : (parentLabels D R a (2 ^ m) p).Nonempty)
    (hA : ∀ z ∈ A, z.1 ∈ parentLabels D R a (2 ^ m) p)
    (hS : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaS)
    (hdy : D.thickness = (2 : ℝ)⁻¹ ^ level) (hm : m ≤ level) (hb : b ≤ level - m + 6) :
    (wzTotalShadingVolume
      (NativeFullCoarseShadow.fullSource hS univ 0 (level - m + 6) b
        (incidences (sourceCells D R A a (2 ^ m) p)))).toReal =
      ((A.image (doublePair h R a m p hQ (2 ^ b))).card : ℝ) *
        (32 / ((2 ^ b : ℕ) : ℝ)) ^ 4 := by
  rw [full_pair_mass hS univ 0 (level - m + 6) b _ (fun z _hz => mem_univ z.1)]
  rw [NativeCurrentReferenceReadback.selected_relative_incidence_image
    h R Eref A a m p hQ (2 ^ b) (NativeCoarseDyadicShading.block (level - m + 6) b) hA hS
    (NativeCoarseDyadicShading.block_mesh (local_source_dyadic h R Eref a level m p hdy hm) hb)]

end NativeMatchedShadowMass
