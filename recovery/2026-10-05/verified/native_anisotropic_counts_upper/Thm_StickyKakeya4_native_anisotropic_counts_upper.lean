import Theorems.Thm_StickyKakeya4_native_anisotropic_column_capacity
import Theorems.Thm_StickyKakeya4_native_raw_shadow_pair_comparison
import Theorems.Thm_StickyKakeya4_native_original_parent_density_core

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeAnisotropicCountsUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeSpatialAngularGeometry
open NativeAnisotropicShortRowGeometry NativeAnisotropicColumnCapacity
open NativeRawShadowPairComparison

/-- The geometric column capacity applies to the old points of any edge
fiber. Repeated tube labels over an old point introduce no extra vertices. -/
lemma column_point_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m f : ℕ) (hmf : m ≤ f)
    (p : Parent) (i : Fin n) (hp : parentLabel D a (2^m) i=p)
    (E : Finset (Fin n × Index)) (q : Index)
    (hcol : ∀z∈E,columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ))
      (64/((2^m:ℕ):ℝ)) z.2=q) :
    (E.image (fun z => spatialLabel D (2^f) z.2)).card ≤ 6655*2^(f-m) := by
  have hh := dyadic_column_vertices_card_le h m f hmf p i hp (E.image Prod.snd) q (by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    exact hcol z hz)
  simpa only [image_image,Function.comp_def] using hh

/-- Every occupied original raw point belongs to the image of one actual
column fiber. The capacity is derived from native geometry, not supplied. -/
theorem point_image_card_le_columns {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m f : ℕ) (hmf : m ≤ f)
    (p : Parent) (i : Fin n) (hp : parentLabel D a (2^m) i=p)
    (E : Finset (Fin n × Index)) :
    (E.image (fun z => spatialLabel D (2^f) z.2)).card ≤
      (6655*2^(f-m))*(E.image (fun z =>
        columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2)).card := by
  let col := columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ))
  have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images E
    (fun z => spatialLabel D (2^f) z.2) (fun z => col z.2) ((6655*2^(f-m):ℕ):ℝ) (by
      intro q _hq
      exact_mod_cast column_point_image_card_le h m f hmf p i hp
        (E.filter (fun z => col z.2=q)) q (fun _z hz => (mem_filter.mp hz).2))
  exact_mod_cast hh

/-- The fine-parent coordinate remains fixed on each comparison fiber.
Thus the same geometric capacity controls the original fine-parent pairs. -/
theorem pair_image_card_le_columns {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m f : ℕ) (hmf : m ≤ f)
    (p : Parent) (i : Fin n) (hp : parentLabel D a (2^m) i=p)
    (E : Finset (Fin n × Index)) :
    (E.image (rawPair D a f)).card ≤
      (6655*2^(f-m))*(E.image (fun z => (parentLabel D a (2^f) z.1,
        columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))).card := by
  exact pair_image_card_le_of_point_comparison E (fun z => parentLabel D a (2^f) z.1)
    (fun z => spatialLabel D (2^f) z.2)
    (fun z => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2)
    (6655*2^(f-m)) (fun F _hF => point_image_card_le_columns h m f hmf p i hp F)

/-- Both upper counts on an arbitrary actual outer parent. A nonempty
parent supplies its own native tube witness; an empty parent has zero counts.
No incidence, shading, admissibility, or backbone hypothesis is needed. -/
theorem parent_counts_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m f : ℕ) (hmf : m ≤ f)
    (E : Finset (Fin n × Index)) (p : Parent) :
    let F := parentEdges D a (2^m) E p
    let col := columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ))
    let raw := spatialLabel D (2^f)
    let phase := parentLabel D a (2^f)
    (F.image (fun z => raw z.2)).card ≤ (6655*2^(f-m))*(F.image (fun z => col z.2)).card ∧
      (F.image (rawPair D a f)).card ≤
        (6655*2^(f-m))*(F.image (fun z => (phase z.1,col z.2))).card := by
  intro F col raw phase
  by_cases hF : F.Nonempty
  · obtain ⟨z,hz⟩ := hF
    have hp : parentLabel D a (2^m) z.1=p := (mem_filter.mp hz).2
    exact ⟨point_image_card_le_columns h m f hmf p z.1 hp F,
      pair_image_card_le_columns h m f hmf p z.1 hp F⟩
  · rw [not_nonempty_iff_eq_empty.mp hF]
    simp

end NativeAnisotropicCountsUpper
