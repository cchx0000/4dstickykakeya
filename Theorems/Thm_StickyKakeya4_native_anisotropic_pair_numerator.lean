import Theorems.Thm_StickyKakeya4_native_anisotropic_global_source_bridge
import Theorems.Thm_StickyKakeya4_native_uniform_retention_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeAnisotropicPairNumerator
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeAnisotropicShortRowGeometry NativeAnisotropicGlobalSourceBridge NativeShortRowPackets
open NativeCoarseShadingUniformity NativeCoarseDyadicShading NativeGlobalCoarseRows NativeLastMenuShadingSize
open NativeUniformRetentionTransfer
open scoped BigOperators

def shortRowColumnCost : ℕ := 61^3*515
def pairUpperConstant : ℝ := (shortRowColumnCost:ℝ)*(16*NativeOriginalPrunedMass.volumeConstant)

lemma pairUpperConstant_pos : 0 < pairUpperConstant := by
  have hh := NativeOriginalPrunedMass.volumeConstant_pos
  dsimp [pairUpperConstant,shortRowColumnCost]
  positivity

theorem short_pair_column_image_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level f m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (p : Parent) (v : Parent × Index) :
    (((parentEdges D a (2^m) E p).filter (fun z => fixedPair D a level f m rep z=v)).image
      (columnPair D a m f p)).card ≤ shortRowColumnCost := by
  let F := parentEdges D a (2^m) E p
  let T := F.filter (fun z => fixedPair D a level f m rep z=v)
  by_cases hn : T.Nonempty
  · obtain ⟨x,hx⟩ := hn
    let col := columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ))
    have hs : T.image (columnPair D a m f p)⊆
        (columnHalo 30 257 (col x.2)).image (fun q => (v.1,q)) := by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      have hxF := (mem_filter.mp hx).1
      have hzF := (mem_filter.mp hz).1
      have hzx : z∈shortEdges D a level f m rep F x := mem_filter.mpr
        ⟨hzF,(mem_filter.mp hz).2.trans (mem_filter.mp hx).2.symm⟩
      have hc := short_row_column_mem_halo h original horiginal ha level f m hdy hmL hdelta hwindow
        rep F ((filter_subset _ _).trans hE) p x hxF (mem_filter.mp hxF).2 z hzx
      have hpz : parentLabel D a (2^f) z.1=v.1 := congrArg Prod.fst (mem_filter.mp hz).2
      exact mem_image.mpr ⟨col z.2,hc,Prod.ext hpz.symm rfl⟩
    have hh := (card_le_card hs).trans card_image_le
    rw [columnHalo_card] at hh
    exact hh
  · change (T.image (columnPair D a m f p)).card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hn,image_empty,card_empty]
    exact Nat.zero_le _

lemma fixedPair_card_sum {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level f m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) :
    (E.image (fixedPair D a level f m rep)).card=
      ∑q∈E.image (fun z => parentLabel D a (2^f) z.1),(rowCells D a level f m rep E q).card := by
  have he : (E.image (fixedPair D a level f m rep)).image Prod.fst=
      E.image (fun z => parentLabel D a (2^f) z.1) := by
    simp only [image_image,Function.comp_def,fixedPair]
  rw [card_eq_sum_card_image Prod.fst,he]
  apply sum_congr rfl
  intro q _hq
  exact (rowCells_card_eq D a level f m rep E q).symm

/-- The genuine short shading rows provide the pair numerator upper.
This uses their already-proved full-row capacity, never individual shading
lower bounds or a supplied tube-population exponent. -/
theorem parent_column_pair_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level f m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm6 : 6 ≤ m) (hmL : m ≤ level)
    (hfL : f ≤ level) (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent) :
    (64/((2^m:ℕ):ℝ))*((parentEdges D a (2^m) E p).image (columnPair D a m f p)).card ≤
      pairUpperConstant*((parentEdges D a (2^m) E p).image (fun z => parentLabel D a (2^f) z.1)).card := by
  let F := parentEdges D a (2^m) E p
  let H : ℝ := 64/((2^m:ℕ):ℝ)
  have hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ) := by
    have hs : ((2^f:ℕ):ℝ)*D.thickness ≤ 1 := by
      rw [NativeLocalParentScales.relative_scale hdy hfL]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hs]
  have himage := image_card_le_mul_of_fiber_images F (columnPair D a m f p)
    (fixedPair D a level f m rep) shortRowColumnCost
    (fun v _hv => short_pair_column_image_card h original horiginal ha level f m hdy hmL
      hdelta hwindow rep E hE p v)
  have hrow (q : Parent) : H*(rowCells D a level f m rep F q).card ≤
      16*NativeOriginalPrunedMass.volumeConstant := by
    have hh := projected_row_card_upper h original horiginal ha (2^f) (block level m) (block_pos level m)
      (by rw [block_thickness hdy hmL]; exact NativeCoarseShadingPruning.coarse_thickness_le_one m hm6)
      rep F ((filter_subset _ _).trans hE) q
    simpa only [block_thickness hdy hmL,rowCells_eq_rows] using hh
  have hs : H*(F.image (fixedPair D a level f m rep)).card ≤
      (16*NativeOriginalPrunedMass.volumeConstant)*(F.image (fun z => parentLabel D a (2^f) z.1)).card := by
    rw [fixedPair_card_sum,Nat.cast_sum,mul_sum]
    calc
      _ ≤ ∑_q∈F.image (fun z => parentLabel D a (2^f) z.1),16*NativeOriginalPrunedMass.volumeConstant :=
        sum_le_sum (fun q _hq => hrow q)
      _ = _ := by simp [mul_comm]
  have hi : ((F.image (columnPair D a m f p)).card:ℝ) ≤
      (shortRowColumnCost:ℝ)*(F.image (fixedPair D a level f m rep)).card := by exact_mod_cast himage
  calc
    _ ≤ H*((shortRowColumnCost:ℝ)*(F.image (fixedPair D a level f m rep)).card) :=
      mul_le_mul_of_nonneg_left hi (by dsimp [H]; positivity)
    _ = (shortRowColumnCost:ℝ)*(H*(F.image (fixedPair D a level f m rep)).card) := by ring
    _ ≤ (shortRowColumnCost:ℝ)*((16*NativeOriginalPrunedMass.volumeConstant)*
        (F.image (fun z => parentLabel D a (2^f) z.1)).card) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
    _ = _ := by dsimp [pairUpperConstant]; ring

end NativeAnisotropicPairNumerator
