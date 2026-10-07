import Theorems.Thm_StickyKakeya4_native_variable_height_geometry
import Theorems.Thm_StickyKakeya4_native_anisotropic_row_count_lower
import Theorems.Thm_StickyKakeya4_native_anisotropic_column_menus
import Theorems.Thm_StickyKakeya4_native_halo_count_transfer
import Theorems.Thm_StickyKakeya4_native_full_vertex_fiber_density

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeVariableHeightRowLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeSpatialAngularGeometry NativeShortRowPackets
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeJointUniformCoarseRelations
open NativeAnisotropicShortRowGeometry NativeAnisotropicColumnMenus NativeHaloCountTransfer
open NativeFullVertexFiberDensity NativeRefinedShortRowDensity NativeDyadicParentCells
open scoped BigOperators

open NativeVariableHeightGeometry

/-- A fine-parent short row remains entirely inside its actual coarser
phase parent. This is an exact incidence inclusion, with no new selection. -/
lemma shortEdges_subset_parent {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (level f m b : ℕ) (hmf : m ≤ f) (rep : Parent → Fin n)
    (E : Finset (Fin n × Index)) (p : Parent) (anchor : Fin n × Index)
    (hp : parentLabel D a (2^m) anchor.1=p) :
    shortEdges D a level f b rep E anchor⊆parentEdges D a (2^m) E p := by
  intro z hz
  obtain ⟨hzE,he⟩ := mem_filter.mp hz
  have hf := congrArg Prod.fst he
  have hc := congrArg (ancestor f m) hf
  change ancestor f m (parentLabel D a (2^f) z.1)=ancestor f m (parentLabel D a (2^f) anchor.1) at hc
  rw [parent_ancestor_eq D a hmf,parent_ancestor_eq D a hmf,hp] at hc
  exact mem_filter.mpr ⟨hzE,hc⟩

/-- The finite halo charge is uniform in the height and horizontal scales. -/
def chargeConstant : ℕ := 127^3*519

/-- A deterministic bridge for actual reference rows. Its final source
specialization supplies hrowLower from queried_short_row_lower, not from a
slice-density certificate. Both original pair and point counts are retained. -/
theorem parent_counts_of_actual_rows {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level f m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmf : m ≤ f) (hbf : b ≤ f) (hfL : f ≤ level)
    (hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))*(64/((2^b:ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) (K : ℝ)
    (hrowLower : ∀anchor∈parentEdges D a (2^m) E p,
      K ≤ (shortVertices D a level f b rep E anchor).card) :
    let F := parentEdges D a (2^m) E p
    let col := columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^b:ℕ):ℝ))
    let raw := spatialLabel D (2^f)
    let phase := parentLabel D a (2^f)
    K*(F.image (fun z => col z.2)).card ≤ chargeConstant*(F.image (fun z => raw z.2)).card ∧
      K*(F.image (fun z => (phase z.1,col z.2))).card ≤
        chargeConstant*(F.image (fun z => (phase z.1,raw z.2))).card := by
  intro F col raw phase
  let row := shortEdges D a level f b rep E
  have hscale : 64/((2^f:ℕ):ℝ) ≤ 64/((2^b:ℕ):ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hbf
  have hrow (x : Fin n × Index) (hx : x∈F) : row x⊆F :=
    shortEdges_subset_parent D a level f m b hmf rep E p x (mem_filter.mp hx).2
  have hcharge (x : Fin n × Index) (hx : x∈F) (y : Fin n × Index) (hy : y∈F)
      (z : Fin n × Index) (hz : z∈row x) (hraw : raw z.2=raw y.2) :
      col x.2∈columnHalo 63 259 (col y.2) := by
    have h1 := NativeVariableHeightGeometry.short_row_column_mem_halo h original horiginal ha level f m b hdy (hbf.trans hfL)
      hdelta hwindow rep E hE p x (mem_filter.mp hx).1 (mem_filter.mp hx).2 z hz
    have h2 := same_raw_column_mem_halo h (2^m) (2^f) (by positivity) (by positivity)
      p y.1 (mem_filter.mp hy).2 (64/((2^b:ℕ):ℝ)) (by positivity) hscale z.2 y.2 hraw
    exact columnHalo_trans 58 257 5 2 (col x.2) (col z.2) (col y.2)
      (columnHalo_symm 58 257 _ _ h1) h2
  constructor
  · apply NativeAnisotropicRowCountLower.image_row_count_lower F hp (fun z => col z.2) (fun z => raw z.2) row
      (fun y => columnHalo 63 259 (col y.2)) K chargeConstant hrow
    · exact hrowLower
    · exact hcharge
    · intro y _hy
      rw [columnHalo_card]
      norm_num [chargeConstant]
  · apply NativeAnisotropicRowCountLower.image_row_count_lower F hp (fun z => (phase z.1,col z.2))
      (fun z => (phase z.1,raw z.2)) row
      (fun y => (columnHalo 63 259 (col y.2)).image (fun c => (phase y.1,c))) K chargeConstant hrow
    · intro x hx
      apply (hrowLower x hx).trans
      have he : ((row x).image (fun z => (phase z.1,raw z.2))).image Prod.snd=
          shortVertices D a level f b rep E x := by
        ext v
        simp only [shortVertices,row,raw,image_image,Function.comp_def,mem_image]
      rw [←he]
      exact_mod_cast card_image_le
    · intro x hx y hy z hz he
      have hf : phase z.1=phase x.1 := congrArg Prod.fst (mem_filter.mp hz).2
      have hxy : phase x.1=phase y.1 := hf.symm.trans (congrArg Prod.fst he)
      exact mem_image.mpr ⟨col x.2,hcharge x hx y hy z hz (congrArg Prod.snd he),
        Prod.ext hxy.symm rfl⟩
    · intro y _hy
      have hh := card_image_le (s := columnHalo 63 259 (col y.2)) (f := fun c => (phase y.1,c))
      rw [columnHalo_card] at hh
      exact_mod_cast hh

/-- Actual source specialization: the time-filling factor is derived from
the same E2 finest richness, two source costs, and the installed query(f,m).
No later subset inherits this lower bound without its own paid retention. -/
theorem queried_parent_counts_lower {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hER : ∀z∈E,z.1∈R)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (f m b : ℕ) (hmf : m ≤ f) (hbf : b ≤ f) (hfL : f ≤ level) (hb6 : 6 ≤ b)
    (hwindow : (64/((2^m:ℕ):ℝ))*(64/((2^b:ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)))
    (HF : HasUniformFibers E Q2 (fixedPair D a level f f (representative h R a (2^f))))
    (HC : HasUniformFibers E Q2 (fixedPair D a level f b (representative h R a (2^f))))
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    let F := parentEdges D a (2^m) E p
    let col := columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^b:ℕ):ℝ))
    let raw := spatialLabel D (2^f)
    let phase := parentLabel D a (2^f)
    let gain := lambda*D.thickness^(c1+3*c2)*((64/((2^b:ℕ):ℝ))/(64/((2^f:ℕ):ℝ)))
    gain*(F.image (fun z => col z.2)).card ≤
      (2401*chargeConstant:ℝ)*(F.image (fun z => raw z.2)).card ∧
      gain*(F.image (fun z => (phase z.1,col z.2))).card ≤
        (2401*chargeConstant:ℝ)*(F.image (fun z => (phase z.1,raw z.2))).card := by
  intro F col raw phase gain
  let rep := representative h R a (2^f)
  have hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ) := by
    have hs : ((2^f:ℕ):ℝ)*D.thickness ≤ 1 := by
      rw [NativeLocalParentScales.relative_scale hdy hfL]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hs]
  have hrow (x : Fin n × Index) (hx : x∈F) :
      gain/2401 ≤ (shortVertices D a level f b rep E x).card := by
    have hxE := (mem_filter.mp hx).1
    have hq : (fixedPair D a level f b rep x).2∈
        rowCells D a level f b rep E (phase x.1) := by
      apply (mem_rowCells D a level f b rep E _ _).mpr
      exact mem_image.mpr ⟨x,hxE,rfl⟩
    have hl := queried_short_row_lower h original horiginal ha R E hE F1 F2 G Q1 Q2
      hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2 f b hbf hfL hb6 HF HC
      (phase x.1) (fixedPair D a level f b rep x).2 hq
    have hc := short_children_le_vertices h original horiginal ha R E hE hER f b hbf hfL hdy x
    have hcr : (rowChildren D a level f b rep E (phase x.1)
        (fixedPair D a level f b rep x).2).card ≤
        (2401:ℝ)*(shortVertices D a level f b rep E x).card := by exact_mod_cast hc
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2401)).mpr
    simpa only [gain,mul_comm] using hl.trans hcr
  have hc := parent_counts_of_actual_rows h original horiginal ha level f m b hdy hmf hbf hfL
    hdelta hwindow rep E hE p hp (gain/2401) hrow
  constructor
  · calc
      _ = 2401*((gain/2401)*(F.image (fun z => col z.2)).card) := by ring
      _ ≤ 2401*((chargeConstant:ℝ)*(F.image (fun z => raw z.2)).card) :=
        mul_le_mul_of_nonneg_left hc.1 (by norm_num)
      _ = _ := by ring
  · calc
      _ = 2401*((gain/2401)*(F.image (fun z => (phase z.1,col z.2))).card) := by ring
      _ ≤ 2401*((chargeConstant:ℝ)*(F.image (fun z => (phase z.1,raw z.2))).card) :=
        mul_le_mul_of_nonneg_left hc.2 (by norm_num)
      _ = _ := by ring


end NativeVariableHeightRowLower
