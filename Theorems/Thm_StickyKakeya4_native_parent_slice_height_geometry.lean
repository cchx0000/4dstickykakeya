import Theorems.Thm_StickyKakeya4_native_anisotropic_slice_labels
import Theorems.Thm_StickyKakeya4_native_local_cell_coherence

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeParentSliceHeightGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeOriginalParentPhysicalData NativeLocalParentPhysicalMap NativeLocalParentGeometry
open NativeContractedUnitParent NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels
open NativeLocalCellCoherence
open scoped BigOperators

/-- Actual parent membership bounds the spatial chart coordinates, including
the original tube residual. No ambient support box is assumed. -/
theorem physical_parent_spatial_bound {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hscale : (N:ℝ)*D.thickness ≤ 1) (p : Parent) (i : Fin n)
    (hp : parentLabel D a N i=p) (k : Index) (hk : k∈original i) (v : Fin 3) :
    |physicalMap D a N p (cellCenter (mesh D) k) v.castSucc| ≤ 1/8 := by
  have hb0 := (parameter_box D a N p i hp).2 v
  have hb : |localIntercept D a N p i v| ≤ 1/4 := abs_le.mpr ⟨by linarith [hb0.1],hb0.2.le⟩
  have hs := localSlope_bound D a N p i hp v
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime D a k| ≤ 1 at ht
  have hprod : |(NativeOriginalPaddedCells.oldTime D a k/4)*localSlope D N p i v| ≤ 1/4 := by
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
    have hh := mul_le_mul (div_le_div_of_nonneg_right ht (by norm_num : (0:ℝ)≤4)) hs
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1/4)
    simpa only [mul_one] using hh
  have hfront : |NativeLocalParentCells.frontPoint D a N p i k v.castSucc| ≤ 1/64 := by
    simp only [NativeLocalParentCells.frontPoint,contractPoint,ActualSlopeSource.heightPoint_castSucc,
      PiLp.smul_apply,PiLp.add_apply,smul_eq_mul]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/32)]
    have hh := (abs_add_le _ _).trans (add_le_add hb hprod)
    linarith only [hh]
  have herr := frontPoint_near_physicalCell h original horiginal ha N p i k hk v.castSucc
  have htri := abs_sub_le (physicalMap D a N p (cellCenter (mesh D) k) v.castSucc)
    (NativeLocalParentCells.frontPoint D a N p i k v.castSucc) 0
  simp only [sub_zero] at htri
  rw [abs_sub_comm] at herr
  have hh := htri.trans (add_le_add herr hfront)
  nlinarith only [hh,hscale]

def endpointHeightMenu (height : ℤ) : Finset Index :=
  Fintype.piFinset (fun v => if v=(3:Fin 4) then {height} else Icc (-1) 1)

lemma endpointHeightMenu_card (height : ℤ) : (endpointHeightMenu height).card=27 := by
  simp only [endpointHeightMenu,Fintype.card_piFinset,Fin.prod_univ_four]
  norm_num [show (0:Fin 4)≠3 by decide,show (1:Fin 4)≠3 by decide,show (2:Fin 4)≠3 by decide]
  decide

theorem endpoint_column_mem_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1) (p : Parent) (i : Fin n)
    (hp : parentLabel D a N i=p) (H : ℝ) (k : Index) (hk : k∈original i) :
    columnLabel D a N p (64/(N:ℝ)) H k ∈
      endpointHeightMenu (columnLabel D a N p (64/(N:ℝ)) H k (3:Fin 4)) := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hw : (N:ℝ)*(64/(N:ℝ))/512=(1/8:ℝ) := by field_simp; norm_num
  apply Fintype.mem_piFinset.mpr
  intro v
  refine Fin.lastCases ?_ (fun v => ?_) v
  · simp only [show (Fin.last 3:Fin 4)=3 by rfl,if_true,mem_singleton]
  · have hv : v.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last v
    simp only [columnLabel,chartWidth,if_neg hv]
    rw [hw]
    have hh := abs_le.mp (physical_parent_spatial_bound h original horiginal ha N hscale p i hp k hk v)
    have hlo : (-1:ℝ) ≤ physicalMap D a N p (cellCenter (mesh D) k) v.castSucc/(1/8) := by
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<1/8)).mpr
      linarith only [hh.1]
    have hup : physicalMap D a N p (cellCenter (mesh D) k) v.castSucc/(1/8) ≤ (1:ℝ) := by
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<1/8)).mpr
      linarith only [hh.2]
    have hl := Int.floor_mono hlo
    have hu := Int.floor_mono hup
    norm_num only [Int.floor_neg,Int.ceil_one,Int.floor_one] at hl hu
    exact mem_Icc.mpr ⟨hl,hu⟩

/-- At the parent-width horizontal endpoint, each fixed height segment has
at most27 occupied spatial bins in the actual reference parent. -/
theorem endpoint_height_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent) (H : ℝ) (height : ℤ) :
    (((parentEdges D a N E p).image (fun z => columnLabel D a N p (64/(N:ℝ)) H z.2)).filter
      (fun q => q (3:Fin 4)=height)).card ≤ 27 := by
  have hs : ((parentEdges D a N E p).image (fun z => columnLabel D a N p (64/(N:ℝ)) H z.2)).filter
      (fun q => q (3:Fin 4)=height) ⊆ endpointHeightMenu height := by
    intro q hq
    obtain ⟨hq,hheight⟩ := mem_filter.mp hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    have hh := endpoint_column_mem_menu h original horiginal ha N hN hscale p z.1
      (mem_filter.mp hz).2 H z.2 ((mem_incidences original z.1 z.2).mp (hE (mem_filter.mp hz).1))
    rwa [hheight] at hh
  exact (card_le_card hs).trans_eq (endpointHeightMenu_card height)

end NativeParentSliceHeightGeometry
