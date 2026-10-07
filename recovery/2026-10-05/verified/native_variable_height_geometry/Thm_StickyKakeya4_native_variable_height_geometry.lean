import Theorems.Thm_StickyKakeya4_native_anisotropic_short_row_geometry
import Theorems.Thm_StickyKakeya4_native_short_row_packets
import Theorems.Thm_StickyKakeya4_native_raw_shadow_point_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeVariableHeightGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeLocalParentPhysicalMap NativeLocalParentGeometry NativeContractedUnitParent
open NativeSpatialAngularGeometry NativeShortRowPackets NativeDirectionRankDichotomy
open scoped BigOperators

open NativeAnisotropicShortRowGeometry

/-- Global-shadow rows at an independent height depth. The factor8 chart
window costs57 spatial bins; no local-height density is assumed. -/
theorem short_row_chart_close {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level f m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbL : b ≤ level)
    (hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))*(64/((2^b:ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (p : Parent) (anchor : Fin n × Index) (hanchor : anchor∈E)
    (hp : parentLabel D a (2^m) anchor.1=p)
    (z : Fin n × Index) (hz : z∈shortEdges D a level f b rep E anchor) :
    (∀v : Fin 3,
      |physicalMap D a (2^m) p (cellCenter (mesh D) z.2) v.castSucc-
        physicalMap D a (2^m) p (cellCenter (mesh D) anchor.2) v.castSucc| ≤
        57*((2^m:ℕ):ℝ)*(64/((2^f:ℕ):ℝ))/512) ∧
      |physicalMap D a (2^m) p (cellCenter (mesh D) z.2) (3:Fin 4)-
        physicalMap D a (2^m) p (cellCenter (mesh D) anchor.2) (3:Fin 4)| ≤
        256*(64/((2^b:ℕ):ℝ))/512 := by
  obtain ⟨hzE,hfine,hheight⟩ := short_member_readback a level f b hdy hbL rep E anchor z hz
  let N : ℝ := ((2^m:ℕ):ℝ)
  let K : ℝ := ((2^f:ℕ):ℝ)
  let H : ℝ := 64/((2^b:ℕ):ℝ)
  let sigma : ℝ := 64/K
  let x := cellCenter (mesh D) anchor.2
  let y := cellCenter (mesh D) z.2
  let dt := y (3:Fin 4)-x (3:Fin 4)
  have hN : 0 < N := by dsimp [N]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hKs : K*sigma=64 := by dsimp [sigma]; field_simp
  have hx := original_cell_in_tube h original horiginal (hE hanchor)
  have hy := original_cell_in_tube h original horiginal (hE hzE)
  have heq : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [heq] at hx hy
  have hw := NativeSameFineParentPacket.same_parent_displacement_error h ha (2^f)
    (by positivity) anchor.1 z.1 hfine hx hy
  change ‖(y-x)-dt • slopeVector D anchor.1‖ ≤ 24*D.thickness+16/K at hw
  change |dt| ≤ 256*H at hheight
  have herr : 24*D.thickness+16/K ≤ 25*sigma := by
    have he : 16/K=sigma/4 := by dsimp [sigma]; ring
    rw [he]
    change D.thickness ≤ sigma at hdelta
    linarith
  have htime : 256*H ≤ 32*N*sigma := by
    change (64/N)*H ≤ 8*sigma at hwindow
    have hh := mul_le_mul_of_nonneg_left hwindow hN.le
    have hid : N*((64/N)*H)=64*H := by field_simp
    rw [hid] at hh
    linarith
  constructor
  · intro v
    let w := (y-x)-dt • slopeVector D anchor.1
    have hwv : |w v.castSucc| ≤ 25*sigma := by
      have hh : |w v.castSucc| ≤ ‖w‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w v.castSucc
      exact hh.trans (hw.trans herr)
    have hs := localSlope_bound D a (2^m) p anchor.1 hp v
    have hmul : |(N*slope (D.line anchor.1) v-(p.1 v:ℝ))*dt| ≤ 256*H := by
      rw [abs_mul]
      exact (mul_le_mul hs hheight (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
    have hn : |N*w v.castSucc| ≤ 25*N*sigma := by
      rw [abs_mul,abs_of_pos hN]
      nlinarith only [mul_le_mul_of_nonneg_left hwv hN.le]
    have hid : N*(y v.castSucc-x v.castSucc)-(p.1 v:ℝ)*dt=
        N*w v.castSucc+(N*slope (D.line anchor.1) v-(p.1 v:ℝ))*dt := by
      dsimp [w,slopeVector]
      simp only [ActualSlopeSource.heightPoint_castSucc]
      ring
    rw [NativeAnisotropicShortRowGeometry.chart_spatial_sub]
    change |(N*(y v.castSucc-x v.castSucc)-(p.1 v:ℝ)*dt)/512| ≤ 57*N*sigma/512
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add hn hmul)).trans (by linarith)
  · rw [NativeAnisotropicShortRowGeometry.chart_height_sub,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    exact div_le_div_of_nonneg_right hheight (by norm_num)

theorem short_row_column_mem_halo {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level f m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbL : b ≤ level)
    (hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))*(64/((2^b:ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (p : Parent) (anchor : Fin n × Index) (hanchor : anchor∈E)
    (hp : parentLabel D a (2^m) anchor.1=p)
    (z : Fin n × Index) (hz : z∈shortEdges D a level f b rep E anchor) :
    columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^b:ℕ):ℝ)) z.2 ∈
      columnHalo 58 257
        (columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^b:ℕ):ℝ)) anchor.2) := by
  have hh := short_row_chart_close h original horiginal ha level f m b hdy hbL hdelta hwindow
    rep E hE p anchor hanchor hp z hz
  apply Fintype.mem_piFinset.mpr
  intro v
  refine Fin.lastCases ?_ (fun v => ?_) v
  · simp only [columnLabel,chartWidth,show (Fin.last 3:Fin 4)=3 by rfl,if_true]
    apply floor_mem_interval 256
    rw [←sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<(64/((2^b:ℕ):ℝ))/512)]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [Nat.cast_ofNat,mul_div_assoc] using hh.2
  · have hv : v.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last v
    simp only [columnLabel,chartWidth,if_neg hv]
    apply floor_mem_interval 57
    rw [←sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<((2^m:ℕ):ℝ)*(64/((2^f:ℕ):ℝ))/512)]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [Nat.cast_ofNat,mul_div_assoc,mul_assoc] using hh.1 v


end NativeVariableHeightGeometry
