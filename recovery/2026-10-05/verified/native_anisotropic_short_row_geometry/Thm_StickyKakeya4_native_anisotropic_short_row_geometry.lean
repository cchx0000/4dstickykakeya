import Theorems.Thm_StickyKakeya4_native_short_row_packets
import Theorems.Thm_StickyKakeya4_native_raw_shadow_point_comparison

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeAnisotropicShortRowGeometry
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeLocalParentPhysicalMap NativeLocalParentGeometry NativeContractedUnitParent
open NativeSpatialAngularGeometry NativeShortRowPackets NativeDirectionRankDichotomy
open scoped BigOperators

/-- Independent horizontal and height widths on the existing parent chart.
Their pullbacks have sheared horizontal width sigma and original height H. -/
def chartWidth (N : ℕ) (sigma H : ℝ) (v : Fin 4) : ℝ :=
  if v=(3:Fin 4) then H/512 else (N:ℝ)*sigma/512

def columnLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    (sigma H : ℝ) (k : Index) : Index :=
  fun v => ⌊physicalMap D a N p (cellCenter (mesh D) k) v/chartWidth N sigma H v⌋

def columnHalo (spatial height : ℕ) (q : Index) : Finset Index :=
  Fintype.piFinset (fun v =>
    let K := if v=(3:Fin 4) then height else spatial
    Icc (q v-(K:ℤ)) (q v+K))

lemma columnHalo_card (spatial height : ℕ) (q : Index) :
    (columnHalo spatial height q).card=(2*spatial+1)^3*(2*height+1) := by
  have hc (v : Fin 4) (K : ℕ) : (Icc (q v-(K:ℤ)) (q v+K)).card=2*K+1 := by
    have hh : ((Icc (q v-(K:ℤ)) (q v+K)).card:ℤ)=2*(K:ℤ)+1 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      ring
    exact_mod_cast hh
  simp only [columnHalo,Fintype.card_piFinset,Fin.prod_univ_four]
  norm_num only [show (0:Fin 4)≠3 by decide,show (1:Fin 4)≠3 by decide,
    show (2:Fin 4)≠3 by decide,if_false,if_true,hc]
  ring

lemma chart_spatial_sub {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (x y : E4) (v : Fin 3) :
    physicalMap D a N p y v.castSucc-physicalMap D a N p x v.castSucc=
      ((N:ℝ)*(y v.castSucc-x v.castSucc)-(p.1 v:ℝ)*(y (3:Fin 4)-x (3:Fin 4)))/512 := by
  simp only [NativeLocalParentPhysicalMap.physicalMap,baseMap,contractPoint,ActualSlopeSource.heightPoint_castSucc,
    PiLp.smul_apply,smul_eq_mul]
  ring

lemma chart_height_sub {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (x y : E4) :
    physicalMap D a N p y (3:Fin 4)-physicalMap D a N p x (3:Fin 4)=
      (y (3:Fin 4)-x (3:Fin 4))/512 := by
  simp only [NativeLocalParentPhysicalMap.physicalMap,baseMap,contractPoint,
    show (3:Fin 4)=Fin.last 3 by rfl,ActualSlopeSource.heightPoint_last,
    PiLp.smul_apply,smul_eq_mul]
  ring

/-- A literal global-shadow short row has height256H. The existing parent
chart turns its transverse displacement into at most29 horizontal bins.
The height is a bounded halo, not an asserted single slice. -/
theorem short_row_chart_close {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level f m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (p : Parent) (anchor : Fin n × Index) (hanchor : anchor∈E)
    (hp : parentLabel D a (2^m) anchor.1=p)
    (z : Fin n × Index) (hz : z∈shortEdges D a level f m rep E anchor) :
    (∀v : Fin 3,
      |physicalMap D a (2^m) p (cellCenter (mesh D) z.2) v.castSucc-
        physicalMap D a (2^m) p (cellCenter (mesh D) anchor.2) v.castSucc| ≤
        29*((2^m:ℕ):ℝ)*(64/((2^f:ℕ):ℝ))/512) ∧
      |physicalMap D a (2^m) p (cellCenter (mesh D) z.2) (3:Fin 4)-
        physicalMap D a (2^m) p (cellCenter (mesh D) anchor.2) (3:Fin 4)| ≤
        256*(64/((2^m:ℕ):ℝ))/512 := by
  obtain ⟨hzE,hfine,hheight⟩ := short_member_readback a level f m hdy hmL rep E anchor z hz
  let N : ℝ := ((2^m:ℕ):ℝ)
  let K : ℝ := ((2^f:ℕ):ℝ)
  let H : ℝ := 64/N
  let sigma : ℝ := 64/K
  let x := cellCenter (mesh D) anchor.2
  let y := cellCenter (mesh D) z.2
  let dt := y (3:Fin 4)-x (3:Fin 4)
  have hN : 0 < N := by dsimp [N]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hNH : N*H=64 := by dsimp [H]; field_simp
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
  have htime : 256*H ≤ 4*N*sigma := by
    change H^2 ≤ sigma at hwindow
    have hh := mul_le_mul_of_nonneg_left hwindow hN.le
    have hid : N*H^2=64*H := by
      calc
        _ = (N*H)*H := by ring
        _ = _ := by rw [hNH]
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
    rw [chart_spatial_sub]
    change |(N*(y v.castSucc-x v.castSucc)-(p.1 v:ℝ)*dt)/512| ≤ 29*N*sigma/512
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    rw [hid]
    exact ((abs_add_le _ _).trans (add_le_add hn hmul)).trans (by linarith)
  · rw [chart_height_sub,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    exact div_le_div_of_nonneg_right hheight (by norm_num)

theorem short_row_column_mem_halo {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level f m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level)
    (hdelta : D.thickness ≤ 64/((2^f:ℕ):ℝ))
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (p : Parent) (anchor : Fin n × Index) (hanchor : anchor∈E)
    (hp : parentLabel D a (2^m) anchor.1=p)
    (z : Fin n × Index) (hz : z∈shortEdges D a level f m rep E anchor) :
    columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2 ∈
      columnHalo 30 257
        (columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) anchor.2) := by
  have hh := short_row_chart_close h original horiginal ha level f m hdy hmL hdelta hwindow
    rep E hE p anchor hanchor hp z hz
  apply Fintype.mem_piFinset.mpr
  intro v
  refine Fin.lastCases ?_ (fun v => ?_) v
  · simp only [columnLabel,chartWidth,show (Fin.last 3:Fin 4)=3 by rfl,if_true]
    apply floor_mem_interval 256
    rw [←sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<(64/((2^m:ℕ):ℝ))/512)]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [Nat.cast_ofNat,mul_div_assoc] using hh.2
  · have hv : v.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last v
    simp only [columnLabel,chartWidth,if_neg hv]
    apply floor_mem_interval 29
    rw [←sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<((2^m:ℕ):ℝ)*(64/((2^f:ℕ):ℝ))/512)]
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [Nat.cast_ofNat,mul_div_assoc,mul_assoc] using hh.1 v

end NativeAnisotropicShortRowGeometry
