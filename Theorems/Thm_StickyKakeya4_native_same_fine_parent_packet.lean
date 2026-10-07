import Theorems.Thm_StickyKakeya4_native_angular_packet_readback
import Theorems.Thm_StickyKakeya4_native_normalized_parent_carrier_metric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeSameFineParentPacket
open Classical StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeDirectionRankDichotomy NativeNormalizedParentCarrierMetric

/-- The actual original marked tube stays in the bounded common-height chart.
The integer chart shift is unchanged. -/
lemma tube_height_from_chart_shift {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (i : Fin n) {y : E4} (hy : y∈markedUnitTube (D.line i) D.thickness) :
    |y (3:Fin 4)-(shift D a:ℝ)*mesh D| ≤ 4 := by
  have hm : 0 < mesh D := half_pos h.1.2.1
  have hlo : (shift D a:ℝ)*mesh D ≤ a := by
    exact (le_div_iff₀ hm).mp (Int.floor_le (a/mesh D))
  have hhi : a<((shift D a:ℝ)+1)*mesh D := by
    exact (div_lt_iff₀ hm).mp (Int.lt_floor_add_one (a/mesh D))
  have hs : |a-(shift D a:ℝ)*mesh D| ≤ mesh D :=
    abs_le.mpr ⟨by linarith,by nlinarith⟩
  have ht := (tube_point_bounds (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i)
    h.1.2.1 (ha i) hy).1
  calc
    _ ≤ |y (3:Fin 4)-a|+|a-(shift D a:ℝ)*mesh D| := abs_sub_le _ _ _
    _ ≤ (1+2*D.thickness)+mesh D := add_le_add ht hs
    _ ≤ 4 := by unfold mesh; linarith [h.1.2.2.1]

/-- Original-coordinate comparison between TWO actual old tubes in one fine
phase-parent. It preserves both old tube memberships; no common marked segment
is asserted. The slope and shifted-intercept discrepancies are both paid. -/
theorem same_parent_displacement_error {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (K : ℕ) (hK : 0 < K) (i i' : Fin n)
    (hparent : parentLabel D a K i'=parentLabel D a K i)
    {x y : E4} (hx : x∈markedUnitTube (D.line i) D.thickness)
    (hy : y∈markedUnitTube (D.line i') D.thickness) :
    ‖(y-x)-(y (3:Fin 4)-x (3:Fin 4)) • slopeVector D i‖ ≤
      24*D.thickness+16/(K:ℝ) := by
  let rho : ℝ := 1/(K:ℝ)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hd := h.1.2.1
  let h0 : ℝ := (shift D a:ℝ)*mesh D
  have ht : |y (3:Fin 4)-h0| ≤ 4 := tube_height_from_chart_shift h ha i' hy
  have hs (u : Fin 3) : |slope (D.line i') u-slope (D.line i) u| ≤ rho :=
    same_floor_mul_close _ _ K hK (congrFun (congrArg Prod.fst hparent) u)
  have hb (u : Fin 3) :
      |shiftedIntercept (D.line i') (mesh D) (shift D a) u-
        shiftedIntercept (D.line i) (mesh D) (shift D a) u| ≤ rho :=
    same_floor_mul_close _ _ K hK (congrFun (congrArg Prod.snd hparent) u)
  have hgraph (u : Fin 3) :
      |(intercept (D.line i') u+slope (D.line i') u*y (3:Fin 4))-
        (intercept (D.line i) u+slope (D.line i) u*y (3:Fin 4))| ≤ 8*rho := by
    have he : (intercept (D.line i') u+slope (D.line i') u*y (3:Fin 4))-
        (intercept (D.line i) u+slope (D.line i) u*y (3:Fin 4)) =
        4*(shiftedIntercept (D.line i') (mesh D) (shift D a) u-
          shiftedIntercept (D.line i) (mesh D) (shift D a) u)+
        (y (3:Fin 4)-h0)*(slope (D.line i') u-slope (D.line i) u) := by
      dsimp [shiftedIntercept,h0]
      ring
    rw [he]
    calc
      _ ≤ |4*(shiftedIntercept (D.line i') (mesh D) (shift D a) u-
          shiftedIntercept (D.line i) (mesh D) (shift D a) u)|+
          |(y (3:Fin 4)-h0)*(slope (D.line i') u-slope (D.line i) u)| := abs_add_le _ _
      _ = 4*|shiftedIntercept (D.line i') (mesh D) (shift D a) u-
          shiftedIntercept (D.line i) (mesh D) (shift D a) u|+
          |y (3:Fin 4)-h0| * |slope (D.line i') u-slope (D.line i) u| := by
        rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
      _ ≤ 4*rho+4*rho := add_le_add
        (mul_le_mul_of_nonneg_left (hb u) (by norm_num))
        (mul_le_mul ht (hs u) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hxres := (tube_point_bounds (D.line i) (h.1.2.2.2.2.1 i) (h.2.1.1 i)
    h.1.2.1 (ha i) hx).2
  have hyres := (tube_point_bounds (D.line i') (h.1.2.2.2.2.1 i') (h.2.1.1 i')
    h.1.2.1 (ha i') hy).2
  let w := (y-x)-(y (3:Fin 4)-x (3:Fin 4)) • slopeVector D i
  have hwcoord (u : Fin 3) : |w u.castSucc| ≤ 12*D.thickness+8*rho := by
    have he : w u.castSucc =
        (y u.castSucc-intercept (D.line i') u-slope (D.line i') u*y (3:Fin 4))-
        (x u.castSucc-intercept (D.line i) u-slope (D.line i) u*x (3:Fin 4))+
        ((intercept (D.line i') u+slope (D.line i') u*y (3:Fin 4))-
          (intercept (D.line i) u+slope (D.line i) u*y (3:Fin 4))) := by
      simp only [w,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,slopeVector,
        ActualSlopeSource.heightPoint_castSucc]
      ring
    rw [he]
    have hh' := add_le_add (add_le_add (hyres u) (hxres u)) (hgraph u)
    exact (((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans hh').trans_eq (by ring)
  have hwlast : w (3:Fin 4)=0 := by
    simp only [w,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,slopeVector_last,mul_one,sub_self]
  let M := 12*D.thickness+8*rho
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hsq : ‖w‖^2 ≤ 3*M^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc,Fin.sum_univ_three,
      show (Fin.last 3:Fin 4)=(3:Fin 4) by rfl,hwlast]
    have h0 := pow_le_pow_left₀ (abs_nonneg _) (hwcoord 0) 2
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hwcoord 1) 2
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hwcoord 2) 2
    simp only [sq_abs] at h0 h1 h2
    rw [show (Fin.castSucc (0:Fin 3):Fin 4)=(0:Fin 4) by rfl] at h0
    rw [show (Fin.castSucc (1:Fin 3):Fin 4)=(1:Fin 4) by rfl] at h1
    rw [show (Fin.castSucc (2:Fin 3):Fin 4)=(2:Fin 4) by rfl] at h2
    dsimp [M]
    norm_num only [zero_pow (by decide : 2≠0),add_zero]
    nlinarith only [h0,h1,h2]
  have hn : ‖w‖ ≤ 2*M := by
    nlinarith only [hsq,norm_nonneg w,hM,sq_nonneg M]
  change ‖w‖ ≤ _
  calc
    _ ≤ 2*M := hn
    _ = _ := by dsimp [M,rho]; ring

/-- A union of old tubes from one genuine fine phase-parent has the required
squared-scale packet bound. The current anchor lies on i; the point y may lie
on a DIFFERENT old tube i'. Fine-parent error is charged explicitly. -/
theorem same_fine_parent_quadratic_packet {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (K N : ℕ) (hK : 0 < K) (hN : 0 < N)
    (hscale : D.thickness ≤ (64/(N:ℝ))^2)
    (hparentScale : 1/(K:ℝ) ≤ (64/(N:ℝ))^2)
    {i : Fin n} {k : Index} (hik : (i,k)∈incidences original)
    (i' j : Fin n) (hparent : parentLabel D a K i'=parentLabel D a K i)
    (hangular : (parentLabel D a N i).1=(parentLabel D a N j).1)
    {y : E4} (hy : y∈markedUnitTube (D.line i') D.thickness)
    (hheight : |y (3:Fin 4)-cellCenter (mesh D) k (3:Fin 4)| ≤ 64/(N:ℝ)) :
    Metric.infDist (y-cellCenter (mesh D) k)
      (Submodule.span ℝ {slopeVector D j}:Set E4) ≤ 41*(64/(N:ℝ))^2 := by
  let x := cellCenter (mesh D) k
  let c := y (3:Fin 4)-x (3:Fin 4)
  let Delta := 64/(N:ℝ)
  have hx := original_cell_in_tube h original horiginal hik
  have hm : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [hm] at hx
  have he := same_parent_displacement_error h ha K hK i i' hparent hx hy
  have hd : ‖slopeVector D i-slopeVector D j‖ ≤ 2/(N:ℝ) := by
    simpa only [dist_eq_norm] using
      NativeAngularPacketReadback.same_angular_slopeVector_dist D a N hN i j hangular
  have hc : ‖c • (slopeVector D i-slopeVector D j)‖ ≤ Delta*(2/(N:ℝ)) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hheight hd (norm_nonneg _) (by dsimp [Delta]; positivity)
  have hv : slopeVector D j∈(Submodule.span ℝ {slopeVector D j}:Set E4) :=
    Submodule.subset_span (by simp)
  apply (Metric.infDist_le_dist_of_mem ((Submodule.span ℝ {slopeVector D j}).smul_mem c hv)).trans
  rw [dist_eq_norm]
  have hid : (y-x)-c • slopeVector D j =
      ((y-x)-c • slopeVector D i)+c • (slopeVector D i-slopeVector D j) := by
    rw [smul_sub]
    abel
  change ‖(y-x)-c • slopeVector D j‖ ≤ 41*Delta^2
  rw [hid]
  calc
    _ ≤ ‖(y-x)-c • slopeVector D i‖+‖c • (slopeVector D i-slopeVector D j)‖ := norm_add_le _ _
    _ ≤ (24*D.thickness+16/(K:ℝ))+Delta*(2/(N:ℝ)) := add_le_add he hc
    _ ≤ 41*Delta^2 := by
      have hp : 16/(K:ℝ) ≤ 16*Delta^2 := by
        simpa only [mul_one_div] using
          mul_le_mul_of_nonneg_left hparentScale (by norm_num : (0:ℝ)≤16)
      have heq : Delta*(2/(N:ℝ))=Delta^2/32 := by dsimp [Delta]; ring
      rw [heq]
      change D.thickness ≤ Delta^2 at hscale
      nlinarith only [hscale,hp,sq_nonneg Delta]

/-- The actual predecessor-cell corollary allows its old tube to differ from
the anchor's tube within the same fine phase-parent. Both incidences are retained. -/
theorem same_fine_parent_cell_packet {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (K N : ℕ) (hK : 0 < K) (hN : 0 < N)
    (hscale : D.thickness ≤ (64/(N:ℝ))^2)
    (hparentScale : 1/(K:ℝ) ≤ (64/(N:ℝ))^2)
    {i i' : Fin n} {k l : Index} (hik : (i,k)∈incidences original)
    (hil : (i',l)∈incidences original) (j : Fin n)
    (hparent : parentLabel D a K i'=parentLabel D a K i)
    (hangular : (parentLabel D a N i).1=(parentLabel D a N j).1)
    (hheight : |cellCenter (mesh D) l (3:Fin 4)-cellCenter (mesh D) k (3:Fin 4)| ≤ 64/(N:ℝ)) :
    Metric.infDist (cellCenter (mesh D) l-cellCenter (mesh D) k)
      (Submodule.span ℝ {slopeVector D j}:Set E4) ≤ 41*(64/(N:ℝ))^2 := by
  have hy := original_cell_in_tube h original horiginal hil
  have hm : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [hm] at hy
  exact same_fine_parent_quadratic_packet h original horiginal ha K N hK hN
    hscale hparentScale hik i' j hparent hangular hy hheight

end NativeSameFineParentPacket
