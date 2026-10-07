import Theorems.Thm_StickyKakeya4_native_same_fine_parent_packet
import Theorems.Thm_StickyKakeya4_native_rank_one_slope_cap
import Theorems.Thm_StickyKakeya4_native_quantized_line_packets
import Theorems.Thm_StickyKakeya4_native_compatible_angular_candidates

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeParentHeightSpatialCells
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeOriginalParentPhysicalData
open NativeDirectionRankDichotomy NativeSameFineParentPacket NativeCompatibleAngularCandidates

/-- Only the raw fourth-coordinate cell is fixed. No spatial-cell or
translated local-chart alignment is assumed. -/
lemma same_height_cell_close {rho : ℝ} (hrho : 0 < rho) (x y : E4)
    (he : wzDyadicCellIndex rho x (3:Fin 4)=wzDyadicCellIndex rho y (3:Fin 4)) :
    |x (3:Fin 4)-y (3:Fin 4)| ≤ rho := by
  change ⌊x (3:Fin 4)/rho⌋=⌊y (3:Fin 4)/rho⌋ at he
  have hm : ⌊x (3:Fin 4)/rho⌋∈Icc (⌊y (3:Fin 4)/rho⌋-(0:ℤ))
      (⌊y (3:Fin 4)/rho⌋+(0:ℤ)) := by simp only [sub_zero,add_zero,he,mem_Icc]; exact ⟨le_rfl,le_rfl⟩
  have hh : |x (3:Fin 4)/rho-y (3:Fin 4)/rho| ≤ 1 := by
    simpa only [Nat.cast_zero,zero_add] using NativeQuantizedLinePackets.abs_sub_le_of_floor_mem 0 hm
  rw [←sub_div,abs_div,abs_of_pos hrho] at hh
  simpa only [one_mul] using (div_le_iff₀ hrho).mp hh

/-- A genuine phase parent meets one raw height slab in a set of bounded
diameter at the slab's own scale. Both points retain their original incidences. -/
theorem same_parent_height_distance {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (K M : ℕ) (hM : 0 < M) (hMK : M ≤ K) (hscale : (K:ℝ)*D.thickness ≤ 1)
    (x y : Fin n × Index) (hx : x∈incidences original) (hy : y∈incidences original)
    (hparent : parentLabel D a K y.1=parentLabel D a K x.1)
    (hheight : spatialLabel D M y.2 (3:Fin 4)=spatialLabel D M x.2 (3:Fin 4)) :
    dist (cellCenter (mesh D) y.2) (cellCenter (mesh D) x.2) ≤ 3*(64/(M:ℝ)) := by
  let X := cellCenter (mesh D) x.2
  let Y := cellCenter (mesh D) y.2
  let rho : ℝ := 64/(M:ℝ)
  let t : ℝ := Y (3:Fin 4)-X (3:Fin 4)
  have hK : 0 < K := hM.trans_le hMK
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hMKr : (M:ℝ) ≤ K := by exact_mod_cast hMK
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hxT := original_cell_in_tube h original horiginal hx
  have hyT := original_cell_in_tube h original horiginal hy
  have hmesh : 2*mesh D=D.thickness := by unfold mesh; ring
  rw [hmesh] at hxT hyT
  have herr := same_parent_displacement_error h ha K hK x.1 y.1 hparent hxT hyT
  have ht : |t| ≤ rho := same_height_cell_close hrho Y X hheight
  have hv := NativeRankOneSlopeCap.slopeVector_norm_le_two h x.1
  have htvec : ‖t • slopeVector D x.1‖ ≤ 2*rho := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul ht hv (norm_nonneg _) hrho.le).trans_eq (by ring)
  have hdK : D.thickness ≤ 1/(K:ℝ) := by
    apply (le_div_iff₀ hKr).mpr
    simpa only [mul_comm] using hscale
  have herrScale : 24*D.thickness+16/(K:ℝ) ≤ rho := by
    calc
      _ ≤ 24*(1/(K:ℝ))+16/(K:ℝ) :=
        by linarith only [hdK]
      _ = 40/(K:ℝ) := by ring
      _ ≤ 40/(M:ℝ) := div_le_div_of_nonneg_left (by norm_num) hMr hMKr
      _ ≤ 64/(M:ℝ) := div_le_div_of_nonneg_right (by norm_num) hMr.le
  calc
    _ = ‖Y-X‖ := dist_eq_norm _ _
    _ = ‖((Y-X)-t • slopeVector D x.1)+t • slopeVector D x.1‖ := by congr 1; abel
    _ ≤ ‖(Y-X)-t • slopeVector D x.1‖+‖t • slopeVector D x.1‖ := norm_add_le _ _
    _ ≤ (24*D.thickness+16/(K:ℝ))+2*rho := add_le_add herr htvec
    _ ≤ 3*rho := by linarith only [herrScale]

/-- One fixed genuine parent and one raw height cell occupy at most7^3
spatial cells at the coarser scale. This is derived from physical geometry. -/
theorem parent_height_spatial_count {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (K M : ℕ) (hM : 0 < M) (hMK : M ≤ K) (hscale : (K:ℝ)*D.thickness ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent)
    (hparent : ∀z∈E,parentLabel D a K z.1=p) (t : ℤ) :
    ((E.filter (fun z => spatialLabel D M z.2 (3:Fin 4)=t)).image
      (fun z => spatialLabel D M z.2)).card ≤ 343 := by
  let S := E.filter (fun z => spatialLabel D M z.2 (3:Fin 4)=t)
  let T := S.image (fun z => spatialLabel D M z.2)
  by_cases hSn : S.Nonempty
  · obtain ⟨z0,hz0⟩ := hSn
    let q0 := spatialLabel D M z0.2
    have ht : ∀q∈T,q (3:Fin 4)=t := by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      exact (mem_filter.mp hz).2
    have hmap : ∀q∈T,(fun j : Fin 3 => q j.castSucc)∈integerBox 3 3 (fun j => q0 j.castSucc) := by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      have hd := same_parent_height_distance h original horiginal ha K M hM hMK hscale z0 z
        (hE (mem_filter.mp hz0).1) (hE (mem_filter.mp hz).1)
        ((hparent z (mem_filter.mp hz).1).trans (hparent z0 (mem_filter.mp hz0).1).symm)
        ((mem_filter.mp hz).2.trans (mem_filter.mp hz0).2.symm)
      have hrho : (0:ℝ)<64/(M:ℝ) := by positivity
      apply Fintype.mem_piFinset.mpr
      intro j
      have hc : |cellCenter (mesh D) z.2 j.castSucc-cellCenter (mesh D) z0.2 j.castSucc| ≤ 3*(64/(M:ℝ)) := by
        have hh := PiLp.dist_apply_le (cellCenter (mesh D) z.2) (cellCenter (mesh D) z0.2) j.castSucc
        rw [Real.dist_eq] at hh
        exact hh.trans hd
      have hs : |cellCenter (mesh D) z.2 j.castSucc/(64/(M:ℝ))-
          cellCenter (mesh D) z0.2 j.castSucc/(64/(M:ℝ))| ≤ (3:ℝ) := by
        rw [←sub_div,abs_div,abs_of_pos hrho]
        exact (div_le_iff₀ hrho).mpr hc
      exact NativeQuantizedLinePackets.floor_mem_interval 3 hs
    have hinj : Set.InjOn (fun q : Index => fun j : Fin 3 => q j.castSucc) (T:Set Index) := by
      intro q hq q' hq' he
      ext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact (ht q hq).trans (ht q' hq').symm
      · exact congrFun he j
    have hcard : T.card ≤ (integerBox 3 3 (fun j => q0 j.castSucc)).card :=
      card_le_card_of_injOn _ hmap hinj
    simpa only [integerBox_card,show (2*3+1)^3=343 by norm_num] using hcard
  · have hS : S=∅ := not_nonempty_iff_eq_empty.mp hSn
    change T.card ≤ 343
    simp only [T,hS,image_empty,card_empty]
    omega

lemma dyadic_scale_le_one (level m : ℕ) (hm : m ≤ level) :
    ((2^m:ℕ):ℝ)*((2:ℝ)⁻¹^level) ≤ 1 := by
  have hp : (2:ℝ)^m ≤ (2:ℝ)^level := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm
  simp only [Nat.cast_pow,Nat.cast_ofNat,inv_pow]
  rw [←div_eq_mul_inv]
  exact (div_le_one (by positivity : (0:ℝ)<(2:ℝ)^level)).mpr hp

/-- The dyadic source hypotheses supply every scale premise of the physical
count. No parent spatial-menu certificate is an input. -/
theorem dyadic_parent_height_spatial_count {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m depth : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level) (hdepth : depth ≤ m)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent)
    (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) (t : ℤ) :
    ((E.filter (fun z => spatialLabel D (2^depth) z.2 (3:Fin 4)=t)).image
      (fun z => spatialLabel D (2^depth) z.2)).card ≤ 343 := by
  apply parent_height_spatial_count h original horiginal ha (2^m) (2^depth) (by positivity)
    (Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hdepth) _ E hE p hparent t
  rw [hdy]
  exact dyadic_scale_le_one level m hm

/-- The menu on fine raw nodes is exactly the image of the same original
incidences. Ancestry uses raw fourth-coordinate labels, before chart translation. -/
theorem ancestor_height_spatial_count {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m depth : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level) (hdepth : depth ≤ m)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent)
    (hparent : ∀z∈E,parentLabel D a (2^m) z.1=p) (t : ℤ) :
    (((E.image (fun z => spatialLabel D (2^m) z.2)).filter
      (fun u => spatialAncestor m depth u (3:Fin 4)=t)).image (spatialAncestor m depth)).card ≤ 343 := by
  have he : ((E.image (fun z => spatialLabel D (2^m) z.2)).filter
      (fun u => spatialAncestor m depth u (3:Fin 4)=t)).image (spatialAncestor m depth) =
      (E.filter (fun z => spatialLabel D (2^depth) z.2 (3:Fin 4)=t)).image
        (fun z => spatialLabel D (2^depth) z.2) := by
    ext q
    simp only [mem_image,mem_filter]
    constructor
    · rintro ⟨u,⟨⟨z,hz,rfl⟩,hzt⟩,hzq⟩
      have ha := spatialAncestor_label D hdepth z.2
      exact ⟨z,⟨hz,by simpa only [ha] using hzt⟩,ha.symm.trans hzq⟩
    · rintro ⟨z,⟨hz,hzt⟩,hzq⟩
      have ha := spatialAncestor_label D hdepth z.2
      exact ⟨spatialLabel D (2^m) z.2,⟨⟨z,hz,rfl⟩,by simpa only [ha] using hzt⟩,ha.trans hzq⟩
  rw [he]
  exact dyadic_parent_height_spatial_count h original horiginal ha level m depth hdy hm hdepth E hE p hparent t

end NativeParentHeightSpatialCells
