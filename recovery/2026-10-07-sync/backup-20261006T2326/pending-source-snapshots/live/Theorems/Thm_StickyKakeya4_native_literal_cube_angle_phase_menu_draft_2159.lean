/- UNVERIFIED literal native-cube/coarse-angle phase menu.
No parent source, mesh change, or source-dependent occupancy tax is used.
All scalar errors below come from actual original cell shading membership.
-/
import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
import Theorems.Thm_StickyKakeya4_native_common_direction_phase_menu
import Theorems.Thm_StickyKakeya4_native_quantized_line_packets
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_native_literal_reference_shadow_cube_draft_2150

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeLiteralCubeAnglePhaseMenuDraft2159
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeOriginalParentPhysicalData NativeCubicalIncidenceCounts
open NativeQuantizedLinePackets NativeReferenceXYGridMenus NativeTangentGridCoarsening

/-- Same coarse slope cell and a common ORIGINAL native fine physical ball
leave a fixed196-bin intercept discrepancy. Both time and position use the
same original cells; the original graph error is6delta before /4. -/
theorem native_cube_intercept_spread {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Nc Nf : ℕ) (hNc : 0<Nc) (hNf : 0<Nf) (hcf : Nc ≤ Nf)
    (hscale : (Nc:ℝ)*D.thickness ≤ 1)
    (i j : Fin n) (k l : Index) (hk : k∈original i) (hl : l∈original j)
    (center : E4) (hkBall : dist (cellCenter (mesh D) k) center ≤ 128/(Nf:ℝ))
    (hlBall : dist (cellCenter (mesh D) l) center ≤ 128/(Nf:ℝ))
    (hAngle : (parentLabel D a Nc i).1=(parentLabel D a Nc j).1) (v : Fin 3) :
    |(Nc:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) v-
      (Nc:ℝ)*shiftedIntercept (D.line j) (mesh D) (shift D a) v| ≤ 196 := by
  let x := ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)
  let y := ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) l)
  let rho : ℝ := 64/(Nf:ℝ)
  let si := slope (D.line i) v
  let sj := slope (D.line j) v
  let bi := shiftedIntercept (D.line i) (mesh D) (shift D a) v
  let bj := shiftedIntercept (D.line j) (mesh D) (shift D a) v
  have hNr : (0:ℝ)<Nc := by exact_mod_cast hNc
  have hFr : (0:ℝ)<Nf := by exact_mod_cast hNf
  have hNcRho : (Nc:ℝ)*rho ≤ 64 := by
    dsimp only [rho]
    rw [mul_div_assoc]
    apply (div_le_iff₀ hFr).mpr
    have hh : (Nc:ℝ) ≤ Nf := by exact_mod_cast hcf
    nlinarith only [hh]
  have hDist : dist (cellCenter (mesh D) k) (cellCenter (mesh D) l) ≤ 256/(Nf:ℝ) := by
    have hh := dist_triangle (cellCenter (mesh D) k) center (cellCenter (mesh D) l)
    rw [dist_comm center] at hh
    linarith only [hh,hkBall,hlBall]
  have hCoord (w : Fin 4) : |cellCenter (mesh D) k w-cellCenter (mesh D) l w| ≤ 256/(Nf:ℝ) := by
    exact (show _ ≤ dist (cellCenter (mesh D) k) (cellCenter (mesh D) l) by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (cellCenter (mesh D) k) (cellCenter (mesh D) l) w).trans hDist
  have hX : |x.1 v-y.1 v| ≤ rho := by
    have he : x.1 v-y.1 v=(cellCenter (mesh D) k v.castSucc-cellCenter (mesh D) l v.castSucc)/4 := by
      dsimp [x,y,ShearBinFibers.oldCenter,chartIndex,cellCenter]
      ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
    exact (div_le_div_of_nonneg_right (hCoord v.castSucc) (by norm_num)).trans_eq (by dsimp only [rho]; ring)
  have hT : |x.2-y.2| ≤ rho := by
    have he : x.2-y.2=(cellCenter (mesh D) k 3-cellCenter (mesh D) l 3)/4 := by
      dsimp only [x,y]
      rw [chart_center_time,chart_center_time]
      ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
    exact (div_le_div_of_nonneg_right (hCoord 3) (by norm_num)).trans_eq (by dsimp only [rho]; ring)
  have hXi := original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)
  have hYj := original_cell_bounds h original horiginal a ha ((mem_incidences original j l).mpr hl)
  have hri : |x.1 v-bi-si*x.2| ≤ 3*D.thickness/2 := by
    have hh := hXi.2 v
    change |_ - _ - _| ≤ 12*(D.thickness/2/4) at hh
    convert hh using 1 <;> ring
  have hrj : |y.1 v-bj-sj*y.2| ≤ 3*D.thickness/2 := by
    have hh := hYj.2 v
    change |_ - _ - _| ≤ 12*(D.thickness/2/4) at hh
    convert hh using 1 <;> ring
  have hsi : |si-sj| ≤ 1/(Nc:ℝ) :=
    same_floor_mul_close _ _ Nc hNc (congrFun hAngle v)
  have hsj : |sj| ≤ 2 := slope_bound (D.line j) (h.1.2.2.2.2.1 j) (h.2.1.1 j) v
  have hA : |(si-sj)*x.2| ≤ 1/(Nc:ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul hsi hXi.1 (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hB : |sj*(x.2-y.2)| ≤ 2*rho := by
    rw [abs_mul]
    exact mul_le_mul hsj hT (abs_nonneg _) (by norm_num)
  have he : bi-bj=(x.1 v-y.1 v)-(si-sj)*x.2-sj*(x.2-y.2)-
      (x.1 v-bi-si*x.2)+(y.1 v-bj-sj*y.2) := by ring
  have hSum : |bi-bj| ≤ 3*D.thickness+3*rho+1/(Nc:ℝ) := by
    rw [he]
    have h1 := abs_sub (x.1 v-y.1 v) ((si-sj)*x.2)
    have h2 := abs_sub ((x.1 v-y.1 v)-(si-sj)*x.2) (sj*(x.2-y.2))
    have h3 := abs_sub ((x.1 v-y.1 v)-(si-sj)*x.2-sj*(x.2-y.2)) (x.1 v-bi-si*x.2)
    have h4 := abs_add_le ((x.1 v-y.1 v)-(si-sj)*x.2-sj*(x.2-y.2)-(x.1 v-bi-si*x.2))
      (y.1 v-bj-sj*y.2)
    linarith only [h1,h2,h3,h4,hX,hA,hB,hri,hrj]
  have hMul := mul_le_mul_of_nonneg_left hSum hNr.le
  have hInv : (Nc:ℝ)*(1/(Nc:ℝ))=1 := by field_simp [hNr.ne']
  change |(Nc:ℝ)*bi-(Nc:ℝ)*bj| ≤ 196
  rw [←mul_sub,abs_mul,abs_of_pos hNr]
  have heq : (Nc:ℝ)*(3*D.thickness+3*rho+1/(Nc:ℝ))=
      3*((Nc:ℝ)*D.thickness)+3*((Nc:ℝ)*rho)+1 := by rw [mul_add,mul_add,hInv]; ring
  exact hMul.trans (by rw [heq]; linarith only [hscale,hNcRho])

/-- A fixed coarse slope cell through an actual native fine physical cube
has at most393^3 full ORIGINAL parameter parents, uniformly in both scales. -/
theorem native_cube_slope_cell_parent_cap {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Nc Nf : ℕ) (hNc : 0<Nc) (hNf : 0<Nf) (hcf : Nc ≤ Nf)
    (hscale : (Nc:ℝ)*D.thickness ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (center : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) center ≤ 128/(Nf:ℝ))
    (angle : Fin 3 → ℤ) (hAngle : ∀z∈E,(parentLabel D a Nc z.1).1=angle) :
    (E.image (fun z => parentLabel D a Nc z.1)).card ≤ 393^3 := by
  by_cases hEn : E.Nonempty
  · obtain ⟨z0,hz0⟩ := hEn
    let box : Finset Parent := {angle} ×ˢ vectorBox (parentLabel D a Nc z0.1).2 196
    have hSub : E.image (fun z => parentLabel D a Nc z.1)⊆box := by
      intro q hq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
      apply mem_product.mpr
      refine ⟨mem_singleton.mpr (hAngle z hz),?_⟩
      apply Fintype.mem_piFinset.mpr
      intro v
      have hh := native_cube_intercept_spread h original horiginal ha Nc Nf hNc hNf hcf hscale
        z.1 z0.1 z.2 z0.2 ((mem_incidences original _ _).mp (hE hz))
        ((mem_incidences original _ _).mp (hE hz0)) center (hBall z hz) (hBall z0 hz0)
        ((hAngle z hz).trans (hAngle z0 hz0).symm) v
      exact floor_mem_interval 196 hh
    exact (card_le_card hSub).trans_eq (by simp only [box,card_product,card_singleton,one_mul,vectorBox_card])
  · simp only [not_nonempty_iff_eq_empty.mp hEn,image_empty,card_empty]
    positivity

/-- A genuine coarse slope ball is covered by a fixed number of coarse
slope cells, each of which has the preceding SOURCE-DERIVED phase cap. -/
theorem native_cube_angle_ball_parent_cap {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (Nc Nf : ℕ) (hNc : 0<Nc) (hNf : 0<Nf) (hcf : Nc ≤ Nf)
    (hscale : (Nc:ℝ)*D.thickness ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (center : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) center ≤ 128/(Nf:ℝ))
    (angularCenter : Fin 3 → ℝ) (radius : ℕ)
    (hAngle : ∀z∈E,∀v : Fin 3,|(Nc:ℝ)*slope (D.line z.1) v-angularCenter v| ≤ radius) :
    ((E.image (fun z => parentLabel D a Nc z.1)).card:ℝ) ≤
      ((393^3:ℕ):ℝ)*(((2*radius+1)^3:ℕ):ℝ) := by
  let angle := fun z : Fin n × Index => (parentLabel D a Nc z.1).1
  have hSub : E.image angle⊆vectorBox (fun v => ⌊angularCenter v⌋) radius := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    apply Fintype.mem_piFinset.mpr
    intro v
    exact floor_mem_interval radius (hAngle z hz v)
  have hAngles : ((E.image angle).card:ℝ) ≤ (((2*radius+1)^3:ℕ):ℝ) := by
    exact_mod_cast (card_le_card hSub).trans_eq (vectorBox_card _ radius)
  have hEach : ∀q∈E.image angle,
      (((E.filter (fun z => angle z=q)).image (fun z => parentLabel D a Nc z.1)).card:ℝ) ≤ ((393^3:ℕ):ℝ) := by
    intro q _hq
    exact_mod_cast native_cube_slope_cell_parent_cap h original horiginal ha Nc Nf hNc hNf hcf hscale
      (E.filter (fun z => angle z=q)) ((filter_subset _ _).trans hE) center
      (fun z hz => hBall z (mem_filter.mp hz).1) q (fun z hz => (mem_filter.mp hz).2)
  have hh := image_card_le_real_mul_of_fiber_images E (fun z => parentLabel D a Nc z.1) angle
    ((393^3:ℕ):ℝ) hEach
  exact hh.trans (mul_le_mul_of_nonneg_left hAngles (Nat.cast_nonneg _))

open NativeGenericReferenceData NativeOriginalParentDensityCore NativeLiteralReferenceShadowCubeDraft2150

/-- Complete literal-S conditional angular count at the prepared scales:
actual native cube + actual coarse slope ball -> fine original parent
labels, using stored GLOBAL conditional shadow means and the finite menu.
The exponent is kappa at the real query scale ratio; there is no parent
renormalization and no inherited lower-profile premise. -/
theorem reference_native_cube_angle_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (i j : Fin (g+1)) (hij : (ref.schedule i).val ≤ (ref.schedule j).val)
    (E : Finset (Fin n × Index)) (hE : E⊆ref.E1) (center : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) center ≤ 128/((2^(ref.schedule j).val:ℕ):ℝ))
    (angularCenter : Fin 3 → ℝ) (radius : ℕ)
    (hAngle : ∀z∈E,∀v : Fin 3,
      |((2^(ref.schedule i).val:ℕ):ℝ)*slope (D.line z.1) v-angularCenter v| ≤ radius) :
    ((E.image (fun z => parentLabel D ref.a (2^(ref.schedule j).val) z.1)).card:ℝ) ≤
      (625*((393^3:ℕ):ℝ)*(((2*radius+1)^3:ℕ):ℝ))*(coreRadix ref.original ref.R L:ℝ)^4*
        D.thickness^(-tau)*
        ((64/((2^(ref.schedule j).val:ℕ):ℝ))/(64/((2^(ref.schedule i).val:ℕ):ℝ)))^
          (-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  let coarse := fun z : Fin n × Index => parentLabel D ref.a (2^(ref.schedule i).val) z.1
  let fine := fun z : Fin n × Index => parentLabel D ref.a (2^(ref.schedule j).val) z.1
  let bound : ℝ := 625*(coreRadix ref.original ref.R L:ℝ)^4*D.thickness^(-tau)*
    ((64/((2^(ref.schedule j).val:ℕ):ℝ))/(64/((2^(ref.schedule i).val:ℕ):ℝ)))^
      (-NativeFixedCompactKakeyaExponent.extremalExponent)
  have hBound : 0 ≤ bound := by have hd := h.1.2.1; dsimp only [bound]; positivity
  have hEach : ∀p∈E.image coarse,(((E.filter (fun z => coarse z=p)).image fine).card:ℝ) ≤ bound := by
    intro p hp
    obtain ⟨z,hz,hzp⟩ := mem_image.mp hp
    have hParent : (parentEdges D ref.a (2^(ref.schedule i).val) ref.E1 p).Nonempty :=
      ⟨z,mem_filter.mpr ⟨hE hz,hzp⟩⟩
    exact reference_native_ball_conditional_parent_upper ref i j hij p hParent
      (E.filter (fun z => coarse z=p))
      (fun z hz => mem_filter.mpr ⟨hE (mem_filter.mp hz).1,(mem_filter.mp hz).2⟩)
      center (fun z hz => hBall z (mem_filter.mp hz).1)
  have hCount := image_card_le_real_mul_of_fiber_images E fine coarse bound hEach
  have hscale : ((2^(ref.schedule i).val:ℕ):ℝ)*D.thickness ≤ 1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale ref.backbone.2.1 (ref.schedule i)
  have hcf : 2^(ref.schedule i).val ≤ (2^(ref.schedule j).val:ℕ) :=
    Nat.pow_le_pow_right (by norm_num) hij
  have hParents := native_cube_angle_ball_parent_cap h ref.original ref.backbone.1 ref.backbone.2.2.1
    (2^(ref.schedule i).val) (2^(ref.schedule j).val) (by positivity) (by positivity) hcf hscale
    E (hE.trans (ref.core.1.trans (filter_subset _ _))) center hBall angularCenter radius hAngle
  have hh := hCount.trans (mul_le_mul_of_nonneg_left hParents hBound)
  simpa only [bound,mul_assoc,mul_comm,mul_left_comm] using hh

end NativeLiteralCubeAnglePhaseMenuDraft2159
