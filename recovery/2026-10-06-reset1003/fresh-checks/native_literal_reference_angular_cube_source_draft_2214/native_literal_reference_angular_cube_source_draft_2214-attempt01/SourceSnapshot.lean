/- UNVERIFIED actual literal-Reference angular cube source,13 declarations.
Combined cube9 and unit-direction/off-menu readers4, preserving original
unit hashes. No source rotation, parent renormalization, desired geometric
upper, native-output assumption, or lower AD profile is introduced.
-/
import Theorems.Thm_StickyKakeya4_native_physical_reference_data
import Theorems.Thm_StickyKakeya4_native_higher_quotient_parent_transport
import Theorems.Thm_StickyKakeya4_native_quantized_line_packets
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
import Theorems.Thm_StickyKakeya4_native_common_direction_phase_menu
import Theorems.Thm_StickyKakeya4_native_angular_dyadic_interpolation
import Theorems.Thm_StickyKakeya4_native_unit_parent_directions

/- UNVERIFIED literal native-source angular cube transfer,9 declarations.
Source geometric membership gives625 actual global-shadow point labels per
native cube and393^3 full phase parents per coarse slope cell. Reference
physical uniformities/balanced global mean, or its stored conditional maps
and two-scale means, yield the actual prepared-scale angular cube uppers.
Every graph uses the original source thicknesssigma=D.thickness. Query
charts are not new admitted sources. No global sigma degree is substituted
for a parent-normalized degree, and no lower AD is assumed or claimed.
-/

/- Frozen source unit Thm_StickyKakeya4_native_literal_reference_shadow_cube_draft_2150.lean; SHA256 43f0aa7015d27b9f465195903a1dfda6b3c7b77a2a656cf3cbee8f31fff28481 -/
/- UNVERIFIED literal native-source cube -> actual GLOBAL shadow transfer.
The source mesh is always D.thickness; the physical cube and coarse shadow
are query objects only. No second parent-normalized source is introduced.
The only uniformities concern the actual physicalPair/physicalPoint maps
already installed by the mandatory relationMenu on the same Reference.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeLiteralReferenceShadowCubeDraft2150
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeCoarsePointMultiplicity NativeCoarseShadingCapacity
open NativeJointUniformCoarseRelations NativeGenericReferenceData NativePhysicalReferenceData
open NativeCubicalDiameterCount NativeQuantizedLinePackets NativeOriginalParentDensityCore
open NativeIncidenceMultiplicityTower NativeTangentGridCoarsening

/-- The zero-parent map appearing in the GLOBAL shadow is a fixed affine
contraction. It is not the rank-stop anisotropic parent map. -/
lemma zero_parent_coordinate_difference {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (x y : E4) (v : Fin 4) :
    NativeLocalParentPhysicalMap.physicalMap D a 1 (0,0) x v-
      NativeLocalParentPhysicalMap.physicalMap D a 1 (0,0) y v=(x v-y v)/512 := by
  refine Fin.lastCases ?_ (fun j => ?_) v
  · rw [NativeHigherQuotientParentTransport.physical_height,
      NativeHigherQuotientParentTransport.physical_height]
    ring
  · rw [NativeHigherQuotientParentTransport.physical_coordinate,
      NativeHigherQuotientParentTransport.physical_coordinate]
    simp only [Nat.cast_one,one_mul,Pi.zero_apply,Int.cast_zero,zero_mul,mul_zero,sub_zero]
    ring

/-- All incidences whose ORIGINAL native cell centers lie in a radius2R
ball have at most625 actual GLOBAL coarse shadow point labels at R=64/2^m.
This is a whole physical-cube statement, not just a fixed original point. -/
theorem actual_shadow_support_in_native_ball {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (hR : ∀z∈E,z.1∈R)
    (x : E4) (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) x ≤ 128/((2^m:ℕ):ℝ)) :
    (E.image (physicalPoint h R a level m)).card ≤ 625 := by
  let N := 2^m
  let e : ℝ := 32/(N:ℝ)
  let rep := NativeCoarseDirectionThinning.representative h R a N
  let center := NativeLocalParentPhysicalMap.physicalMap D a 1 (0,0) x
  have hN : 0<N := by dsimp only [N]; positivity
  have he : 0<e := by dsimp only [e]; positivity
  have hscale : (N:ℝ)*D.thickness ≤ 1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨m,by omega⟩
  have hmesh := NativeCoarseDyadicShading.block_mesh hdy hm
  have hSub : E.image (physicalPoint h R a level m)⊆
      indexBox (wzDyadicCellIndex e center) 2 := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    have hOrig := (mem_incidences original z.1 z.2).mp (hE hz)
    have hRep : parentLabel D a N (rep (parentLabel D a N z.1))=parentLabel D a N z.1 :=
      (NativeCoarseDirectionThinning.representative_spec h R a N
        (mem_image_of_mem _ (hR z hz))).2
    apply Fintype.mem_piFinset.mpr
    intro v
    have hProj := projected_front_near_physical h original horiginal ha N hN hscale
      z.1 (rep (parentLabel D a N z.1)) z.2 hOrig hRep v
    have hNative : |cellCenter (mesh D) z.2 v-x v| ≤ 4*e := by
      have hh : |cellCenter (mesh D) z.2 v-x v| ≤ dist (cellCenter (mesh D) z.2) x := by
        simpa only [Real.dist_eq] using PiLp.dist_apply_le (cellCenter (mesh D) z.2) x v
      exact (hh.trans (hBall z hz)).trans_eq (by dsimp only [e,N]; ring)
    have hMove : |NativeLocalParentPhysicalMap.physicalMap D a 1 (0,0)
        (cellCenter (mesh D) z.2) v-center v| ≤ (4*e)/512 := by
      rw [zero_parent_coordinate_difference,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
      exact div_le_div_of_nonneg_right hNative (by norm_num)
    have hTri := abs_sub_le
      (NativeOriginalPaddedCells.frontPoint D a (0,0) (rep (parentLabel D a N z.1)) z.2 v)
      (NativeLocalParentPhysicalMap.physicalMap D a 1 (0,0) (cellCenter (mesh D) z.2) v) (center v)
    have hClose : |NativeOriginalPaddedCells.frontPoint D a (0,0)
        (rep (parentLabel D a N z.1)) z.2 v-center v| ≤ 2*e := by
      change |_ - _| ≤ (3/2:ℝ)*e at hProj
      linarith only [hProj,hMove,hTri,he]
    have hFloor := floor_mem_interval (x:=NativeOriginalPaddedCells.frontPoint D a (0,0)
        (rep (parentLabel D a N z.1)) z.2 v/e) (y:=center v/e) 2 (by
      rw [←sub_div,abs_div,abs_of_pos he]
      exact (div_le_iff₀ he).mpr hClose)
    change ⌊NativeOriginalPaddedCells.frontPoint D a (0,0)
        (rep (parentLabel D a N z.1)) z.2 v/
        (((NativeCoarseDyadicShading.block level m:ℕ):ℝ)*D.thickness/128)⌋∈_
    rw [hmesh]
    exact hFloor
  exact (card_le_card hSub).trans_eq (by rw [indexBox_card]; norm_num)

/-- Convert native-cube support and actual image-degree comparability into
occupied ORIGINAL tube-parent count. The final Reference readers below
supply the mean from their stored balanced fields. -/
theorem native_ball_parent_count_of_uniformity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level)
    (Ecore E : Finset (Fin n × Index)) (hCore : Ecore⊆incidences original)
    (hR : ∀z∈Ecore,z.1∈R) (hE : E⊆Ecore) (Q : ℕ)
    (Hpair : HasUniformFibers Ecore Q (physicalPair h R a level m))
    (Hpoint : HasUniformFibers Ecore Q (physicalPoint h R a level m))
    (B : ℝ) (hB : 0 ≤ B)
    (hMean : multiplicity (Ecore.image (physicalPair h R a level m)) ≤ B)
    (x : E4) (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) x ≤ 128/((2^m:ℕ):ℝ)) :
    ((E.image (fun z => parentLabel D a (2^m) z.1)).card:ℝ) ≤ 625*(Q:ℝ)^4*B := by
  let F := E.image (physicalPair h R a level m)
  have hF : F⊆Ecore.image (physicalPair h R a level m) := image_subset_image hE
  have hEach : ∀k∈F.image Prod.snd,(((F.filter (fun z => z.2=k)).image id).card:ℝ) ≤ (Q:ℝ)^4*B := by
    intro k _hk
    have hu := NativeCoarseUniformImageDegrees.image_point_degree_le_multiplicity
      Ecore (physicalPair h R a level m) (Q^2) (Q^2) Hpair Hpoint k
    have hu' : (((Ecore.image (physicalPair h R a level m)).filter (fun z => z.2=k)).card:ℝ) ≤
        (Q:ℝ)^4*multiplicity (Ecore.image (physicalPair h R a level m)) := by
      convert hu using 1 <;> push_cast <;> ring
    have hc : ((F.filter (fun z => z.2=k)).card:ℝ) ≤
        (((Ecore.image (physicalPair h R a level m)).filter (fun z => z.2=k)).card:ℝ) :=
      Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hF))
    simpa only [image_id] using hc.trans (hu'.trans (mul_le_mul_of_nonneg_left hMean (by positivity)))
  have hCount := image_card_le_real_mul_of_fiber_images F id Prod.snd ((Q:ℝ)^4*B) hEach
  simp only [image_id] at hCount
  have hPoint : F.image Prod.snd=E.image (physicalPoint h R a level m) := by
    dsimp only [F]
    rw [image_image]
    rfl
  have hSupport : ((F.image Prod.snd).card:ℝ) ≤ 625 := by
    rw [hPoint]
    exact_mod_cast actual_shadow_support_in_native_ball h original horiginal ha R level m hdy hm
      E (hE.trans hCore) (fun z hz => hR z (hE hz)) x hBall
  have hParents : ((E.image (fun z => parentLabel D a (2^m) z.1)).card:ℝ) ≤ F.card := by
    have he : F.image Prod.fst=E.image (fun z => parentLabel D a (2^m) z.1) := by
      dsimp only [F]
      rw [image_image]
      rfl
    rw [←he]
    exact_mod_cast card_image_le
  exact (hParents.trans hCount).trans ((mul_le_mul_of_nonneg_left hSupport
    (mul_nonneg (by positivity) hB)).trans_eq (by ring))

/-- The GLOBAL balanced shadow mean of this SAME literal Reference bounds
all its retained incidences in one native physical cube. No parent source
or normalized parent point-degree upper is invoked. -/
theorem reference_native_ball_parent_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (Hphysical : HasPhysicalUniformities ref) (j : Fin (g+1))
    (E : Finset (Fin n × Index)) (hE : E⊆ref.E1) (x : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) x ≤ 128/((2^(ref.schedule j).val:ℕ):ℝ)) :
    ((E.image (fun z => parentLabel D ref.a (2^(ref.schedule j).val) z.1)).card:ℝ) ≤
      625*(coreRadix ref.original ref.R L:ℝ)^4*D.thickness^(-seed)*
        (64/((2^(ref.schedule j).val:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  have hR : ∀z∈ref.E1,z.1∈ref.R := fun z hz => (mem_filter.mp (ref.core.1 hz)).2
  have hMean := (ref.scales j).2.2.1
  rw [full_source_multiplicity_real h ref.R ref.a ref.level (ref.schedule j).val ref.E1 hR] at hMean
  have hM : multiplicity (ref.E1.image (physicalPair h ref.R ref.a ref.level (ref.schedule j).val)) ≤
      D.thickness^(-seed)*(64/((2^(ref.schedule j).val:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent) := hMean
  have hh := native_ball_parent_count_of_uniformity h ref.original ref.backbone.1 ref.backbone.2.2.1
    ref.R ref.level (ref.schedule j).val ref.backbone.2.1 (Nat.le_of_lt_succ (ref.schedule j).isLt)
    ref.E1 E (ref.core.1.trans (filter_subset _ _)) hR hE (coreRadix ref.original ref.R L)
    (Hphysical j).1 (Hphysical j).2 _ (by positivity) hM x hBall
  simpa only [mul_assoc] using hh

/-- At a coarse ORIGINAL parameter parent, ref.pairs bounds the fine GLOBAL
shadow image on the same E1. Native spatial cubes stay at their original
locations; the bound involves the actual coarse/fine angular ratio only. -/
theorem reference_native_ball_conditional_parent_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (i j : Fin (g+1)) (hij : (ref.schedule i).val ≤ (ref.schedule j).val)
    (p : Parent) (hp : (parentEdges D ref.a (2^(ref.schedule i).val) ref.E1 p).Nonempty)
    (E : Finset (Fin n × Index))
    (hE : E⊆parentEdges D ref.a (2^(ref.schedule i).val) ref.E1 p) (x : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) x ≤ 128/((2^(ref.schedule j).val:ℕ):ℝ)) :
    ((E.image (fun z => parentLabel D ref.a (2^(ref.schedule j).val) z.1)).card:ℝ) ≤
      625*(coreRadix ref.original ref.R L:ℝ)^4*D.thickness^(-tau)*
        ((64/((2^(ref.schedule j).val:ℕ):ℝ))/(64/((2^(ref.schedule i).val:ℕ):ℝ)))^
          (-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  let Ep := parentEdges D ref.a (2^(ref.schedule i).val) ref.E1 p
  have hR : ∀z∈Ep,z.1∈ref.R := fun z hz => (mem_filter.mp (ref.core.1 (mem_filter.mp hz).1)).2
  have Hpair : HasUniformFibers Ep (coreRadix ref.original ref.R L)
      (physicalPair h ref.R ref.a ref.level (ref.schedule j).val) :=
    conditioned_uniformity ref.E1
      (fun z : Fin n × Index => parentLabel D ref.a (2^(ref.schedule i).val) z.1)
      _ _ (ref.conditioned i j).1 p
  have Hpoint : HasUniformFibers Ep (coreRadix ref.original ref.R L)
      (physicalPoint h ref.R ref.a ref.level (ref.schedule j).val) :=
    conditioned_uniformity ref.E1
      (fun z : Fin n × Index => parentLabel D ref.a (2^(ref.schedule i).val) z.1)
      _ _ (ref.conditioned i j).2 p
  have hMean := (ref.pairs (ref.schedule i).val (ref.schedule j).val hij
    (Nat.le_of_lt_succ (ref.schedule j).isLt) p hp).2
  rw [full_source_multiplicity_real h ref.R ref.a ref.level (ref.schedule j).val Ep hR] at hMean
  have hM : multiplicity (Ep.image (physicalPair h ref.R ref.a ref.level (ref.schedule j).val)) ≤
      D.thickness^(-tau)*
        ((64/((2^(ref.schedule j).val:ℕ):ℝ))/(64/((2^(ref.schedule i).val:ℕ):ℝ)))^
          (-NativeFixedCompactKakeyaExponent.extremalExponent) := hMean
  have hh := native_ball_parent_count_of_uniformity h ref.original ref.backbone.1 ref.backbone.2.2.1
    ref.R ref.level (ref.schedule j).val ref.backbone.2.1 (Nat.le_of_lt_succ (ref.schedule j).isLt)
    Ep E ((filter_subset _ _).trans (ref.core.1.trans (filter_subset _ _))) hR hE
    (coreRadix ref.original ref.R L) Hpair Hpoint _ (by positivity) hM x hBall
  simpa only [mul_assoc] using hh

end NativeLiteralReferenceShadowCubeDraft2150
end -- explicit anonymous source-unit section

/- Frozen source unit Thm_StickyKakeya4_native_literal_cube_angle_phase_menu_draft_2159.lean; SHA256 4c81dc509cff7467993fe5ac68f543bef175a99563c38f683cede90672e94d15 -/
/- UNVERIFIED literal native-cube/coarse-angle phase menu.
No parent source, mesh change, or source-dependent occupancy tax is used.
All scalar errors below come from actual original cell shading membership.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
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
end -- explicit anonymous source-unit section

/- Reader source unit Thm_StickyKakeya4_native_literal_cube_unit_angular_readback_draft_2212.lean; SHA256 c1ff75564309e606da30b576b23b5d0cf69ef8b9ea955fb302b5e81686f82b05 -/

/- UNVERIFIED source-facing readers for the literal Reference cube estimate.
Actual unit-direction balls replace a supplied coordinate slope-bin bound.
The existing angularCell at N=1,p=0 is only a query on the original slopes.
Its exact dyadic descendants account for every omitted fine query depth.
No native source, point alphabet, or incidence graph is changed.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeLiteralCubeUnitAngularReadbackDraft2212
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeGenericReferenceData NativeOriginalParentDensityCore
open NativeLiteralCubeAnglePhaseMenuDraft2159 NativeNormalizedCellAngularMenu
open NativeAngularDyadicInterpolation NativeLocalParentGeometry

/-- The angular query at N=1 and zero parent is the actual original slope
grid, coarsened by eight. This identity makes no parent-membership claim. -/
lemma literal_angular_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (M : ℕ) (i : Fin n) :
    angularCell D 1 M (0,0) i=(fun v => (parentLabel D a M i).1 v/8) := by
  funext v
  change ⌊((M:ℝ)*((1:ℝ)*slope (D.line i) v-(0:ℝ)))/8⌋=
    ⌊(M:ℝ)*slope (D.line i) v⌋/8
  simp only [one_mul,sub_zero]
  have hh := Int.floor_div_natCast ((M:ℝ)*slope (D.line i) v) 8
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

/-- Angular labels are an exact image of the occupied full original
parameter labels, so their count needs no extra source or geometric loss. -/
lemma literal_angular_count_le {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (M : ℕ) (E : Finset (Fin n × Index)) :
    (E.image (fun z => angularCell D 1 M (0,0) z.1)).card ≤
      (E.image (fun z => parentLabel D a M z.1)).card := by
  have he : E.image (fun z => angularCell D 1 M (0,0) z.1)=
      (E.image (fun z => parentLabel D a M z.1)).image (fun p => fun v => p.1 v/8) := by
    rw [image_image]
    congr 1
    funext z
    exact literal_angular_readback D a M z.1
  rw [he]
  exact card_image_le

/-- A physical source cube and a genuine ambient unit-direction ball give
the prepared-scale count. The arbitrary ball center is removed using one
occupied witness; native direction-to-slope control gives the fixed768
coordinate margin, hence1537^3 coarse angular cells. -/
theorem reference_native_cube_unit_ball_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (i j : Fin (g+1)) (hij : (ref.schedule i).val ≤ (ref.schedule j).val)
    (E : Finset (Fin n × Index)) (hE : E⊆ref.E1) (center directionCenter : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) center ≤
      128/((2^(ref.schedule j).val:ℕ):ℝ))
    (hAngle : ∀z∈E,dist (direction (D.line z.1)) directionCenter ≤
      64/((2^(ref.schedule i).val:ℕ):ℝ)) :
    ((E.image (fun z => parentLabel D ref.a (2^(ref.schedule j).val) z.1)).card:ℝ) ≤
      (625*((393^3:ℕ):ℝ)*((1537^3:ℕ):ℝ))*(coreRadix ref.original ref.R L:ℝ)^4*
        D.thickness^(-tau)*
        ((64/((2^(ref.schedule j).val:ℕ):ℝ))/(64/((2^(ref.schedule i).val:ℕ):ℝ)))^
          (-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  have hd := h.1.2.1
  by_cases hEn : E.Nonempty
  · obtain ⟨z0,hz0⟩ := hEn
    let N : ℕ := 2^(ref.schedule i).val
    have hNr : (0:ℝ)<N := by dsimp only [N]; positivity
    have hSlope : ∀z∈E,∀v : Fin 3,
        |(N:ℝ)*slope (D.line z.1) v-(N:ℝ)*slope (D.line z0.1) v| ≤ (768:ℕ) := by
      intro z hz v
      have hdist : dist (direction (D.line z.1)) (direction (D.line z0.1)) ≤
          2*(64/(N:ℝ)) := by
        calc
          _ ≤ dist (direction (D.line z.1)) directionCenter+
              dist directionCenter (direction (D.line z0.1)) := dist_triangle _ _ _
          _ ≤ 64/(N:ℝ)+64/(N:ℝ) :=
            add_le_add (hAngle z hz) (by simpa only [dist_comm] using hAngle z0 hz0)
          _ = _ := by ring
      have hs := (NativeUnitParentDirections.slope_sub_le_direction_dist
        (D.line z.1) (D.line z0.1) (h.1.2.2.2.2.1 z0.1) (h.2.1.1 z.1) (h.2.1.1 z0.1) v).trans
          (mul_le_mul_of_nonneg_left hdist (by norm_num))
      calc
        _ = (N:ℝ)*|slope (D.line z.1) v-slope (D.line z0.1) v| := by
          rw [←mul_sub,abs_mul,abs_of_pos hNr]
        _ ≤ (N:ℝ)*(6*(2*(64/(N:ℝ)))) := mul_le_mul_of_nonneg_left hs hNr.le
        _ = _ := by field_simp; ring
    have hh := reference_native_cube_angle_upper ref i j hij E hE center hBall
      (fun v => (N:ℝ)*slope (D.line z0.1) v) 768 hSlope
    norm_num only [Nat.reduceMul,Nat.reduceAdd] at hh
    exact hh
  · rw [not_nonempty_iff_eq_empty.mp hEn,image_empty,card_empty,Nat.cast_zero]
    positivity

/-- Every finer dyadic angular query is read from the same prepared cube
estimate with its exact3-dimensional descendant cost. Source cube centers
and unit directions remain literal; sigma is still D.thickness. -/
theorem reference_off_menu_cube_angular_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ} (ref : Reference h tau htau seed e zeta L g)
    (i j : Fin (g+1)) (hij : (ref.schedule i).val ≤ (ref.schedule j).val)
    (s : ℕ) (hjs : (ref.schedule j).val ≤ s)
    (E : Finset (Fin n × Index)) (hE : E⊆ref.E1) (center directionCenter : E4)
    (hBall : ∀z∈E,dist (cellCenter (mesh D) z.2) center ≤ 128/((2^s:ℕ):ℝ))
    (hAngle : ∀z∈E,dist (direction (D.line z.1)) directionCenter ≤
      64/((2^(ref.schedule i).val:ℕ):ℝ)) :
    ((E.image (fun z => angularCell D 1 (2^s) (0,0) z.1)).card:ℝ) ≤
      (((2^(s-(ref.schedule j).val))^3:ℕ):ℝ)*
        (625*((393^3:ℕ):ℝ)*((1537^3:ℕ):ℝ))*(coreRadix ref.original ref.R L:ℝ)^4*
          D.thickness^(-tau)*
          ((64/((2^(ref.schedule j).val:ℕ):ℝ))/(64/((2^(ref.schedule i).val:ℕ):ℝ)))^
            (-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  have hScale : 128/((2^s:ℕ):ℝ) ≤ 128/((2^(ref.schedule j).val:ℕ):ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) hjs
  have hParent := reference_native_cube_unit_ball_upper ref i j hij E hE center directionCenter
    (fun z hz => (hBall z hz).trans hScale) hAngle
  have hAngular : ((E.image (fun z => angularCell D 1 (2^(ref.schedule j).val) (0,0) z.1)).card:ℝ) ≤
      ((E.image (fun z => parentLabel D ref.a (2^(ref.schedule j).val) z.1)).card:ℝ) := by
    exact_mod_cast literal_angular_count_le D ref.a (2^(ref.schedule j).val) E
  have hInterp := angular_image_interpolation D 1 (0,0) E hjs
  exact hInterp.trans ((mul_le_mul_of_nonneg_left (hAngular.trans hParent)
    (Nat.cast_nonneg _)).trans_eq (by ring))

end NativeLiteralCubeUnitAngularReadbackDraft2212

end -- explicit reader source-unit anonymous section
