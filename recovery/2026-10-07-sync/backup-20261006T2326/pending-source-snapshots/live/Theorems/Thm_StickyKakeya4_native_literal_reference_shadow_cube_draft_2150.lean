/- UNVERIFIED literal native-source cube -> actual GLOBAL shadow transfer.
The source mesh is always D.thickness; the physical cube and coarse shadow
are query objects only. No second parent-normalized source is introduced.
The only uniformities concern the actual physicalPair/physicalPoint maps
already installed by the mandatory relationMenu on the same Reference.
-/
import Theorems.Thm_StickyKakeya4_native_physical_reference_data
import Theorems.Thm_StickyKakeya4_native_higher_quotient_parent_transport
import Theorems.Thm_StickyKakeya4_native_quantized_line_packets
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
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
