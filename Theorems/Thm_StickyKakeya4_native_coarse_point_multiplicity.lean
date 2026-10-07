import Theorems.Thm_StickyKakeya4_native_local_cell_coherence
import Theorems.Thm_StickyKakeya4_native_coarse_representative_geometry
import Theorems.Thm_StickyKakeya4_native_incidence_multiplicity_tower
import Theorems.Thm_StickyKakeya4_native_coarse_uniform_image_degrees
import Theorems.Thm_StickyKakeya4_native_point_menu_transfer
import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow
import Theorems.Thm_StickyKakeya4_native_local_parent_scales

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
noncomputable section
namespace NativeCoarsePointMultiplicity
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open NativeOriginalPaddedCells NativeCoarseShadingCapacity NativeUnitParentNormalization
open NativeContractedUnitParent NativeNormalizedParentCarrierMetric
open scoped BigOperators

lemma zero_front_eq_local {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (i : Fin n) (k : Index) :
    frontPoint D a (0,0) i k = NativeLocalParentCells.frontPoint D a 1 (0,0) i k := by
  simp only [frontPoint,NativeLocalParentCells.frontPoint,
    NativeLocalParentGeometry.localIntercept,NativeLocalParentGeometry.localSlope,
    newIntercept,newSlope,Nat.cast_one,one_mul]

lemma same_parent_front_error {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (hN : 0 < N) (i j : Fin n) (k : Index)
    (hp : parentLabel D a N j = parentLabel D a N i) (ht : |oldTime D a k| ≤ 1)
    (v : Fin 4) :
    |frontPoint D a (0,0) j k v-frontPoint D a (0,0) i k v| ≤ (1/(N:ℝ))/64 := by
  refine Fin.lastCases ?_ (fun u => ?_) v
  · rw [show (Fin.last 3:Fin 4)=3 by rfl,frontPoint_height,frontPoint_height,sub_self,abs_zero]
    positivity
  · have hs := same_floor_mul_close (slope (D.line j) u) (slope (D.line i) u) N hN
      (congrFun (congrArg Prod.fst hp) u)
    have hb := same_floor_mul_close (shiftedIntercept (D.line j) (mesh D) (shift D a) u)
      (shiftedIntercept (D.line i) (mesh D) (shift D a) u) N hN
      (congrFun (congrArg Prod.snd hp) u)
    have hm := mul_le_mul ht hs (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    rw [←abs_mul,one_mul] at hm
    have he : frontPoint D a (0,0) j k u.castSucc-frontPoint D a (0,0) i k u.castSucc =
        ((shiftedIntercept (D.line j) (mesh D) (shift D a) u-
          shiftedIntercept (D.line i) (mesh D) (shift D a) u) +
          oldTime D a k*(slope (D.line j) u-slope (D.line i) u))/128 := by
      simp only [frontPoint,contractPoint,ActualSlopeSource.heightPoint_castSucc,
        PiLp.smul_apply,PiLp.add_apply,smul_eq_mul,newIntercept,newSlope]
      simp only [Pi.zero_apply,Int.cast_zero,sub_zero]
      ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<128)]
    have hh := (abs_add_le _ _).trans (add_le_add hb hm)
    linarith

/-- All representative projections of the same old cell lie close to one
common physical cell image, regardless of its occupied original parent. -/
theorem projected_front_near_physical {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (i j : Fin n) (k : Index) (hk : k∈original i)
    (hp : parentLabel D a N j=parentLabel D a N i) (v : Fin 4) :
    |frontPoint D a (0,0) j k v-
      NativeLocalParentPhysicalMap.physicalMap D a 1 (0,0) (cellCenter (mesh D) k) v| ≤
        (3/2:ℝ)*(32/(N:ℝ)) := by
  have ht := (original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)).1
  change |oldTime D a k| ≤ 1 at ht
  have hd := NativeLocalCellCoherence.frontPoint_near_physicalCell h original horiginal ha 1 (0,0) i k hk v
  rw [←zero_front_eq_local] at hd
  norm_num only [Nat.cast_one,one_mul] at hd
  have hf := same_parent_front_error D a N hN i j k hp ht v
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hdN : D.thickness ≤ 1/(N:ℝ) := (le_div_iff₀ hNr).mpr (by simpa only [mul_comm] using hscale)
  have hh := (abs_sub_le (frontPoint D a (0,0) j k v)
    (frontPoint D a (0,0) i k v) _).trans (add_le_add hf hd)
  have hpos : 0 < 1/(N:ℝ) := by positivity
  simp only [div_eq_mul_inv] at hh hdN hpos ⊢
  nlinarith

/-- The actual coarse cell belongs to the fixed 125-cell physical menu. -/
theorem projectedLabel_mem_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (hmesh : (B:ℝ)*D.thickness/128=32/(N:ℝ))
    (i j : Fin n) (k : Index) (hk : k∈original i)
    (hp : parentLabel D a N j=parentLabel D a N i) :
    projectedLabel D a B j k ∈ NativeLocalCellCoherence.neighborBox (32/(N:ℝ))
      (NativeLocalParentPhysicalMap.physicalMap D a 1 (0,0) (cellCenter (mesh D) k)) := by
  unfold projectedLabel
  rw [hmesh]
  apply NativeLocalCellCoherence.cellIndex_mem_neighborBox (by positivity)
  · exact projected_front_near_physical h original horiginal ha N hN hscale i j k hk hp
  · rw [frontPoint_height,NativeLocalCellCoherence.physicalCell_height]

/-- The actual point projection of a literal original incidence. -/
def pointLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N B : ℕ)
    (rep : Parent → Fin n) (z : Fin n × Index) : Index :=
  projectedLabel D a B (rep (parentLabel D a N z.1)) z.2

/-- The SAME E has at most 125 actual coarse point labels over each old cell.
Representatives need only belong to their original parameter parent. -/
theorem original_cell_image_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (hmesh : (B:ℝ)*D.thickness/128=32/(N:ℝ))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hrep : ∀z∈E,parentLabel D a N (rep (parentLabel D a N z.1))=parentLabel D a N z.1)
    (k : Index) :
    ((E.filter (fun z => z.2=k)).image (pointLabel D a N B rep)).card ≤ 125 := by
  rw [←NativeLocalCellCoherence.neighborBox_card (32/(N:ℝ))
    (NativeLocalParentPhysicalMap.physicalMap D a 1 (0,0) (cellCenter (mesh D) k))]
  apply card_le_card
  intro q hq
  obtain ⟨⟨i,l⟩,hz,rfl⟩ := mem_image.mp hq
  obtain ⟨hz,he⟩ := mem_filter.mp hz
  change l=k at he
  subst l
  exact projectedLabel_mem_menu h original horiginal ha N B hN hscale hmesh i _ k
    ((mem_incidences original i k).mp (hE hz)) (hrep (i,k) hz)

/-- Projection of an abstract occupied parent/old-cell pair into its actual
front-meeting coarse cell. Its original parent coordinate is unchanged. -/
def pairProjection {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (B : ℕ)
    (rep : Parent → Fin n) (z : Parent × Index) : Parent × Index :=
  (z.1,projectedLabel D a B (rep z.1) z.2)

lemma abstract_projected_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N B : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) :
    (NativeIncidenceMultiplicityTower.coarse E (parentLabel D a N)).image
      (pairProjection D a B rep) = NativeCoarseShadingCapacity.coarse D a N B rep E := by
  simp only [NativeIncidenceMultiplicityTower.coarse,NativeCoarseShadingCapacity.coarse,
    image_image,Function.comp_def,pairProjection]
  rfl

lemma old_fiber_projected_support {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N B : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (k : Index) :
    (((NativeIncidenceMultiplicityTower.coarse E (parentLabel D a N)).filter
      (fun z => z.2=k)).image (pairProjection D a B rep)).image Prod.snd =
        (E.filter (fun z => z.2=k)).image (pointLabel D a N B rep) := by
  simp only [NativeIncidenceMultiplicityTower.coarse,filter_image,image_image,
    Function.comp_def,pairProjection]
  rfl

/-- The abstract coarse multiplicity is controlled by the ACTUAL coarse
image of the same original E. Uniformity concerns only two relations on E. -/
theorem multiplicity_le_actual {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (hmesh : (B:ℝ)*D.thickness/128=32/(N:ℝ))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hrep : ∀z∈E,parentLabel D a N (rep (parentLabel D a N z.1))=parentLabel D a N z.1)
    (rad : ℕ)
    (hpair : ∀x∈E,∀y∈E,
      (E.filter (fun z => label D a N B rep z=label D a N B rep x)).card ≤
        rad^2*(E.filter (fun z => label D a N B rep z=label D a N B rep y)).card)
    (hpoint : ∀x∈E,∀y∈E,
      (E.filter (fun z => pointLabel D a N B rep z=pointLabel D a N B rep x)).card ≤
        rad^2*(E.filter (fun z => pointLabel D a N B rep z=pointLabel D a N B rep y)).card) :
    NativeIncidenceMultiplicityTower.multiplicity
      (NativeIncidenceMultiplicityTower.coarse E (parentLabel D a N)) ≤
      (125:ℝ)*(rad:ℝ)^4*NativeIncidenceMultiplicityTower.multiplicity
        (NativeCoarseShadingCapacity.coarse D a N B rep E) := by
  let C := NativeCoarseShadingCapacity.coarse D a N B rep E
  let M := (rad:ℝ)^4*NativeIncidenceMultiplicityTower.multiplicity C
  have hM : 0 ≤ M := mul_nonneg (by positivity)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hdegree (q : Index) : ((C.filter (fun z => z.2=q)).card:ℝ) ≤ M := by
    have hh := NativeCoarseUniformImageDegrees.image_point_degree_le_multiplicity
      E (label D a N B rep) (rad^2) (rad^2) hpair hpoint q
    have he : ((rad^2:ℕ):ℝ)*((rad^2:ℕ):ℝ)=(rad:ℝ)^4 := by push_cast; ring
    simpa only [he,M,C,NativeCoarseShadingCapacity.coarse] using hh
  have hh := NativePointMenuTransfer.multiplicity_le_menu_mul_degree
    (NativeIncidenceMultiplicityTower.coarse E (parentLabel D a N))
    (pairProjection D a B rep) 125 M (fun _ _ => rfl)
    (fun k => by
      rw [old_fiber_projected_support]
      exact original_cell_image_card_le h original horiginal ha N B hN hscale hmesh rep E hE hrep k)
    hM (fun q => by rw [abstract_projected_image]; exact hdegree q)
  simpa only [Nat.cast_ofNat,M,mul_assoc] using hh

/-- Reindexing arbitrary coarse rows by the full parent set changes no
occupied parent/cell pair. This applies even to empty-shading parent labels. -/
lemma reindexed_rows_image (P : Finset Parent) (C : Finset (Parent × Index))
    (hC : ∀z∈C,z.1∈P) :
    (incidences (fun i : Fin P.card =>
      (C.filter (fun z => z.1=NativeCoarseCellSource.parentIndex P i)).image Prod.snd)).image
        (fun z => (NativeCoarseCellSource.parentIndex P z.1,z.2)) = C := by
  ext z
  rcases z with ⟨p,k⟩
  constructor
  · intro hz
    obtain ⟨⟨i,l⟩,hi,he⟩ := mem_image.mp hz
    have hc := (mem_incidences _ i l).mp hi
    obtain ⟨⟨q,u⟩,hu,hul⟩ := mem_image.mp hc
    obtain ⟨hu,hq⟩ := mem_filter.mp hu
    have hip : NativeCoarseCellSource.parentIndex P i=p := congrArg Prod.fst he
    have hlk : l=k := congrArg Prod.snd he
    change q=NativeCoarseCellSource.parentIndex P i at hq
    change u=l at hul
    simpa only [hq,hip,hul,hlk] using hu
  · intro hz
    have hp := hC (p,k) hz
    let i : Fin P.card := P.equivFin ⟨p,hp⟩
    have hi : NativeCoarseCellSource.parentIndex P i=p := by
      simp only [NativeCoarseCellSource.parentIndex,i,Equiv.symm_apply_apply]
    refine mem_image.mpr ⟨(i,k),?_,by simp only [hi]⟩
    apply (mem_incidences _ i k).mpr
    exact mem_image.mpr ⟨(p,k),mem_filter.mpr ⟨hz,hi.symm⟩,rfl⟩

/-- Exact physical multiplicity readback for the full actual shadow; no
native input, occupancy, or density condition is imposed on that shadow. -/
theorem full_source_multiplicity_real {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level m : ℕ) (E : Finset (Fin n × Index)) (hR : ∀z∈E,z.1∈R) :
    (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level m E)).toReal =
      NativeIncidenceMultiplicityTower.multiplicity
        (NativeCoarseShadingCapacity.coarse D a (2^m) (NativeCoarseDyadicShading.block level m)
          (NativeCoarseDirectionThinning.representative h R a (2^m)) E) := by
  let P := R.image (parentLabel D a (2^m))
  let C := NativeCoarseShadingCapacity.coarse D a (2^m) (NativeCoarseDyadicShading.block level m)
    (NativeCoarseDirectionThinning.representative h R a (2^m)) E
  let cells : Fin P.card → Finset Index := fun i =>
    (C.filter (fun z => z.1=NativeCoarseCellSource.parentIndex P i)).image Prod.snd
  have himage : (incidences cells).image
      (fun z => (NativeCoarseCellSource.parentIndex P z.1,z.2))=C := by
    apply reindexed_rows_image
    intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    exact mem_image_of_mem _ (hR w hw)
  have hinj : Function.Injective (fun z : Fin P.card × Index =>
      (NativeCoarseCellSource.parentIndex P z.1,z.2)) := by
    intro z w he
    exact Prod.ext (NativeCoarseCellSource.parentIndex_injective P (congrArg Prod.fst he))
      (congrArg (fun t : Parent × Index => t.2) he)
  have hcard : (incidences cells).card=C.card := by
    rw [←himage,card_image_of_injective _ hinj]
  have hsupport : support cells=C.image Prod.snd := by
    rw [support_eq_image,←himage,image_image]
    rfl
  have hmul := multiplicity_eq_card_ratio (NativeFullCoarseShadow.fullSource h R a level m E)
    (by positivity : 0 < 32/((2^m:ℕ):ℝ)) cells (fun _ => rfl) (fun _ => rfl)
  rw [hmul,ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast,hcard,hsupport]
  rfl

/-- Source-facing multiplicity transfer on one unchanged original E and R.
The only uniformity hypotheses are equalities of two actual old-label maps. -/
theorem multiplicity_le_full_source {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level)
    (rad : ℕ)
    (hpair : let rep := NativeCoarseDirectionThinning.representative h R a (2^m)
      let B := NativeCoarseDyadicShading.block level m
      ∀x∈E,∀y∈E,
      (E.filter (fun z => label D a (2^m) B rep z=label D a (2^m) B rep x)).card ≤
        rad^2*(E.filter (fun z => label D a (2^m) B rep z=label D a (2^m) B rep y)).card)
    (hpoint : let rep := NativeCoarseDirectionThinning.representative h R a (2^m)
      let B := NativeCoarseDyadicShading.block level m
      ∀x∈E,∀y∈E,
      (E.filter (fun z => pointLabel D a (2^m) B rep z=pointLabel D a (2^m) B rep x)).card ≤
        rad^2*(E.filter (fun z => pointLabel D a (2^m) B rep z=pointLabel D a (2^m) B rep y)).card) :
    NativeIncidenceMultiplicityTower.multiplicity
      (NativeIncidenceMultiplicityTower.coarse E (parentLabel D a (2^m))) ≤
      (125:ℝ)*(rad:ℝ)^4*(NativeFiniteKakeyaCounts.multiplicity
        (NativeFullCoarseShadow.fullSource h R a level m E)).toReal := by
  rw [full_source_multiplicity_real h R a level m E hR]
  apply multiplicity_le_actual h original horiginal ha (2^m) _ (by positivity) _
    (NativeCoarseDyadicShading.block_mesh hdy hm) _ E hE _ rad hpair hpoint
  · rw [NativeLocalParentScales.relative_scale hdy hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · intro z hz
    exact (NativeCoarseDirectionThinning.representative_spec h R a (2^m)
      (mem_image_of_mem _ (hR z hz))).2

end NativeCoarsePointMultiplicity
