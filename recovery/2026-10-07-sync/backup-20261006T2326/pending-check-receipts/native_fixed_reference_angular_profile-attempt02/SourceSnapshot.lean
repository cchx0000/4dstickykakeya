import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_original_point_angular_lower
import Theorems.Thm_StickyKakeya4_native_coarse_uniform_image_degrees
import Theorems.Thm_StickyKakeya4_native_normalized_parent_carrier_metric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeFixedReferenceAngularProfile
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeOriginalCellChartGeometry
open NativeJointUniformCoarseRelations NativeConditionedPairMenu NativeGenericReferenceData
open NativeFixedCompactKakeyaExponent NativePointAngularParentFibers SelfUniform
open scoped BigOperators

/-- Literal incidences of the unchanged fine reference at an original point,
whose actual unit directions lie in a closed Euclidean ball. -/
def ballIncidences {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (k : Index) (v : E4) (r : ℝ) :
    Finset (Fin n × Index) :=
  E.filter (fun z => z.2=k ∧ dist (direction (D.line z.1)) v≤r)

/-- Distinct actual directions through the original point, without representatives. -/
def ballDirections {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (k : Index) (v : E4) (r : ℝ) : Finset E4 :=
  (ballIncidences D E k v r).image (fun z => direction (D.line z.1))

/-- Native fine separation identifies direction counts with original incidence
counts at one point. This is an equality, not a new separation assumption. -/
lemma ballDirections_card {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (E : Finset (Fin n × Index)) (k : Index) (v : E4) (r : ℝ) :
    (ballDirections D E k v r).card=(ballIncidences D E k v r).card := by
  apply card_image_iff.mpr
  intro z hz w hw he
  change direction (D.line z.1)=direction (D.line w.1) at he
  have hfirst : z.1=w.1 := by
    by_contra hne
    have hs := h.1.2.2.2.2.2.2.2.2.2.1 z.1 w.1 hne
    rw [he,dist_self] at hs
    exact (not_le_of_gt h.1.2.1) hs
  exact Prod.ext hfirst ((mem_filter.mp hz).2.1.trans (mem_filter.mp hw).2.1.symm)

lemma formal_uniformity {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) :
    HasUniformFibers ref.E1 (coreRadix ref.original ref.R L)
      (formalPair D ref.a (ref.schedule j).val) := by
  intro x hx y hy
  have hh := ref.parent_point j x y hx hy
  change degree (fun _ : Fin n × Index => 1)
    (fun x y => formalPair D ref.a (ref.schedule j).val x =
      formalPair D ref.a (ref.schedule j).val y) ref.E1 x ≤
    (coreRadix ref.original ref.R L)^2*degree (fun _ : Fin n × Index => 1)
      (fun x y => formalPair D ref.a (ref.schedule j).val x =
        formalPair D ref.a (ref.schedule j).val y) ref.E1 y at hh
  simpa only [unit_degree_eq_fiber] using hh

lemma parent_point_uniformity {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) (p : Parent) :
    HasUniformFibers (parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p)
      (coreRadix ref.original ref.R L) Prod.snd :=
  conditioned_uniformity ref.E1
    (fun z : Fin n × Index => parentLabel D ref.a (2^(ref.schedule j).val) z.1)
    Prod.snd (coreRadix ref.original ref.R L) (formal_uniformity ref j) p

lemma uniform_point_fiber_le_mean {n : ℕ} (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : HasUniformFibers E Q Prod.snd) (k : Index) :
    ((E.filter (fun z => z.2=k)).card:ℝ) ≤
      (Q:ℝ)^2*NativeIncidenceMultiplicityTower.multiplicity E := by
  by_cases hE : E.Nonempty
  · have hs : (0:ℝ)<(E.image Prod.snd).card := by
      exact_mod_cast card_pos.mpr (hE.image Prod.snd)
    have hc : (E.filter (fun z => z.2=k)).card*(E.image Prod.snd).card ≤ Q^2*E.card := by
      simpa only [id_eq,image_id] using
        NativeCoarseUniformImageDegrees.point_fiber_card_cross E id (Q^2) H k
    rw [NativeIncidenceMultiplicityTower.multiplicity,←mul_div_assoc]
    apply (le_div_iff₀ hs).mpr
    exact_mod_cast hc
  · rw [not_nonempty_iff_eq_empty.mp hE]
    simp [NativeIncidenceMultiplicityTower.multiplicity]

/-- Both pointwise bounds use the mean inside this same original parent. -/
lemma parent_point_fiber_bounds {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1))
    (p : Parent) (k : Index)
    (hk : k∈(parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p).image Prod.snd) :
    D.thickness^seed*(((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) ≤
      (coreRadix ref.original ref.R L:ℝ)^2*
        (((parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p).filter (fun z => z.2=k)).card:ℝ) ∧
    (((parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p).filter (fun z => z.2=k)).card:ℝ) ≤
      (coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed)*
        (((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) := by
  let Ep := parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p
  have hp : Ep.Nonempty := by
    obtain ⟨z,hz,_⟩ := mem_image.mp hk
    exact ⟨z,hz⟩
  have H := parent_point_uniformity ref j p
  have HM := ((ref.scales j).2.2.2 p hp).2.2
  refine ⟨HM.1.trans (NativeActualAngularMenuLower.mean_le_point_fiber Ep _ H k hk),?_⟩
  exact (uniform_point_fiber_le_mean Ep _ H k).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left HM.2
      (sq_nonneg (coreRadix ref.original ref.R L:ℝ))))

/-- The upper also applies to empty original parent-point fibers. -/
lemma parent_point_fiber_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) (p : Parent) (k : Index) :
    (((parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p).filter (fun z => z.2=k)).card:ℝ) ≤
      (coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed)*
        (((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) := by
  have hd := h.1.2.1
  by_cases hk : k∈(parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p).image Prod.snd
  · exact (parent_point_fiber_bounds ref j p k hk).2
  · have he : (parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p).filter
        (fun z => z.2=k)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hk (mem_image.mpr ⟨z,(mem_filter.mp hz).1,(mem_filter.mp hz).2⟩)
    rw [he,card_empty,Nat.cast_zero]
    positivity

lemma same_parent_direction_close {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (N : ℕ) (hN : 0<N)
    (i t : Fin n) (hp : parentLabel D a N t=parentLabel D a N i) :
    dist (direction (D.line t)) (direction (D.line i)) ≤ 64/(N:ℝ) := by
  have hs : dist (slope (D.line t)) (slope (D.line i))≤1/(N:ℝ) := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro u
    simpa only [Real.dist_eq] using
      NativeNormalizedParentCarrierMetric.same_floor_mul_close _ _ N hN
        (congrFun (congrArg Prod.fst hp) u)
  have hd := NativeOriginalSlopeCubePacking.direction_dist_le_eight_slope_dist
    (D.line t) (D.line i) (h.1.2.2.2.2.1 t) (h.1.2.2.2.2.1 i) (h.2.1.1 t) (h.2.1.1 i)
  calc
    _ ≤ 8*(1/(N:ℝ)) := hd.trans (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ = 8/(N:ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)

/-- At an occupied center, the actual scheduled parent provides the lower
ball count on ref.E1, with its original fine point and original mean. -/
theorem scheduled_ball_lower {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1))
    (i : Fin n) (k : Index) (hik : (i,k)∈ref.E1) :
    D.thickness^seed*(((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) ≤
      (coreRadix ref.original ref.R L:ℝ)^2*
        (ballDirections D ref.E1 k (direction (D.line i))
          (64/((2^(ref.schedule j).val:ℕ):ℝ))).card := by
  let N : ℕ := 2^(ref.schedule j).val
  let p := parentLabel D ref.a N i
  have hikp : (i,k)∈parentEdges D ref.a N ref.E1 p := mem_filter.mpr ⟨hik,rfl⟩
  have hlo := (parent_point_fiber_bounds ref j p k (mem_image_of_mem Prod.snd hikp)).1
  have hs : (parentEdges D ref.a N ref.E1 p).filter (fun z => z.2=k) ⊆
      ballIncidences D ref.E1 k (direction (D.line i)) (64/(N:ℝ)) := by
    intro z hz
    obtain ⟨hzp,hzk⟩ := mem_filter.mp hz
    obtain ⟨hz,hzp⟩ := mem_filter.mp hzp
    exact mem_filter.mpr ⟨hz,hzk,same_parent_direction_close h ref.a N (by dsimp [N]; positivity) i z.1 hzp⟩
  rw [ballDirections_card h]
  exact hlo.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hs)
    (sq_nonneg (coreRadix ref.original ref.R L:ℝ)))

lemma floor_mem_radius (x y : ℝ) (K : ℕ) (hxy : |x-y|≤K) :
    ⌊x⌋∈Icc (⌊y⌋-(K:ℤ)) (⌊y⌋+K) := by
  obtain ⟨hl,hu⟩ := abs_le.mp hxy
  have hx0 := Int.floor_le x
  have hx1 := Int.lt_floor_add_one x
  have hy0 := Int.floor_le y
  have hy1 := Int.lt_floor_add_one y
  have hlo : ⌊y⌋-(K:ℤ)<⌊x⌋+1 := by exact_mod_cast (show (⌊y⌋:ℝ)-(K:ℝ)<(⌊x⌋:ℝ)+1 by linarith)
  have hhi : ⌊x⌋<⌊y⌋+(K:ℤ)+1 := by exact_mod_cast (show (⌊x⌋:ℝ)<(⌊y⌋:ℝ)+(K:ℝ)+1 by linarith)
  exact mem_Icc.mpr ⟨by omega,by omega⟩

/-- An arbitrary Euclidean ball at radius64/N meets at most1537^3 of the
literal slope cells at depthN. The occupied anchor is only used in this proof. -/
lemma ball_angular_cells_card {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (N : ℕ) (hN : 0<N)
    (E : Finset (Fin n × Index)) (k : Index) (v : E4) :
    (pointAngular D a N (ballIncidences D E k v (64/(N:ℝ))) k).card≤1537^3 := by
  let B := ballIncidences D E k v (64/(N:ℝ))
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  by_cases hB : B.Nonempty
  · obtain ⟨z0,hz0⟩ := hB
    let q := (parentLabel D a N z0.1).1
    let menu : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun u => Icc (q u-768) (q u+768))
    have hmenu : menu.card=1537^3 := by
      have hc (u : Fin 3) : (Icc (q u-768) (q u+768)).card=1537 := by
        have hh : ((Icc (q u-768) (q u+768)).card:ℤ)=1537 := by
          rw [Int.card_Icc_of_le _ _ (by omega)]
          omega
        exact_mod_cast hh
      simp only [menu,Fintype.card_piFinset,hc,prod_const,card_univ,Fintype.card_fin]
    have hsub : pointAngular D a N B k⊆menu := by
      rw [pointAngular_readback]
      intro q' hq'
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hq'
      have hzB := (mem_filter.mp hz).1
      have hzball := (mem_filter.mp hzB).2.2
      have hz0ball := (mem_filter.mp hz0).2.2
      have hdist : dist (direction (D.line z.1)) (direction (D.line z0.1))≤2*(64/(N:ℝ)) := by
        calc
          _ ≤ dist (direction (D.line z.1)) v+dist v (direction (D.line z0.1)) := dist_triangle _ _ _
          _ ≤ 64/(N:ℝ)+64/(N:ℝ) := add_le_add hzball (by simpa only [dist_comm] using hz0ball)
          _ = _ := by ring
      apply Fintype.mem_piFinset.mpr
      intro u
      have hs := (NativeUnitParentDirections.slope_sub_le_direction_dist
        (D.line z.1) (D.line z0.1) (h.1.2.2.2.2.1 z0.1) (h.2.1.1 z.1) (h.2.1.1 z0.1) u).trans
          (mul_le_mul_of_nonneg_left hdist (by norm_num))
      have hm : |(N:ℝ)*slope (D.line z.1) u-(N:ℝ)*slope (D.line z0.1) u|≤768 := by
        calc
          _ = (N:ℝ)*|slope (D.line z.1) u-slope (D.line z0.1) u| := by rw [←mul_sub,abs_mul,abs_of_pos hNr]
          _ ≤ (N:ℝ)*(6*(2*(64/(N:ℝ)))) := mul_le_mul_of_nonneg_left hs hNr.le
          _ = _ := by field_simp; ring
      exact floor_mem_radius _ _ 768 hm
    exact (card_le_card hsub).trans_eq hmenu
  · have he : B=∅ := not_nonempty_iff_eq_empty.mp hB
    change (pointAngular D a N B k).card≤_
    simp only [he,pointAngular,pointParents,filter_empty,image_empty,card_empty]
    positivity

/-- Sum actual same-reference parent-point uppers. The factor343 is the
geometric intercept menu at the original point, not a parent population loss. -/
theorem scheduled_ball_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) (k : Index) (v : E4) :
    ((ballDirections D ref.E1 k v (64/((2^(ref.schedule j).val:ℕ):ℝ))).card:ℝ) ≤
      (343*1537^3:ℝ)*(coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed)*
        (((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) := by
  let N : ℕ := 2^(ref.schedule j).val
  let B := ballIncidences D ref.E1 k v (64/(N:ℝ))
  let U : ℝ := (coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed)*
    ((N:ℝ)*D.thickness/64)^(-extremalExponent)
  have hN : 0<N := by dsimp [N]; positivity
  have hd := h.1.2.1
  have hU : 0≤U := by dsimp [U]; positivity
  have hBpoint : B.filter (fun z => z.2=k)=B := by
    apply filter_eq_self.mpr
    intro z hz
    exact (mem_filter.mp hz).2.1
  have hBoriginal : B⊆incidences ref.original := by
    intro z hz
    exact (mem_filter.mp (ref.core.1 (mem_filter.mp hz).1)).1
  have hscale : (N:ℝ)*D.thickness≤1 :=
    NativeCompactAncestorRegularity.dyadic_parent_scale ref.backbone.2.1 (ref.schedule j)
  have hparents := pointParents_card_le_angular h ref.original ref.backbone.1
    ref.backbone.2.2.1 N hscale B hBoriginal k
  have hangles := ball_angular_cells_card h ref.a N hN ref.E1 k v
  have hP : (pointParents D ref.a N B k).card≤343*1537^3 :=
    hparents.trans (Nat.mul_le_mul_left 343 hangles)
  have hsum : (B.card:ℝ)=∑p∈pointParents D ref.a N B k,
      ((B.filter (fun z => parentLabel D ref.a N z.1=p)).card:ℝ) := by
    have hp : pointParents D ref.a N B k=B.image (fun z => parentLabel D ref.a N z.1) := by
      rw [pointParents,hBpoint]
    rw [hp]
    exact_mod_cast card_eq_sum_card_image (fun z => parentLabel D ref.a N z.1) B
  have hbound (p : Parent) : ((B.filter (fun z => parentLabel D ref.a N z.1=p)).card:ℝ)≤U := by
    have hsub : B.filter (fun z => parentLabel D ref.a N z.1=p)⊆
        (parentEdges D ref.a N ref.E1 p).filter (fun z => z.2=k) := by
      intro z hz
      obtain ⟨hzB,hzp⟩ := mem_filter.mp hz
      obtain ⟨hz,hzk,_⟩ := mem_filter.mp hzB
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hz,hzp⟩,hzk⟩
    have hc : ((B.filter (fun z => parentLabel D ref.a N z.1=p)).card:ℝ) ≤
        (((parentEdges D ref.a N ref.E1 p).filter (fun z => z.2=k)).card:ℝ) := by
      exact_mod_cast card_le_card hsub
    exact hc.trans (parent_point_fiber_upper ref j p k)
  rw [ballDirections_card h]
  change (B.card:ℝ)≤_
  calc
    _ = _ := hsum
    _ ≤ ∑_p∈pointParents D ref.a N B k,U := sum_le_sum (fun p _ => hbound p)
    _ = ((pointParents D ref.a N B k).card:ℝ)*U := by simp
    _ ≤ (343*1537^3:ℝ)*U := mul_le_mul_of_nonneg_right (by exact_mod_cast hP) hU
    _ = _ := by dsimp [U]; ring

/-- Source-facing scheduled-radius angular profile of the single fixed E1.
The lower uses an occupied center; the upper holds for every ambient center.
The normalization scale remains the original D.thickness throughout. -/
theorem scheduled_angular_profile {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) :
    (∀ (i : Fin n) (k : Index), (i,k)∈ref.E1 →
      D.thickness^seed*(((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) ≤
        (coreRadix ref.original ref.R L:ℝ)^2*
          (ballDirections D ref.E1 k (direction (D.line i))
            (64/((2^(ref.schedule j).val:ℕ):ℝ))).card) ∧
    (∀ (k : Index) (v : E4),
      ((ballDirections D ref.E1 k v (64/((2^(ref.schedule j).val:ℕ):ℝ))).card:ℝ) ≤
        (343*1537^3:ℝ)*(coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed)*
          (((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent)) :=
  ⟨fun i k hik => scheduled_ball_lower ref j i k hik,
    fun k v => scheduled_ball_upper ref j k v⟩

/-- The scheduled local multiplicity power is precisely the angular radius
relative to the original fine thickness. -/
lemma relative_power {delta : ℝ} (hd : 0<delta) (N : ℕ) (hN : 0<N) (kappa : ℝ) :
    ((N:ℝ)*delta/64)^(-kappa)=((64/(N:ℝ))/delta)^kappa := by
  rw [Real.rpow_neg_eq_inv_rpow]
  congr 1
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  field_simp [hd.ne',hNr.ne']

/-- Explicit scheduled AD powers with sigma=D.thickness and rho=64/2^j.
No all-radius endpoint or schedule interpolation is asserted here. -/
theorem scheduled_angular_power_profile {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0<tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) :
    let rho : ℝ := 64/((2^(ref.schedule j).val:ℕ):ℝ)
    let Q : ℕ := coreRadix ref.original ref.R L
    (∀ (i : Fin n) (k : Index), (i,k)∈ref.E1 →
      D.thickness^seed*(rho/D.thickness)^extremalExponent/(Q:ℝ)^2 ≤
        (ballDirections D ref.E1 k (direction (D.line i)) rho).card) ∧
    (∀ (k : Index) (v : E4),
      ((ballDirections D ref.E1 k v rho).card:ℝ) ≤
        (343*1537^3:ℝ)*(Q:ℝ)^2*D.thickness^(-seed)*(rho/D.thickness)^extremalExponent) := by
  intro rho Q
  have hQn : 0<Q := lt_of_lt_of_le (by norm_num : 0<4)
    (NativeSourceSizeBounds.radix_four_le _ _)
  have hQ : (0:ℝ)<(Q:ℝ)^2 := by positivity
  have hp := relative_power h.1.2.1 (2^(ref.schedule j).val) (by positivity) extremalExponent
  obtain ⟨hlo,hhi⟩ := scheduled_angular_profile ref j
  constructor
  · intro i k hik
    apply (div_le_iff₀ hQ).mpr
    have hh := hlo i k hik
    rw [hp] at hh
    simpa only [mul_comm] using hh
  · intro k v
    have hh := hhi k v
    rwa [hp] at hh

end NativeFixedReferenceAngularProfile
