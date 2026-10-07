import Theorems.Thm_StickyKakeya4_native_scale_menu_successor
import Theorems.Thm_StickyKakeya4_native_balanced_configuration
import Theorems.Thm_StickyKakeya4_native_coarse_scale_interpolation
import Theorems.Thm_StickyKakeya4_native_coarse_power_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeMiddleWindowBalance
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeFixedSizeScaleMenu NativeScaleMenuSuccessor NativeLocalMenuInterpolation
open NativeNearTargetLoss
open scoped BigOperators ENNReal

/-- At an arbitrary original depth, the full physical coarse shadow and all
active original parent incidences have complementary extremal powers. -/
def HasMiddleScale {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ) (tau : ℝ) : Prop :=
  let rho := 64/((2^m:ℕ):ℝ)
  let C := (NativeFiniteKakeyaCounts.multiplicity
    (NativeFullCoarseShadow.fullSource h R a level m E)).toReal
  D.thickness^tau*rho^(-extremalExponent) ≤ C ∧
    C ≤ D.thickness^(-tau)*rho^(-extremalExponent) ∧
    ∀p,(parentEdges D a (2^m) E p).Nonempty →
      D.thickness^tau*(localScale D.thickness m)^(-extremalExponent) ≤
        edgeMultiplicity (parentEdges D a (2^m) E p) ∧
      edgeMultiplicity (parentEdges D a (2^m) E p) ≤
        D.thickness^(-tau)*(localScale D.thickness m)^(-extremalExponent)

lemma radix_sq_le_of_transfer_cost {delta eta gamma : ℝ} (hd : 0 < delta)
    (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (F Q : ℕ) (hF : 0 < F)
    (hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤ delta^(-gamma)) :
    (Q:ℝ)^2 ≤ delta^(-gamma) := by
  have hF1 : (1:ℝ) ≤ F := by exact_mod_cast hF
  have hC : (1:ℝ) ≤ (125*175616*16384:ℝ)*(F:ℝ) := by nlinarith
  have hp : 1 ≤ delta^(-eta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr heta)
  have hs : (Q:ℝ)^2 ≤ (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (sq_nonneg (Q:ℝ))
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2 by positivity)
  have hm' : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2 ≤
      (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) := by
    simpa only [mul_one] using hm
  exact hs.trans (hm'.trans hcost)

lemma large_level_of_grid (w : ℝ) (hw : 0 < w) (g level : ℕ) (hg : 0 < g)
    (hgrid : 1/(g:ℝ) < w/4) (hgl : g ≤ level) : 4 ≤ w*(level:ℝ) := by
  have hgr : (0:ℝ) < g := by exact_mod_cast hg
  have hh := (div_lt_iff₀ hgr).mp hgrid
  have hglR : (g:ℝ) ≤ level := by exact_mod_cast hgl
  have hmul := mul_le_mul_of_nonneg_left hglR hw.le
  nlinarith

/-- Direct readback of the all-scale physical upper bound, with its scale
loss paid at original delta. This uses no off-menu incidence uniformity. -/
lemma coarse_upper_of_admission {n : ℕ} {D : FiniteScaleSource n}
    {eta a e zeta gamma loss target : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (level m : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level)
    (hloss : 0 ≤ loss) (hmargin : gamma+loss ≤ target)
    (HC : HasCoarseScale h R E a level m e zeta gamma loss) :
    (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level m E)).toReal ≤
      D.thickness^(-target)*(64/((2^m:ℕ):ℝ))^(-extremalExponent) := by
  have hd := h.1.2.1
  have hr : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hdr : D.thickness ≤ 64/((2^m:ℕ):ℝ) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<((2^m:ℕ):ℝ))).mpr
    nlinarith
  have hfinite : (ENNReal.ofReal D.thickness).rpow (-gamma)*
      (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow (-extremalExponent-loss) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top)
  have hreal : (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level m E)).toReal ≤
      D.thickness^(-gamma)*(64/((2^m:ℕ):ℝ))^(-extremalExponent-loss) := by
    have hh := ENNReal.toReal_mono hfinite HC.2
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hd.le,ENNReal.toReal_ofReal hr.le] using hh
  exact upper_with_target_loss hd h.1.2.2.1 hr hdr hloss hmargin hreal

/-- Preceding and succeeding entries of the SAME fixed menu control both
sides of every original parent at an arbitrary middle-window depth. -/
theorem middle_old_parent_bounds {n : ℕ} (D : FiniteScaleSource n)
    (hd : 0 < D.thickness) (hd1 : D.thickness ≤ 1) (a : ℝ)
    (E : Finset (Fin n × Index)) (level : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2)
    (g Q : ℕ) (hg : 0 < g) (hgl : g ≤ level) (hgrid : 1/(g:ℝ) < w/4)
    (b gamma target : ℝ) (hQ : (Q:ℝ)^2 ≤ D.thickness^(-gamma))
    (hmarginL : b+(1/(g:ℝ))*extremalExponent ≤ target)
    (hmarginU : b+gamma+(2/(g:ℝ))*extremalExponent ≤ target)
    (HU : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1)
        (parentPointRel D a (2^(windowSchedule w hw.le g level j).val)) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1)
        (parentPointRel D a (2^(windowSchedule w hw.le g level j).val)) E y)
    (HM : ∀j p,(parentEdges D a (2^(windowSchedule w hw.le g level j).val) E p).Nonempty →
      D.thickness^b*(localScale D.thickness (windowSchedule w hw.le g level j).val)^(-extremalExponent) ≤
        edgeMultiplicity (parentEdges D a (2^(windowSchedule w hw.le g level j).val) E p) ∧
      edgeMultiplicity (parentEdges D a (2^(windowSchedule w hw.le g level j).val) E p) ≤
        D.thickness^(-b)*(localScale D.thickness (windowSchedule w hw.le g level j).val)^(-extremalExponent))
    (m : ℕ) (hlo : w*(level:ℝ) ≤ m) (hhi : (m:ℝ) ≤ (1-w)*(level:ℝ))
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    D.thickness^target*(localScale D.thickness m)^(-extremalExponent) ≤
        edgeMultiplicity (parentEdges D a (2^m) E p) ∧
      edgeMultiplicity (parentEdges D a (2^m) E p) ≤
        D.thickness^(-target)*(localScale D.thickness m)^(-extremalExponent) := by
  have hlarge := large_level_of_grid w hw g level hg hgrid hgl
  obtain ⟨jc,hcm,_hgap,hgapR⟩ :=
    exists_window_predecessor w hw hwsmall g level m hg hgrid hlarge hlo hhi
  obtain ⟨jd,hmd,_hgapD,hgapDR⟩ :=
    exists_window_successor w hw hwsmall g level m hg hlarge hlo hhi
  have hl := off_menu_parent_power_lower D hd a E level hdy hmd (1/(g:ℝ)) b
    extremalExponent hgapDR extremalExponent_nonneg (fun q hq => (HM jd q hq).1) p hp
  have hu := off_menu_parent_power_absorbed D hd a E Q level hdy hcm
    (2/(g:ℝ)) b gamma extremalExponent (gap_le_twice_fraction g level m _ hg hgl hgapR)
    extremalExponent_nonneg hQ (HU jc) (fun q hq => (HM jc q hq).2) p
  refine ⟨lower_with_target_loss hd hd1 (localScale_pos hd m) hmarginL hl,hu.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith))
    (Real.rpow_pos_of_pos (localScale_pos hd m) _).le

/-- The full physical lower bound comes from the preceding menu's actual
cube image and the proved 729*r^4 representative comparison. -/
theorem middle_coarse_lower {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (w : ℝ) (hw : 0<w) (hwsmall : w<1/2) (g : ℕ)
    (hg : 0<g) (hgl : g≤level) (hgrid : 1/(g:ℝ)<w/4)
    (b target : ℝ) (hconstant : (729:ℝ)≤D.thickness^(-b))
    (hmargin : 2*b+(2/(g:ℝ))*(4+extremalExponent)≤target)
    (HM : ∀j,D.thickness^b*(64/((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ))^(-extremalExponent) ≤
      (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level
        (windowSchedule w hw.le g level j).val E)).toReal)
    (m : ℕ) (hm : m ≤ level) (hlo : w*(level:ℝ) ≤ m) (hhi : (m:ℝ) ≤ (1-w)*(level:ℝ)) :
    D.thickness^target*(64/((2^m:ℕ):ℝ))^(-extremalExponent) ≤
      (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E)).toReal := by
  have hd := h.1.2.1
  have hlarge := large_level_of_grid w hw g level hg hgrid hgl
  obtain ⟨j,hcm,_hgap,hgapR⟩ :=
    exists_window_predecessor w hw hwsmall g level m hg hgrid hlarge hlo hhi
  let c := (windowSchedule w hw.le g level j).val
  have hforward := NativeCoarseScaleInterpolation.full_source_multiplicity_le h original horiginal ha
    R E hE hR level c m hdy hcm hm
  have hr : (0:ℝ)<((2^(m-c):ℕ):ℝ) := by positivity
  have hscale : 64/((2^c:ℕ):ℝ)=((2^(m-c):ℕ):ℝ)*(64/((2^m:ℕ):ℝ)) := by
    have hh := NativeCoarseScaleInterpolation.coarse_mesh_ratio c m hcm
    calc
      _ = 2*(32/((2^c:ℕ):ℝ)) := by ring
      _ = 2*(((2^(m-c):ℕ):ℝ)*(32/((2^m:ℕ):ℝ))) := by rw [hh]
      _ = _ := by ring
  have hratio := NativeLocalMenuInterpolation.dyadic_gap_power hdy
    (gap_le_twice_fraction g level m c hg hgl hgapR)
  have hl := NativeCoarsePowerInterpolation.middle_lower_of_forward_bound hd
    (by positivity : (0:ℝ)<64/((2^m:ℕ):ℝ)) hr extremalExponent_nonneg
    hscale hratio hconstant (HM j) hforward ENNReal.toReal_nonneg
  exact lower_with_target_loss hd h.1.2.2.1 (by positivity) hmargin hl

/-- The complete original backbone data is retained unchanged by the
middle-window interpolation. Its population law still covers every level. -/
def HasOriginalBackbone {n : ℕ} (D : FiniteScaleSource n)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (a : ℝ) (level : ℕ) (zeta : ℝ) : Prop :=
  (∀i,D.shading i=wzCellShading (mesh D) original i) ∧
  D.thickness=(2:ℝ)⁻¹^level ∧
  (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
  R.Nonempty ∧ n≤2*R.card ∧
  wzTotalShadingVolume D≤2*NativeOriginalPrunedMass.shadingMass D R ∧
  (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R ≤
    NativeOriginalPrunedMass.shadingMass D R ∧
  (∀U : Set E4,Convex ℝ U →
    ((R.filter (fun i => markedUnitTube (D.line i) D.thickness⊆U)).card:ℝ≥0∞) ≤
      (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
  ∀ell : Fin (level+1),∀p : Parent,
    (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
    D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
      ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
    ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
      D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3

/-- The literal clipped menu used by the source-facing endpoint. -/
def canonicalSchedule (window tau : ℝ) (hw : 0 < window) (htau : 0 < tau)
    (g level : ℕ) : Fin (g+1) → Fin (level+1) :=
  windowSchedule (min window (tau/1000)) (lt_min hw (by positivity)).le g level

/-- Genuine near-extremizers supply one R and one incidence core E with
two-sided bounds at EVERY dyadic depth in the requested middle window. The
finite menu count is fixed before the source, and only its scheduled local
sources are asserted to be native inputs. -/
theorem exists_middle_configuration (hk : 0 < extremalExponent)
    (tau window : ℝ) (htau : 0 < tau) (hw : 0 < window) (hwsmall : window < 1/2) :
    ∃ (e zeta : ℝ) (L g : ℕ), 0<e ∧ 0<zeta ∧ zeta≤tau/2048 ∧ 0<L ∧ 0<g ∧
      1/(g:ℝ) < min window (tau/1000)/4 ∧
      ∀etaBound deltaBound : ℝ,0<etaBound → 0<deltaBound →
      ∃ (eta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0<eta ∧ eta<etaBound ∧ eta<tau/64 ∧ D.thickness<deltaBound ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D)≤(ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta)≤(NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n))
          (original : Fin n → Finset Index) (E : Finset (Fin n × Index))
          (schedule : Fin (g+1) → Fin (level+1)),
          HasOriginalBackbone D original R a level zeta ∧ g ≤ level ∧
          schedule = canonicalSchedule window tau hw htau g level ∧
          IsCore D original R a eta zeta (menuSize (g+1) (g+1)) (g+1) L
            (relationMenu h R a schedule (fun j => parentPointRel D a (2^(schedule j).val)))
            (fun j => 2^(schedule j).val) E ∧
          (∀j,HasJointScale h R E a level (schedule j).val e zeta ((tau/8)/8) ((tau/8)/8) ∧
            HasBalancedScale h R E a level (schedule j).val (tau/8)) ∧
          ∀m : ℕ,window*(level:ℝ) ≤ m → (m:ℝ) ≤ (1-window)*(level:ℝ) →
            HasMiddleScale h R E a level m tau := by
  let w := min window (tau/1000)
  let b := tau/8
  have hw0 : 0<w := lt_min hw (by positivity)
  have hw0small : w<1/2 := (min_le_left _ _).trans_lt hwsmall
  have hbw : 0<b := by dsimp [b]; positivity
  obtain ⟨g,dm,hg,hdm,hgrid,hmenu⟩ := exists_source_window_menu w hw0 hw0small
  obtain ⟨e,zeta,L,he,_hzeq,hzeta,hzsmall,hL,hbase⟩ :=
    exists_balanced_configuration hk b (w/2) hbw (half_pos hw0) (g+1) (g+1) (by omega)
  have hzsmall' : zeta≤tau/2048 := by dsimp [b] at hzsmall; linarith
  obtain ⟨dc,hdc,_hdc1,hconstantCut⟩ := exists_positive_rpow_absorption_threshold hbw
    (by norm_num : (0:ℝ)≤729) (by norm_num : (0:ℝ)<1)
  refine ⟨e,zeta,L,g,he,hzeta,hzsmall',hL,hg,hgrid,?_⟩
  intro etaBound deltaBound heB hdB
  let cutoff := min deltaBound (min dm (min ((2:ℝ)⁻¹^g) dc))
  have hcut : 0<cutoff := lt_min hdB (lt_min hdm (lt_min (by positivity) hdc))
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSmall,hsmall,hK,hvol,hnear,
    a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase etaBound cutoff heB hcut
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hetaTarget : eta<tau/64 := by dsimp [b] at hetaSmall; linarith
  have hcuts : D.thickness≤deltaBound ∧ D.thickness≤dm ∧
      D.thickness≤(2:ℝ)⁻¹^g ∧ D.thickness≤dc := by
    simpa only [cutoff,le_min_iff] using hsmall.le
  have hgl := depth_le_of_dyadic_cutoff level g hdy hcuts.2.2.1
  let schedule := windowSchedule w hw0.le g level
  let Rel := fun j : Fin (g+1) => parentPointRel D a (2^(schedule j).val)
  have hmenuPower := (hmenu D.thickness level hdy hcuts.2.1).1
  obtain ⟨E,hEcore,hcost,hOld,hCoarseAll,hScales⟩ := hcore schedule
    (fun j => (hmenuPower j).1) (fun j => (hmenuPower j).2) Rel
    (fun j => parentPointRel_refl D a _) (fun j => parentPointRel_symm D a _)
  have hF : 0<factor (menuSize (g+1) (g+1)) (g+1) L := by
    unfold factor NativeLocalPairUniformCore.retentionCost menuSize
    positivity
  have hQ := radix_sq_le_of_transfer_cost hd hd1 heta.le
    (factor (menuSize (g+1) (g+1)) (g+1) L) (coreRadix original R L) hF hcost
  have hconstant : (729:ℝ)≤D.thickness^(-b) := by
    have hh := hconstantCut D.thickness hd hcuts.2.2.2
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd b)).mpr hh
  have hgridSmall : 1/(g:ℝ)≤tau/4000 := by
    have hwTau : w≤tau/1000 := min_le_right _ _
    nlinarith
  have hkgrid : (1/(g:ℝ))*extremalExponent≤3*(1/(g:ℝ)) := by
    exact (mul_le_mul_of_nonneg_left extremalExponent_le_three (by positivity)).trans_eq (by ring)
  have htwo : 2/(g:ℝ)=2*(1/(g:ℝ)) := by ring
  have hmarginL : b+(1/(g:ℝ))*extremalExponent≤tau := by dsimp [b]; nlinarith
  have hmarginU : b+b/8+(2/(g:ℝ))*extremalExponent≤tau := by rw [htwo]; dsimp [b]; nlinarith
  have hmarginC : 2*b+(2/(g:ℝ))*(4+extremalExponent)≤tau := by rw [htwo]; dsimp [b]; nlinarith
  have hEA : E⊆incidences original := hEcore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hEcore.1 hz)).2
  have hOldMenu : ∀j p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
      D.thickness^b*(localScale D.thickness (schedule j).val)^(-extremalExponent) ≤
        edgeMultiplicity (parentEdges D a (2^(schedule j).val) E p) ∧
      edgeMultiplicity (parentEdges D a (2^(schedule j).val) E p) ≤
        D.thickness^(-b)*(localScale D.thickness (schedule j).val)^(-extremalExponent) := by
    intro j p hp
    exact ((hScales j).2.2.2 p hp).2.2
  refine ⟨eta,n,D,h,heta,hetaB,hetaTarget,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    a,level,R,original,E,schedule,⟨horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H⟩,
    hgl,rfl,hEcore,hScales,?_⟩
  intro m hlo hhi
  have hln : (0:ℝ)≤level := Nat.cast_nonneg _
  have hwWindow : w≤window := min_le_left _ _
  have hwLevels := mul_le_mul_of_nonneg_right hwWindow hln
  have hwLevel0 : 0≤w*(level:ℝ) := mul_nonneg hw0.le hln
  have hwindowLevel0 : 0≤window*(level:ℝ) := mul_nonneg hw.le hln
  have hlo0 : w*(level:ℝ) ≤ m := by nlinarith
  have hhi0 : (m:ℝ)≤(1-w)*(level:ℝ) := by nlinarith
  have hm : m≤level := by
    have hh : (m:ℝ)≤level := by nlinarith
    exact_mod_cast hh
  have hpower := depth_window_powers (w:=w) level m hdy (by nlinarith) (by nlinarith)
  refine ⟨?_,?_,?_⟩
  · exact middle_coarse_lower h original horiginal ha R E hEA hER level hdy
      w hw0 hw0small g hg hgl hgrid b tau hconstant hmarginC
      (fun j => (hScales j).2.1) m hm hlo0 hhi0
  · exact coarse_upper_of_admission (gamma:=b/8) (loss:=b/8) (target:=tau)
      h R E level m hdy hm (by dsimp [b]; positivity)
      (by dsimp [b]; linarith) (hCoarseAll m hpower.1 hpower.2)
  · intro p hp
    exact middle_old_parent_bounds D hd hd1 a E level hdy w hw0 hw0small g
      (coreRadix original R L) hg hgl hgrid b (b/8) tau hQ hmarginL hmarginU hOld hOldMenu m hlo0 hhi0 p hp

end NativeMiddleWindowBalance
