/- UNVERIFIED actual Reference point-degree reader. No Lean/compiler check run.
This reads only the genuine Reference fields. In particular, the per-point
estimate is summed directly over actual original parents, with ONE Q^2 loss.
No global mean upper, point separation, or new E1 admission is a premise.
-/
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_coarse_pruning_budget
import Theorems.Thm_StickyKakeya4_native_coarse_uniform_image_degrees

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeFixedReferencePointDegree
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeLocalMenuInterpolation NativeMiddleWindowBalance NativeBalancedConfiguration
open NativeGenericReferenceData NativeAllTwoScaleConfiguration
open NativeActualMesoscopicRankConfiguration NativeFixedSizeScaleMenu
open NativeFixedCompactKakeyaExponent SelfUniform
open scoped BigOperators ENNReal

/-- Uniformity on this actual parent controls each of its point fibers by
its actual incidence/support mean, with one square-radix factor. -/
lemma uniform_point_fiber_le_mean {n : ℕ} (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : HasUniformFibers E Q Prod.snd) (k : Index) :
    ((E.filter (fun z => z.2=k)).card:ℝ) ≤
      (Q:ℝ)^2*NativeIncidenceMultiplicityTower.multiplicity E := by
  by_cases hE : E.Nonempty
  · have hs : (0:ℝ) < (E.image Prod.snd).card := by
      exact_mod_cast card_pos.mpr (hE.image Prod.snd)
    have hc : (E.filter (fun z => z.2=k)).card*(E.image Prod.snd).card ≤ Q^2*E.card := by
      simpa only [id_eq,image_id] using
        NativeCoarseUniformImageDegrees.point_fiber_card_cross E id (Q^2) H k
    rw [NativeIncidenceMultiplicityTower.multiplicity,←mul_div_assoc]
    apply (le_div_iff₀ hs).mpr
    exact_mod_cast hc
  · rw [not_nonempty_iff_eq_empty.mp hE]
    simp [NativeIncidenceMultiplicityTower.multiplicity]

/-- The stored parent-point relation is the literal formalPair relation. -/
lemma formal_uniformity {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
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

/-- Each actual scheduled parent point fiber is controlled by the old-parent
mean stored in ref.scales. There is no second global point-uniformity loss. -/
lemma parent_point_fiber_upper {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) (p : Parent) (k : Index) :
    (((parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p).filter
      (fun z => z.2=k)).card:ℝ) ≤
      (coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed)*
        (((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) := by
  let Ep := parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p
  have hU : HasUniformFibers Ep (coreRadix ref.original ref.R L) Prod.snd :=
    conditioned_uniformity ref.E1
      (fun z : Fin n × Index => parentLabel D ref.a (2^(ref.schedule j).val) z.1)
      Prod.snd (coreRadix ref.original ref.R L) (formal_uniformity ref j) p
  by_cases hp : Ep.Nonempty
  · have hM : NativeIncidenceMultiplicityTower.multiplicity Ep ≤
        D.thickness^(-seed)*
          (((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) :=
      ((ref.scales j).2.2.2 p hp).2.2.2
    exact (uniform_point_fiber_le_mean Ep _ hU k).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hM (sq_nonneg (coreRadix ref.original ref.R L:ℝ)))
  · have hzero : Ep=∅ := not_nonempty_iff_eq_empty.mp hp
    change ((Ep.filter (fun z => z.2=k)).card:ℝ) ≤ _
    rw [hzero]
    simp only [filter_empty,card_empty,Nat.cast_zero]
    positivity

/-- Direct per-point summation over the original occupied parents. The
population law and source packing bound their number on this exact backbone. -/
theorem scheduled_point_fiber_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (j : Fin (g+1)) (k : Index) :
    ((ref.E1.filter (fun z => z.2=k)).card:ℝ) ≤
      373248*(coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed-zeta)*
        ((2^(ref.schedule j).val:ℕ):ℝ)^3*
        (((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) := by
  let N : ℕ := 2^(ref.schedule j).val
  let Q : ℕ := coreRadix ref.original ref.R L
  let P := ref.R.image (parentLabel D ref.a N)
  let F := ref.E1.filter (fun z => z.2=k)
  let B := (Q:ℝ)^2*D.thickness^(-seed)*((N:ℝ)*D.thickness/64)^(-extremalExponent)
  have hd := h.1.2.1
  have hER : ∀z∈ref.E1,z.1∈ref.R := fun z hz =>
    (mem_filter.mp (ref.core.1 hz)).2
  obtain ⟨_horiginal,_hdy,_ha,_hR,_hhalf,_hshade,_hdensity,_hCW,H⟩ := ref.backbone
  have hP : (P.card:ℝ) ≤ 373248*D.thickness^(-zeta)*(N:ℝ)^3 :=
    NativeCoarsePruningBudget.original_occupied_count h ref.R N (by dsimp [N]; positivity)
      (fun p hp => (H (ref.schedule j) p hp).1)
  have hsumNat : F.card = ∑p∈P,(F.filter (fun z => parentLabel D ref.a N z.1=p)).card := by
    apply card_eq_sum_card_fiberwise (s:=F)
      (f:=fun z : Fin n × Index => parentLabel D ref.a N z.1) (t:=P)
    intro z hz
    exact mem_image.mpr ⟨z.1,hER z (mem_filter.mp hz).1,rfl⟩
  have hsum : (F.card:ℝ) =
      ∑p∈P,((F.filter (fun z => parentLabel D ref.a N z.1=p)).card:ℝ) := by
    exact_mod_cast hsumNat
  have hfiber (p : Parent) :
      F.filter (fun z => parentLabel D ref.a N z.1=p) =
        (parentEdges D ref.a N ref.E1 p).filter (fun z => z.2=k) := by
    ext z
    simp only [F,parentEdges,mem_filter,and_assoc,and_left_comm]
  have hcount : (F.card:ℝ) ≤ (P.card:ℝ)*B := by
    rw [hsum]
    calc
      _ ≤ ∑_p∈P,B := by
        apply sum_le_sum
        intro p _hp
        rw [hfiber]
        exact parent_point_fiber_upper ref j p k
      _ = _ := by simp
  have hpowers : D.thickness^(-zeta)*D.thickness^(-seed)=D.thickness^(-seed-zeta) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  calc
    _ ≤ (373248*D.thickness^(-zeta)*(N:ℝ)^3)*B :=
      hcount.trans (mul_le_mul_of_nonneg_right hP (by dsimp [B]; positivity))
    _ = 373248*(Q:ℝ)^2*(D.thickness^(-zeta)*D.thickness^(-seed))*(N:ℝ)^3*
        ((N:ℝ)*D.thickness/64)^(-extremalExponent) := by dsimp [B]; ring
    _ = _ := by rw [hpowers]

/-- Exact first scheduled scale, with its single ceiling allowance. -/
theorem first_scheduled_scale_lower {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (hg : 0 < g)
    (hgrid : 1/(g:ℝ) < rankWindow tau/4) :
    32*D.thickness^(rankWindow tau/2) ≤ 64/((2^(ref.schedule 0).val:ℕ):ℝ) := by
  let w := rankWindow tau
  have hw : 0 < w := rankWindow_pos htau
  have hw8 : w ≤ 1/8 := (min_le_left _ _).trans (min_le_right _ _)
  have hwsmall : w < 1/2 := hw8.trans_lt (by norm_num)
  have hlarge := large_level_of_grid w hw g ref.level hg hgrid ref.grid_depth
  have hschedule : ref.schedule=windowSchedule w hw.le g ref.level :=
    ref.schedule_eq.trans (fullSchedule_eq_rankWindow tau htau g ref.level)
  have hdepth : ((ref.schedule 0).val:ℝ) ≤ (w/2)*(ref.level:ℝ)+1 := by
    rw [hschedule,windowSchedule_zero w hw hwsmall g ref.level hlarge]
    exact (Nat.ceil_lt_add_one (show 0 ≤ (w/2)*(ref.level:ℝ) by positivity)).le
  have hd : D.thickness=(2:ℝ)^(-(ref.level:ℝ)) := by
    simp only [ref.backbone.2.1,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,inv_pow]
  have hp : D.thickness^(w/2) ≤ 2/((2^(ref.schedule 0).val:ℕ):ℝ) := by
    calc
      _ = (2:ℝ)^(-(ref.level:ℝ)*(w/2)) := by
        rw [hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ (2:ℝ)^(1-((ref.schedule 0).val:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        nlinarith
      _ = _ := by
        simp only [Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_one,
          Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ 32*(2/((2^(ref.schedule 0).val:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

/-- Elementary complementary-scale algebra. The nonpositive remaining
coarse exponent uses only kappa≤3. -/
lemma scheduled_scale_power {delta N rho kappa w : ℝ}
    (hd : 0 < delta) (hN : 0 < N) (hr : 0 < rho)
    (hrho : rho=64/N) (hrhoLower : delta^(w/2) ≤ rho) (hk : kappa ≤ 3) :
    N^3*(N*delta/64)^(-kappa) ≤
      (64:ℝ)^3*delta^(-kappa-(3-kappa)*w/2) := by
  have hNread : N=64/rho := by rw [hrho]; field_simp [hN.ne']
  have heps : N*delta/64=delta/rho := by rw [hrho]; field_simp [hN.ne'] <;> ring
  have hproduct : rho^3*rho^(-kappa)=rho^(3-kappa) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hr]
    congr 1
    ring
  have hneg : rho^(-(3-kappa))=1/(rho^3*rho^(-kappa)) := by
    rw [hproduct,Real.rpow_neg hr.le,one_div]
  have hidentity : N^3*(N*delta/64)^(-kappa)=
      (64:ℝ)^3*delta^(-kappa)*rho^(-(3-kappa)) := by
    rw [heps,Real.div_rpow hd.le hr.le,hNread,div_pow,hneg]
    field_simp [hr.ne', (Real.rpow_pos_of_pos hr (-kappa)).ne'] <;> ring
  have hcoarse : rho^(-(3-kappa)) ≤ delta^(-(3-kappa)*w/2) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hd (w/2))
      hrhoLower (by linarith : -(3-kappa) ≤ 0)
    rw [←Real.rpow_mul hd.le] at hh
    convert hh using 1 <;> ring
  calc
    _ = (64:ℝ)^3*delta^(-kappa)*rho^(-(3-kappa)) := hidentity
    _ ≤ (64:ℝ)^3*delta^(-kappa)*delta^(-(3-kappa)*w/2) :=
      mul_le_mul_of_nonneg_left hcoarse (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hd]; congr 2 <;> ring

/-- The first scheduled scale controls every point of this exact E1. -/
theorem first_depth_point_fiber_upper {n : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} {h : IsWangZakharovNativeFiniteInput D eta}
    {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (hg : 0 < g)
    (hgrid : 1/(g:ℝ) < rankWindow tau/4) (k : Index) :
    ((ref.E1.filter (fun z => z.2=k)).card:ℝ) ≤
      (373248*64^3:ℝ)*(coreRadix ref.original ref.R L:ℝ)^2*
        D.thickness^(-extremalExponent-seed-zeta-(3-extremalExponent)*rankWindow tau/2) := by
  have hd := h.1.2.1
  let N : ℝ := ((2^(ref.schedule 0).val:ℕ):ℝ)
  let rho := 64/N
  have hN : 0 < N := by dsimp [N]; positivity
  have hr : 0 < rho := by dsimp [rho]; positivity
  have hrho : D.thickness^(rankWindow tau/2) ≤ rho := by
    have hs := first_scheduled_scale_lower ref hg hgrid
    have hnonneg := Real.rpow_nonneg hd.le (rankWindow tau/2)
    change 32*D.thickness^(rankWindow tau/2) ≤ rho at hs
    nlinarith
  have hpower := scheduled_scale_power hd hN hr rfl hrho extremalExponent_le_three
  have hraw := scheduled_point_fiber_upper ref (0 : Fin (g+1)) k
  calc
    _ ≤ (373248*(coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed-zeta))*
        (N^3*(N*D.thickness/64)^(-extremalExponent)) := by
      simpa only [mul_assoc] using hraw
    _ ≤ (373248*(coreRadix ref.original ref.R L:ℝ)^2*D.thickness^(-seed-zeta))*
        ((64:ℝ)^3*D.thickness^(-extremalExponent-(3-extremalExponent)*rankWindow tau/2)) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by
      have hp : D.thickness^(-seed-zeta)*
          D.thickness^(-extremalExponent-(3-extremalExponent)*rankWindow tau/2)=
          D.thickness^(-extremalExponent-seed-zeta-(3-extremalExponent)*rankWindow tau/2) := by
        rw [←Real.rpow_add hd]
        congr 1
        ring
      calc
        _ = (373248*64^3:ℝ)*(coreRadix ref.original ref.R L:ℝ)^2*
            (D.thickness^(-seed-zeta)*
              D.thickness^(-extremalExponent-(3-extremalExponent)*rankWindow tau/2)) := by ring
        _ = _ := by rw [hp]

/-- A cutoff depending only on tau pays the numeric coefficient. Every
remaining cost is read from ref.cost and its actual parameter margins. -/
theorem exists_point_degree_cutoff (tau : ℝ) (htau : 0 < tau) :
    ∃delta0 : ℝ,0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (seed e zeta : ℝ) (L g : ℕ),
        0 ≤ eta → seed ≤ tau/16384 → zeta ≤ seed/256 →
        0 < g → 1/(g:ℝ) < rankWindow tau/4 → D.thickness ≤ delta0 →
        ∀ref : Reference h tau htau seed e zeta L g,∀k : Index,
          ((ref.E1.filter (fun z => z.2=k)).card:ℝ) ≤
            D.thickness^(-extremalExponent-tau) := by
  obtain ⟨delta0,hdelta0,_hdelta1,hconstantCut⟩ :=
    exists_positive_rpow_absorption_threshold (half_pos htau)
      (by norm_num : (0:ℝ) ≤ 373248*64^3) (by norm_num : (0:ℝ) < 1)
  refine ⟨delta0,hdelta0,?_⟩
  intro n D eta h seed e zeta L g heta hseed hzeta hg hgrid hsmall ref k
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hconstant : (373248*64^3:ℝ) ≤ D.thickness^(-(tau/2)) := by
    have hh := hconstantCut D.thickness hd hsmall
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd (tau/2))).mpr hh
  have hQ := radix_sq_le_of_transfer_cost hd hd1 heta
    (factor ref.dimension (g+1) L) (coreRadix ref.original ref.R L)
    (NativeGenericReferenceData.factor_pos ref) ref.cost
  let loss := seed+zeta+(3-extremalExponent)*rankWindow tau/2+seed/8
  have hw : 0 < rankWindow tau := rankWindow_pos htau
  have hwBound : rankWindow tau ≤ tau/16000 := by
    exact (min_le_right _ _).trans_eq (by ring)
  have hkw := mul_nonneg extremalExponent_nonneg hw.le
  have hloss : loss ≤ tau/2 := by
    dsimp [loss]
    nlinarith
  have hp := first_depth_point_fiber_upper ref hg hgrid k
  calc
    _ ≤ (373248*64^3:ℝ)*(coreRadix ref.original ref.R L:ℝ)^2*
        D.thickness^(-extremalExponent-seed-zeta-(3-extremalExponent)*rankWindow tau/2) := hp
    _ ≤ (373248*64^3:ℝ)*D.thickness^(-(seed/8))*
        D.thickness^(-extremalExponent-seed-zeta-(3-extremalExponent)*rankWindow tau/2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQ (by norm_num)) (by positivity)
    _ = (373248*64^3:ℝ)*D.thickness^(-extremalExponent-loss) := by
      rw [mul_assoc,←Real.rpow_add hd]
      congr 2
      dsimp [loss]
      ring
    _ ≤ D.thickness^(-(tau/2))*D.thickness^(-extremalExponent-loss) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = D.thickness^(-extremalExponent-loss-tau/2) := by
      rw [←Real.rpow_add hd]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)

end NativeFixedReferencePointDegree
