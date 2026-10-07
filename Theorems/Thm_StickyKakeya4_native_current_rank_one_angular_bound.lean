import Theorems.Thm_StickyKakeya4_native_fixed_reference_all_radius_angular_profile
import Theorems.Thm_StickyKakeya4_native_rank_one_slope_cap
import Theorems.Thm_StickyKakeya4_native_two_stage_point_retention
import Theorems.Thm_StickyKakeya4_native_incident_rank_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeCurrentRankOneAngularBound
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeDirectionRankDichotomy NativeIncidentRankSelection
open NativeRankOneSlopeCap NativeFixedReferenceAngularProfile NativeFixedReferenceAllRadiusAngularProfile
open NativeGenericReferenceData NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeTwoStagePointRetention NativeActualMesoscopicRankConfiguration
open scoped BigOperators

/-- The current point's direction set uses the original unit directions and
the original tube indices; it is not a projected or rounded angular cloud. -/
def pointDirections {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (k : Index) : Finset E4 :=
  (pointSet E k).image (fun z => direction (D.line z.1))

/-- At one original point, native fine separation makes this map exactly
injective, even after arbitrary incidence cuts. No multiplicity estimate is
silently reversed. -/
lemma pointDirections_card {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (E : Finset (Fin n × Index)) (k : Index) :
    (pointDirections D E k).card = (pointSet E k).card := by
  apply card_image_iff.mpr
  intro z hz w hw he
  change direction (D.line z.1) = direction (D.line w.1) at he
  have hi : z.1 = w.1 := by
    by_contra hne
    have hs := h.1.2.2.2.2.2.2.2.2.2.1 z.1 w.1 hne
    rw [he, dist_self] at hs
    exact (not_le_of_gt h.1.2.1) hs
  exact Prod.ext hi ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm)

lemma ballIncidences_subset_pointSet {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (k : Index) (v : E4) (r : ℝ) :
    ballIncidences D E k v r ⊆ pointSet E k := by
  intro z hz
  exact mem_filter.mpr ⟨(mem_filter.mp hz).1, (mem_filter.mp hz).2.1⟩

/-- The rank-one near fiber lies in a 384s ball of actual unit directions.
Its center is a literal member of that same near fiber. This works in the
original fixed chart and does not alter the current graph field or offset. -/
theorem current_rank_one_direction_ball {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (E : Finset (Fin n × Index)) (k : Index)
    (P : Submodule ℝ E4) (hP : Module.finrank ℝ P ≤ 1)
    (s : ℝ) (hs : 0 < s) (hs4 : s ≤ 1/4)
    (hne : (pointNear D E k s P).Nonempty) :
    ∃z0 ∈ pointNear D E k s P,
      pointNear D E k s P ⊆ ballIncidences D E k (direction (D.line z0.1)) (384*s) := by
  obtain ⟨z0,hz0,hcap⟩ := near_labels_cap (pointSet E k)
    (fun z => slopeVector D z.1) P hP 2 s hs hs4
    (fun z _ => slopeVector_last D z.1)
    (fun z _ => slopeVector_norm_le_two h z.1) hne
  refine ⟨z0,hz0,?_⟩
  intro z hz
  have hc : ‖slopeVector D z.1 - slopeVector D z0.1‖ ≤ 48*s := by
    convert hcap z hz using 1
    norm_num
  have hcoord (j : Fin 3) : |slope (D.line z.1) j - slope (D.line z0.1) j| ≤ 48*s := by
    simpa only [PiLp.sub_apply, slopeVector, ActualSlopeSource.heightPoint_castSucc] using
      (coordinate_abs_le_norm (slopeVector D z.1 - slopeVector D z0.1) j.castSucc).trans hc
  have hdist : dist (slope (D.line z.1)) (slope (D.line z0.1)) ≤ 48*s := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro j
    simpa only [Real.dist_eq] using hcoord j
  have hdir := NativeOriginalSlopeCubePacking.direction_dist_le_eight_slope_dist
    (D.line z.1) (D.line z0.1) (h.1.2.2.2.2.1 z.1) (h.1.2.2.2.2.1 z0.1)
    (h.2.1.1 z.1) (h.2.1.1 z0.1)
  obtain ⟨hzE,hzk⟩ := mem_filter.mp (mem_filter.mp hz).1
  refine mem_filter.mpr ⟨hzE,hzk,?_⟩
  linarith

/-- An actual direction-ball upper is an upper for the original current
incidence fiber, with no angular-realizer multiplicity loss. -/
theorem current_rank_one_upper_of_balls {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (Eref E : Finset (Fin n × Index)) (hE : E ⊆ Eref) (k : Index)
    (P : Submodule ℝ E4) (hP : Module.finrank ℝ P ≤ 1)
    (s U : ℝ) (hs : 0 < s) (hs4 : s ≤ 1/4) (hU : 0 ≤ U)
    (hball : ∀v : E4, ((ballDirections D Eref k v (384*s)).card:ℝ) ≤ U) :
    ((pointNear D E k s P).card:ℝ) ≤ U := by
  by_cases hne : (pointNear D E k s P).Nonempty
  · obtain ⟨z0,_hz0,hsub⟩ := current_rank_one_direction_ball h E k P hP s hs hs4 hne
    have hsref : ballIncidences D E k (direction (D.line z0.1)) (384*s) ⊆
        ballIncidences D Eref k (direction (D.line z0.1)) (384*s) := filter_subset_filter _ hE
    have hh := hball (direction (D.line z0.1))
    rw [ballDirections_card h] at hh
    exact (show ((pointNear D E k s P).card:ℝ) ≤
      (ballIncidences D Eref k (direction (D.line z0.1)) (384*s)).card by
        exact_mod_cast card_le_card (hsub.trans hsref)).trans hh
  · rw [not_nonempty_iff_eq_empty.mp hne,card_empty,Nat.cast_zero]
    exact hU

/-- The unchanged reference's AD lower at radius one gives its literal
point-degree lower. The ball need not contain all reference directions. -/
lemma reference_degree_lower {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (Eref : Finset (Fin n × Index))
    (tau : ℝ) (i : Fin n) (k : Index) (hik : (i,k) ∈ Eref)
    (hlo : ∀i k, (i,k) ∈ Eref →
      D.thickness^tau*(1/D.thickness)^extremalExponent ≤
        (ballDirections D Eref k (direction (D.line i)) 1).card) :
    D.thickness^tau*(1/D.thickness)^extremalExponent ≤ (pointSet Eref k).card := by
  have hh := hlo i k hik
  rw [ballDirections_card h] at hh
  exact hh.trans (by exact_mod_cast card_le_card (ballIncidences_subset_pointSet D Eref k _ 1))

/-- Scalar normalization cancels the ORIGINAL fine-scale angular power.
The factor K is an actual degree loss; K=1 applies to the reference itself. -/
lemma normalize_angular_bound {delta tau kappa s count degree K : ℝ}
    (hd : 0 < delta) (hs : 0 < s)
    (hdegree : delta^tau*(1/delta)^kappa ≤ K*degree)
    (hupper : count ≤ delta^(-tau)*((384*s)/delta)^kappa) :
    count ≤ (K*(384:ℝ)^kappa*delta^(-2*tau))*s^kappa*degree := by
  let A : ℝ := delta^tau*(1/delta)^kappa
  have hA : 0 < A := by dsimp [A]; positivity
  have hratio : 1 ≤ (K*degree)/A := (one_le_div hA).mpr hdegree
  have hmul := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ delta^(-tau)*((384*s)/delta)^kappa by positivity)
  rw [mul_one] at hmul
  apply hupper.trans (hmul.trans_eq ?_)
  have hscale : ((384*s)/delta)^kappa =
      (384:ℝ)^kappa*s^kappa*(1/delta)^kappa := by
    rw [show (384*s)/delta=(384*s)*(1/delta) by ring,
      Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) hs.le]
  have hcancel : delta^(-tau)/delta^tau = delta^(-2*tau) := by
    rw [←Real.rpow_sub hd]
    congr 1
    ring
  rw [hscale]
  dsimp only [A]
  have hp : (1/delta)^kappa ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  have ht : delta^tau ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  rw [←hcancel]
  field_simp [hp,ht]

/-- Paid conversion from absolute angular AD counts to the SAME retained
point denominator. The pointwise retention is derived from two actual
uniformities and total retention; it is not inferred from subset inclusion. -/
theorem current_rank_one_relative_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (Eref E : Finset (Fin n × Index)) (hE : E ⊆ Eref) (Qref Q : ℕ)
    (Href : HasUniformFibers Eref Qref Prod.snd) (HE : HasUniformFibers E Q Prod.snd)
    (lambda G tau : ℝ) (hlambda : 0 < lambda) (hG : 0 ≤ G)
    (hret : lambda*(Eref.card:ℝ) ≤ G*E.card)
    (hlo : ∀i k, (i,k) ∈ Eref →
      D.thickness^tau*(1/D.thickness)^extremalExponent ≤
        (ballDirections D Eref k (direction (D.line i)) 1).card)
    (hup : ∀k v r, D.thickness ≤ r → r ≤ 1 →
      ((ballDirections D Eref k v r).card:ℝ) ≤
        D.thickness^(-tau)*(r/D.thickness)^extremalExponent)
    (k : Index) (hk : k ∈ E.image Prod.snd)
    (P : Submodule ℝ E4) (hP : Module.finrank ℝ P ≤ 1)
    (s : ℝ) (hs : 0 < s) (hslo : D.thickness ≤ 384*s) (hshi : 384*s ≤ 1) :
    ((pointNear D E k s P).card:ℝ) ≤
      ((G*(Qref:ℝ)^2*(Q:ℝ)^2/lambda)*(384:ℝ)^extremalExponent*
        D.thickness^(-2*tau))*s^extremalExponent*((pointSet E k).card:ℝ) := by
  have hd := h.1.2.1
  obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
  have hpoint : lambda*((pointSet Eref k).card:ℝ) ≤
      G*(Qref:ℝ)^2*(Q:ℝ)^2*((pointSet E k).card:ℝ) := by
    simpa only [pointSet,hzk] using point_retention_of_two_uniformities
      Eref E hE Qref Q Href HE lambda G hlambda.le hG hret z hz
  have hzref : (z.1,k) ∈ Eref := by simpa only [←hzk] using hE hz
  have hloDeg := reference_degree_lower h Eref tau z.1 k hzref hlo
  have hdegree : lambda*(D.thickness^tau*(1/D.thickness)^extremalExponent) ≤
      G*(Qref:ℝ)^2*(Q:ℝ)^2*((pointSet E k).card:ℝ) :=
    (mul_le_mul_of_nonneg_left hloDeg hlambda.le).trans hpoint
  have habs := current_rank_one_upper_of_balls h Eref E hE k P hP s
    (D.thickness^(-tau)*((384*s)/D.thickness)^extremalExponent)
    hs (by linarith) (by positivity) (fun v => hup k v _ hslo hshi)
  have hdegree' : D.thickness^tau*(1/D.thickness)^extremalExponent ≤
      (G*(Qref:ℝ)^2*(Q:ℝ)^2/lambda)*((pointSet E k).card:ℝ) := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlambda).mpr (by simpa only [mul_comm] using hdegree)
  exact normalize_angular_bound hd hs hdegree' habs

/-- A point with a surviving original incidence has positive literal degree. -/
lemma current_degree_pos {n : ℕ} (E : Finset (Fin n × Index)) (k : Index)
    (hk : k ∈ E.image Prod.snd) : (0:ℝ) < (pointSet E k).card := by
  obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
  exact_mod_cast card_pos.mpr (show (pointSet E k).Nonempty from
    ⟨z,mem_filter.mpr ⟨hz,hzk⟩⟩)

/-- The necessary source/menu budget is visible. A positive exponent gap
alone does not absorb the source loss or the actual post-cut degree loss. -/
lemma rank_one_threshold_failure {count degree C s kappa beta : ℝ}
    (hs : 0 < s) (hdegree : 0 < degree)
    (hupper : count ≤ C*s^kappa*degree)
    (hbudget : C*s^(kappa-beta) < 1) : count < s^beta*degree := by
  have hp : 0 < s^beta := Real.rpow_pos_of_pos hs _
  have hpow : s^kappa = s^(kappa-beta)*s^beta := by
    rw [←Real.rpow_add hs]
    congr 1
    ring
  have hh := mul_lt_mul_of_pos_right hbudget (mul_pos hp hdegree)
  apply hupper.trans_lt
  rw [hpow]
  nlinarith only [hh]

/-- Actual global retention after choosing a parent keeps its true fraction
of the original reference. This identity does not replace that fraction by
a constant or infer pointwise retention from the parent subset alone. -/
lemma global_retention_from_parent {n : ℕ}
    (Eref Eparent E : Finset (Fin n × Index)) (hRef : Eref.Nonempty)
    (lambda G : ℝ) (hret : lambda*(Eparent.card:ℝ) ≤ G*E.card) :
    (lambda*((Eparent.card:ℝ)/(Eref.card:ℝ)))*(Eref.card:ℝ) ≤ G*E.card := by
  have hn : (Eref.card:ℝ) ≠ 0 := (show (0:ℝ) < Eref.card by
    exact_mod_cast card_pos.mpr hRef).ne'
  rw [mul_assoc,div_mul_cancel₀ _ hn]
  exact hret

/-- The composed parent and third-core costs remain explicit and refer to
the same original incidence sets. In particular, no sparse shading is
readmitted as a new native source. -/
lemma compose_actual_parent_retention {n : ℕ}
    (Eparent E2parent E : Finset (Fin n × Index))
    (population lambda G : ℝ) (hlambda : 0 ≤ lambda)
    (hparent : population*(Eparent.card:ℝ) ≤ E2parent.card)
    (hthird : lambda*(E2parent.card:ℝ) ≤ G*E.card) :
    (lambda*population)*(Eparent.card:ℝ) ≤ G*E.card := by
  exact (show (lambda*population)*(Eparent.card:ℝ) ≤ lambda*(E2parent.card:ℝ) by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hparent hlambda).trans hthird

/-- A single cutoff from the already proved all-radius theorem, before D
and the same Reference, gives weighted rank-one bounds on every current
incidence cut with its actual uniformity and retention. The original tube
index, original point, sigma, and actual current denominator never change. -/
theorem exists_current_rank_one_upper (tau : ℝ) (htau : 0 < tau) :
    ∃delta0 : ℝ, 0 < delta0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (seed e zeta : ℝ) (L g : ℕ),
        0 ≤ eta → seed ≤ tau/16384 → 0 < g → 1/(g:ℝ) < rankWindow tau/4 →
        D.thickness ≤ delta0 →
      ∀ref : Reference h tau htau seed e zeta L g,
      ∀E : Finset (Fin n × Index), E ⊆ ref.E1 →
      ∀Q : ℕ, HasUniformFibers E Q Prod.snd →
      ∀lambda G : ℝ, 0 < lambda → 0 ≤ G → lambda*(ref.E1.card:ℝ) ≤ G*E.card →
      ∀k ∈ E.image Prod.snd, ∀P : Submodule ℝ E4, Module.finrank ℝ P ≤ 1 →
      ∀s : ℝ, 0 < s → D.thickness ≤ 384*s → 384*s ≤ 1 →
        let C := (G*(coreRadix ref.original ref.R L:ℝ)^2*(Q:ℝ)^2/lambda)*
          (384:ℝ)^extremalExponent*D.thickness^(-2*tau)
        ((pointNear D E k s P).card:ℝ) ≤ C*s^extremalExponent*((pointSet E k).card:ℝ) ∧
        ∀beta : ℝ, C*s^(extremalExponent-beta) < 1 →
          ((pointNear D E k s P).card:ℝ) < s^beta*((pointSet E k).card:ℝ) := by
  obtain ⟨delta0,hd0,H⟩ := exists_all_radius_cutoff tau htau
  refine ⟨delta0,hd0,?_⟩
  intro n D eta h seed e zeta L g heta hseed hg hgrid hsmall ref E hE Q HE lambda G
    hlambda hG hret k hk P hP s hs hslo hshi C
  obtain ⟨hlo,hup⟩ := H n D eta h seed e zeta L g heta hseed hg hgrid hsmall ref
  have hu := current_rank_one_relative_upper h ref.E1 E hE
    (coreRadix ref.original ref.R L) Q ref.point HE lambda G tau hlambda hG hret
    (fun i k hik => hlo i k hik 1 h.1.2.2.1 le_rfl) hup k hk P hP s hs hslo hshi
  refine ⟨hu,?_⟩
  intro beta hbudget
  exact rank_one_threshold_failure hs (current_degree_pos E k hk) hu hbudget

/-- A source-independent smallness cutoff pays the exact current loss when
its proven exponent is loss. The radius upper is on this same original
sigma scale. This works for every kappa>beta, including 0<kappa≤1; no
kappa>1 contradiction is used. -/
theorem exists_rank_one_gap_cutoff (kappa beta tau loss a C : ℝ)
    (hgap : 2*tau+loss < a*(kappa-beta)) (hexp : beta < kappa) (hC : 0 ≤ C) :
    ∃delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀s K : ℝ, 0 < s → s ≤ delta^a → 0 ≤ K → K ≤ delta^(-loss) →
        (K*C*delta^(-2*tau))*s^(kappa-beta) < 1 := by
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < a*(kappa-beta)-(2*tau+loss) by linarith) hC
    (by norm_num : (0:ℝ) < 1/2)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall s K hs hscale hK hKloss
  have hpow : s^(kappa-beta) ≤ delta^(a*(kappa-beta)) := by
    exact (Real.rpow_le_rpow hs.le hscale (sub_pos.mpr hexp).le).trans_eq
      (Real.rpow_mul hd.le a (kappa-beta)).symm
  have hh : (K*C*delta^(-2*tau))*s^(kappa-beta) ≤
      C*delta^(a*(kappa-beta)-(2*tau+loss)) := by
    calc
      _ ≤ (delta^(-loss)*C*delta^(-2*tau))*delta^(a*(kappa-beta)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKloss hC)
          (Real.rpow_nonneg hd.le _)) hpow (Real.rpow_nonneg hs.le _)
          (by positivity)
      _ = C*(delta^(-loss)*delta^(-2*tau)*delta^(a*(kappa-beta))) := by ring
      _ = _ := by
        rw [←Real.rpow_add hd,←Real.rpow_add hd]
        congr 2
        ring
  exact (hh.trans (H delta hd hsmall)).trans_lt (by norm_num)

/-- When a fresh literal current source has already supplied its Reference,
test rank directly on that SAME E1. Radius-one AD normalizes by its own
point degree with no old-parent ratio and no superfluous uniformity radix.
This theorem does not construct or assume the preceding offset-source cut. -/
theorem exists_reference_rank_one_upper (tau : ℝ) (htau : 0 < tau) :
    ∃delta0 : ℝ, 0 < delta0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (seed e zeta : ℝ) (L g : ℕ),
        0 ≤ eta → seed ≤ tau/16384 → 0 < g → 1/(g:ℝ) < rankWindow tau/4 →
        D.thickness ≤ delta0 →
      ∀ref : Reference h tau htau seed e zeta L g,
      ∀k ∈ ref.E1.image Prod.snd, ∀P : Submodule ℝ E4, Module.finrank ℝ P ≤ 1 →
      ∀s : ℝ, 0 < s → D.thickness ≤ 384*s → 384*s ≤ 1 →
        let C := (384:ℝ)^extremalExponent*D.thickness^(-2*tau)
        ((pointNear D ref.E1 k s P).card:ℝ) ≤ C*s^extremalExponent*((pointSet ref.E1 k).card:ℝ) ∧
        ∀beta : ℝ, C*s^(extremalExponent-beta) < 1 →
          ((pointNear D ref.E1 k s P).card:ℝ) < s^beta*((pointSet ref.E1 k).card:ℝ) := by
  obtain ⟨delta0,hd0,H⟩ := exists_all_radius_cutoff tau htau
  refine ⟨delta0,hd0,?_⟩
  intro n D eta h seed e zeta L g heta hseed hg hgrid hsmall ref k hk P hP s hs hslo hshi C
  obtain ⟨hlo,hup⟩ := H n D eta h seed e zeta L g heta hseed hg hgrid hsmall ref
  obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
  have hzkref : (z.1,k) ∈ ref.E1 := by simpa only [←hzk] using hz
  have hdeg := reference_degree_lower h ref.E1 tau z.1 k hzkref
    (fun i k hik => hlo i k hik 1 h.1.2.2.1 le_rfl)
  have habs := current_rank_one_upper_of_balls h ref.E1 ref.E1 (Subset.refl _) k P hP s
    (D.thickness^(-tau)*((384*s)/D.thickness)^extremalExponent)
    hs (by linarith) (by have hd := h.1.2.1; positivity)
    (fun v => hup k v _ hslo hshi)
  have hu : ((pointNear D ref.E1 k s P).card:ℝ) ≤ C*s^extremalExponent*((pointSet ref.E1 k).card:ℝ) := by
    simpa only [one_mul] using normalize_angular_bound (K:=1) h.1.2.1 hs
      (by simpa only [one_mul] using hdeg) habs
  refine ⟨hu,?_⟩
  intro beta hbudget
  exact rank_one_threshold_failure hs (current_degree_pos ref.E1 k hk) hu hbudget

/-- Concrete source-native rank-one exclusion on the fresh reference E1.
The cutoff precedes the source and the reference, and pays all AD losses.
Only the actual original-scale menu endpoint guards and a positive exponent
margin are inputs. In particular the argument applies throughout 0<kappa≤1.
To join the graph cap, the separate literal-source construction must also
supply its actual graph residual on this very E1. -/
theorem exists_reference_rank_one_exclusion (tau beta a : ℝ) (htau : 0 < tau)
    (hbeta : beta < extremalExponent) (hgap : 2*tau < a*(extremalExponent-beta)) :
    ∃delta0 : ℝ, 0 < delta0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta)
        (seed e zeta : ℝ) (L g : ℕ),
        0 ≤ eta → seed ≤ tau/16384 → 0 < g → 1/(g:ℝ) < rankWindow tau/4 →
        D.thickness ≤ delta0 →
      ∀ref : Reference h tau htau seed e zeta L g,
      ∀k ∈ ref.E1.image Prod.snd, ∀P : Submodule ℝ E4, Module.finrank ℝ P ≤ 1 →
      ∀s : ℝ, 0 < s → D.thickness ≤ 384*s → 384*s ≤ 1 → s ≤ D.thickness^a →
        ((pointNear D ref.E1 k s P).card:ℝ) < s^beta*((pointSet ref.E1 k).card:ℝ) := by
  obtain ⟨dAD,hdAD,HAD⟩ := exists_reference_rank_one_upper tau htau
  obtain ⟨dGap,hdGap,_hdGap1,HGap⟩ := exists_rank_one_gap_cutoff
    extremalExponent beta tau 0 a ((384:ℝ)^extremalExponent)
    (by simpa only [add_zero] using hgap) hbeta (Real.rpow_nonneg (by norm_num) _)
  refine ⟨min dAD dGap,lt_min hdAD hdGap,?_⟩
  intro n D eta h seed e zeta L g heta hseed hg hgrid hsmall ref k hk P hP s hs hslo hshi hscale
  have hsmallAD := hsmall.trans (min_le_left _ _)
  have hsmallGap := hsmall.trans (min_le_right _ _)
  have H := HAD n D eta h seed e zeta L g heta hseed hg hgrid hsmallAD ref k hk P hP s hs hslo hshi
  apply H.2 beta
  have hh := HGap D.thickness h.1.2.1 hsmallGap s 1 hs hscale (by norm_num)
    (by simp only [neg_zero,Real.rpow_zero,le_refl])
  simpa only [one_mul] using hh

/-- A concentration witness returned by a finite selector cannot have its
rank-one index when the actual same-fiber tests are all strictly below their
rank-one thresholds. This does not assert that arbitrary current cuts obey
those tests without the paid source/retention budget above. -/
theorem selected_rank_ne_zero {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E F : Finset (Fin n × Index))
    (ell : Fin 3) (j : ι) (allowed : Fin 3 → Finset ι) (hj : j ∈ allowed ell)
    (radius : ι → ℝ) (beta : Fin 3 → ℝ) (P : Index → Submodule ℝ E4)
    (hFn : F.Nonempty)
    (Hselected : ∀k ∈ F.image Prod.snd,
      Module.finrank ℝ (P k) ≤ ell.val+1 ∧
      (radius j)^(beta ell)*((pointSet E k).card:ℝ) ≤
        (pointNear D E k (radius j) (P k)).card)
    (Hfailed : ∀k ∈ F.image Prod.snd, ∀test ∈ allowed (0 : Fin 3),
      ∀Q : Submodule ℝ E4, Module.finrank ℝ Q ≤ 1 →
      ((pointNear D E k (radius test) Q).card:ℝ) <
        (radius test)^(beta (0 : Fin 3))*((pointSet E k).card:ℝ)) : ell ≠ 0 := by
  intro hell
  subst ell
  obtain ⟨z,hz⟩ := hFn
  have hk := mem_image_of_mem Prod.snd hz
  obtain ⟨hdim,hmass⟩ := Hselected z.2 hk
  exact (not_lt_of_ge hmass) (Hfailed z.2 hk j hj (P z.2) hdim)

end NativeCurrentRankOneAngularBound
