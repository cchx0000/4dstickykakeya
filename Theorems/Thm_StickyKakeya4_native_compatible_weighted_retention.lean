import Theorems.Thm_StickyKakeya4_native_angular_candidate_capacity_product
import Theorems.Thm_StickyKakeya4_native_actual_angular_menu_cost
import Theorems.Thm_StickyKakeya4_native_quarter_scale_parameters

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

noncomputable section
namespace NativeCompatibleWeightedRetention
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeCompatibleAngularCandidates NativeAngularCandidateCapacityProduct
open NativeOriginalAngularTupleMenu NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeTwoScaleConfiguration NativeFixedCompactKakeyaExponent NativeFixedSizeScaleMenu
open NativeMiddleWindowBalance NativeAllTwoScaleConfiguration NativeIncidentRankSelection
open NativeDirectionRankDichotomy NativeLocalPairUniformCore NativeLocalMenuInterpolation SelfUniform
open scoped BigOperators

/-- All fixed angular-menu costs, before taking the actual rank power. -/
def menuCost (J : ℕ) : ℝ := 686*(259:ℝ)^3*(2*costConstant)^J

def combinedLoss (seed c2 tau : ℝ) (J : ℕ) : ℝ := 11*seed/8+c2+3*tau*(J:ℝ)

/-- Exact retained fraction after cancelling the actual terminal angular scale. -/
def retainedFraction (delta lambda seed c2 tau : ℝ) (J ell : ℕ) : ℝ :=
  ((lambda/menuCost J)*delta^(combinedLoss seed c2 tau J))^ell

lemma menuCost_pos (J : ℕ) : 0 < menuCost J := by
  have hC : 0 < costConstant := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) costConstant_one_le
  unfold menuCost
  positivity

/-- The rank loss lambda is paid exactly once before the rank power. All
source-delta exponents and all fixed constants remain explicit. -/
lemma retainedFraction_closed_form {delta : ℝ} (hd : 0 < delta)
    (lambda seed c2 tau : ℝ) (J ell : ℕ) :
    retainedFraction delta lambda seed c2 tau J ell=
      lambda^ell/((686:ℝ)^ell*((259:ℝ)^3)^ell*(2*costConstant)^(J*ell))*
        delta^((ell:ℝ)*(11*seed/8+c2)+3*tau*((J*ell:ℕ):ℝ)) := by
  unfold retainedFraction
  rw [mul_pow,div_pow,←Real.rpow_mul_natCast hd.le]
  have hcost : (menuCost J)^ell=(686:ℝ)^ell*((259:ℝ)^3)^ell*(2*costConstant)^(J*ell) := by
    simp only [menuCost,mul_pow,←pow_mul]
  rw [hcost]
  congr 1
  congr 1
  simp only [combinedLoss,Nat.cast_mul]
  ring

/-- The exact successor denominator written as one rank power. -/
lemma denominator_power {delta rho : ℝ} (hd : 0 < delta) (hrho : 0 < rho)
    (tau kappa : ℝ) (J ell : ℕ) :
    (((259:ℝ)^3*(2*costConstant)^J)*(delta^(-(3*tau*(J:ℝ)))*rho^(-kappa)))^ell=
      ((259:ℝ)^3)^ell*((2*costConstant)^(J*ell)*
        delta^(-(3*tau)*((J*ell:ℕ):ℝ))*rho^(-(kappa*(ell:ℝ)))) := by
  have hdelt : (delta^(-(3*tau*(J:ℝ))))^ell=delta^(-(3*tau)*((J*ell:ℕ):ℝ)) := by
    rw [←Real.rpow_mul_natCast hd.le]
    congr 1
    push_cast
    ring
  have hrhop : (rho^(-kappa))^ell=rho^(-(kappa*(ell:ℝ))) := by
    rw [←Real.rpow_mul_natCast hrho.le]
    congr 1
    ring
  simp only [mul_pow,←pow_mul,hdelt,hrhop]
  ring

/-- Cancel the common terminal angular scale in the actual lower/upper
inequalities. The weights on I and S are unchanged original-point weights. -/
theorem cancel_terminal_scale {delta rho : ℝ} (hd : 0 < delta) (hrho : 0 < rho)
    (lambda seed c2 tau kappa : ℝ) (J ell : ℕ) (M N S : ℝ)
    (hlower : ((lambda/686)*delta^(11*seed/8+c2)*rho^(-kappa))^ell*M ≤ N)
    (hupper : N ≤ ((259:ℝ)^3)^ell*((2*costConstant)^(J*ell)*
      delta^(-(3*tau)*((J*ell:ℕ):ℝ))*rho^(-(kappa*(ell:ℝ))))*S) :
    retainedFraction delta lambda seed c2 tau J ell*M ≤ S := by
  let K := (259:ℝ)^3*(2*costConstant)^J
  let A := 11*seed/8+c2
  let b := 3*tau*(J:ℝ)
  let Den := K*(delta^(-b)*rho^(-kappa))
  have hK : 0 < K := by
    have hC : 0 < costConstant := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) costConstant_one_le
    dsimp [K]
    positivity
  have hDen : 0 < Den := by dsimp [Den]; positivity
  have hdelt : delta^(A+b)*delta^(-b)=delta^A := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hMenu : menuCost J=686*K := by dsimp [menuCost,K]; ring
  have hbase : ((lambda/menuCost J)*delta^(combinedLoss seed c2 tau J))*Den=
      (lambda/686)*delta^A*rho^(-kappa) := by
    rw [hMenu]
    change ((lambda/(686*K))*delta^(A+b))*(K*(delta^(-b)*rho^(-kappa)))=_
    calc
      _ = (lambda/686)*(delta^(A+b)*delta^(-b))*rho^(-kappa) := by field_simp [hK.ne']
      _ = _ := by rw [hdelt]
  apply (mul_le_mul_iff_right₀ (pow_pos hDen ell)).mp
  calc
    _ = (((lambda/menuCost J)*delta^(combinedLoss seed c2 tau J))*Den)^ell*M := by
      unfold retainedFraction
      rw [mul_pow]
      ring
    _ = ((lambda/686)*delta^A*rho^(-kappa))^ell*M := by rw [hbase]
    _ ≤ N := hlower
    _ ≤ _ := hupper
    _ = Den^ell*S := by
      dsimp [Den,K,b]
      rw [denominator_power hd hrho]

/-- Retention on literal original points, together with the actual selected
pair family, its local witnesses, and its compatible candidate tree. -/
def RetainedFamily {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (stop : ℕ)
    (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ) (w : Index → ℕ)
    (J : ℕ) (fraction : ℝ) : Prop :=
  ∃P⊆terminalFamily D a stop E2 q ell, ∃S⊆E2.image Prod.snd,
    S=P.image Prod.fst ∧
    (∀x y,x∈P → y∈P → x.1=y.1 → x=y) ∧
    SelfUniform.mass (fun p => w p.1) P=SelfUniform.mass w S ∧
    fraction*(SelfUniform.mass w (E2.image Prod.snd):ℝ) ≤ (SelfUniform.mass w S:ℝ) ∧
    (∀j,j<J+1 → ∀x y,x∈P → y∈P →
      NativeSpatialAngularGeometry.spatialLabel D (2^(depth J stop j)) x.1=
        NativeSpatialAngularGeometry.spatialLabel D (2^(depth J stop j)) y.1 →
      projectWord stop (depth J stop j) x.2=projectWord stop (depth J stop j) y.2) ∧
    (∀p∈P,LocalWitness D a stop E2 q ell p) ∧
    ∀j,j<J → ∀v∈P.image (node D J stop (j+1)),
      ancestorNode (depth J stop (j+1)) (depth J stop j) v∈P.image (node D J stop j) ∧
      (candidate D J stop (j+1) P v ∩ candidate D J stop j P
        (ancestorNode (depth J stop (j+1)) (depth J stop j) v)).Nonempty

lemma retainedFamily_mono {n : ℕ} {D : FiniteScaleSource n} {a q : ℝ}
    {stop ell J : ℕ} {E2 : Finset (Fin n × Index)} {w : Index → ℕ}
    {f g : ℝ} (hfg : f ≤ g) (H : RetainedFamily D a stop E2 q ell w J g) :
    RetainedFamily D a stop E2 q ell w J f := by
  obtain ⟨P,hP,S,hSsub,hS,hinj,hmass,hret,hcompat,hwitness,htrace⟩ := H
  exact ⟨P,hP,S,hSsub,hS,hinj,hmass,
    (mul_le_mul_of_nonneg_right hfg (Nat.cast_nonneg _)).trans hret,hcompat,hwitness,htrace⟩

/-- Combine already-constructed actual candidates and the actual weighted
terminal numerator, cancelling its scale factor before estimating any loss. -/
theorem exact_retention_from_numerator {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (stop : ℕ)
    (E2 : Finset (Fin n × Index)) (q : ℝ) (ell : ℕ) (w : Index → ℕ)
    (J : ℕ) (hJ : 0 < J) (hstop : 6 ≤ stop)
    (lambda seed c2 tau : ℝ) (htau : 0 ≤ tau)
    (HC : HasCompatibleCandidates D a stop E2 q ell w J (3*tau) extremalExponent)
    (HN : ((lambda/686)*D.thickness^(11*seed/8+c2)*
        ((64:ℝ)/((2^stop:ℕ):ℝ))^(-extremalExponent))^ell*
        (SelfUniform.mass w (E2.image Prod.snd):ℝ) ≤
      ((∑k∈E2.image Prod.snd,w k*(angularMenu D a stop E2 k q ell).card:ℕ):ℝ)) :
    RetainedFamily D a stop E2 q ell w J
      (retainedFraction D.thickness lambda seed c2 tau J ell) := by
  obtain ⟨P,hP,S,hSsub,hS,hinj,hmass,hret,hcompat,hwitness,htrace⟩ := HC
  have hcast : ((∑k∈E2.image Prod.snd,w k*(angularMenu D a stop E2 k q ell).card:ℕ):ℝ) ≤
      ((∏j∈range (J+1),selectionBudget D (3*tau) extremalExponent J stop ell j:ℕ):ℝ)*
        (SelfUniform.mass w S:ℝ) := by exact_mod_cast hret
  have hbudget := native_master_product_bound h htau J stop ell hJ hstop
  have hupper := hcast.trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _))
  refine ⟨P,hP,S,hSsub,hS,hinj,hmass,?_,hcompat,hwitness,htrace⟩
  exact cancel_terminal_scale h.1.2.1 (by positivity) lambda seed c2 tau extremalExponent
    J ell _ _ _ HN hupper

/-- The actual master witness, actual E2 retention and raw refinement costs
supply both sides of the exact comparison. No terminal-menu lower bound,
compatible-candidate certificate, or desired retained fraction is assumed. -/
theorem from_master_and_actual_cost {n d g L level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F E2 : Finset (Fin n × Index)) (h21 : E2⊆E1)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (htau : 0 < tau) (heta : 0 ≤ eta) (hseed : seed ≤ tau/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4)
    (hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule = fullSchedule tau htau g level)
    (hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E1)
    (hcost1 : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (J stop d2 L2 : ℕ) (hJ : 0 < J) (hstop : stop ≤ level) (hsix : 6 ≤ stop)
    (r etaRank : ℝ) (hr : 0 < r)
    (hret : (r^etaRank/(4*((g:ℝ)+1)))*(E1.card:ℝ) ≤
      (retentionCost d2 1 L2:ℝ)*E2.card)
    (hnear : D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity E1)
    (hcost2 : (125*175616*16384:ℝ)*(factor d2 1 L2:ℝ)*
      (NativeSourceSizeBounds.radix F.card L2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (hOld : ∀x y,x∈E1 → y∈E1 →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^stop)) E1 x ≤
      (coreRadix original R L)^2*
        degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^stop)) E1 y)
    (Hpoint : HasUniformFibers E2 (NativeSourceSizeBounds.radix F.card L2) Prod.snd)
    (hupper : ∀p,(parentEdges D a (2^stop) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^stop) E1 p) ≤
        D.thickness^(-seed)*((((2^stop:ℕ):ℝ)*D.thickness/64)^(-extremalExponent)))
    (q : ℝ) (hq : 0 < q) (ell : ℕ)
    (Hchains : ∀k∈E2.image Prod.snd,
      (((pointSet E2 k).card:ℝ)/2)^ell ≤
        ((chains (pointSet E2 k) (fun z => slopeVector D z.1) q ell).card:ℝ))
    (w : Index → ℕ) :
    RetainedFamily D a stop E2 q ell w J
      (retainedFraction D.thickness (r^etaRank/(4*((g:ℝ)+1))) seed c2 tau J ell) := by
  have HC := NativeCompatibleAngularCandidates.from_master_reference h original R E1 E2 h21 schedule Rel
    htau heta hseed hg hgl hgrid hbackbone hschedule hcore hcost1 hconditioned hreference
    J stop hJ hstop q hq ell w
  have hE2 : E2⊆incidences original := h21.trans (hcore.1.trans (filter_subset _ _))
  have hscale : ((2^stop:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hbackbone.2.1 hstop]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have HN := NativeActualAngularMenuCost.stopping_weighted_numerator h heta original hbackbone.1
    hbackbone.2.2.1 R E1 F E2 h21 hE2 L L2 stop hscale r etaRank hr hret hnear
    hcost1 hcost2 hOld Hpoint hupper q ell Hchains w
  exact exact_retention_from_numerator h a stop E2 q ell w J hJ hsix
    (r^etaRank/(4*((g:ℝ)+1))) seed c2 tau htau.le HC HN

/-- With J fixed before tau, the stated caller bound leaves at least half of
commonBudget unused after all delta losses in the exact retained fraction. -/
lemma combinedLoss_budget {t seed c2 tau : ℝ} (J : ℕ) (ht : 0 < t)
    (htau : 0 ≤ tau) (hseed0 : 0 ≤ seed) (hseed : seed ≤ tau/16384)
    (hsmall : tau ≤ t/(1000*((J:ℝ)+1))) (hc2 : c2=t/4) :
    0 ≤ combinedLoss seed c2 tau J ∧ combinedLoss seed c2 tau J ≤ t/2 := by
  have hJR : (0:ℝ) ≤ J := Nat.cast_nonneg _
  have hden : (0:ℝ) < 1000*((J:ℝ)+1) := by positivity
  have hpaid := (le_div_iff₀ hden).mp hsmall
  have hprod : 0 ≤ tau*(J:ℝ) := mul_nonneg htau hJR
  have hseedtau : 11*seed/8 ≤ tau := by nlinarith
  have htail : tau+3*tau*(J:ℝ) ≤ t/4 := by nlinarith
  rw [combinedLoss,hc2]
  constructor
  · positivity
  · linarith

/-- Convert an actual original-delta loss using the actual stopping-scale
upper bound; the inequality direction preserves a lower retained fraction. -/
lemma delta_loss_lower {delta r a s : ℝ} (hd : 0 < delta) (hr : 0 ≤ r)
    (ha : 0 < a) (hs : 0 ≤ s) (hscale : r ≤ delta^a) : r^(s/a) ≤ delta^s := by
  calc
    _ ≤ (delta^a)^(s/a) := Real.rpow_le_rpow hr hscale (div_nonneg hs ha.le)
    _ = _ := by
      rw [←Real.rpow_mul hd.le]
      congr 1
      field_simp [ha.ne']

/-- A source-uniform threshold depending on the already chosen g, J and
commonBudget t. It is independent of the later source, stopping depth, rank,
rank dimension and tuple length. -/
theorem exists_rank_retention_cutoff (g J : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀aRank etaRank seed c2 tau r : ℝ,
        0 < aRank → 0 < etaRank → t=aRank*etaRank →
        0 ≤ tau → 0 ≤ seed → seed ≤ tau/16384 →
        tau ≤ t/(1000*((J:ℝ)+1)) → c2=t/4 →
        0 < r → r ≤ 1 → r ≤ delta^aRank →
        ∀ell : ℕ,r^(2*(ell:ℝ)*etaRank) ≤
          retainedFraction delta (r^etaRank/(4*((g:ℝ)+1))) seed c2 tau J ell := by
  let K := 4*((g:ℝ)+1)*menuCost J
  have hK : 0 < K := by dsimp [K]; exact mul_pos (by positivity) (menuCost_pos J)
  obtain ⟨delta0,hd0,hd01,hcut⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff
    (show 0 < t/2 by positivity) (show 0 < 1/K by positivity)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall aRank etaRank seed c2 tau r ha he htId htau hseed0 hseed hTau hc2 hr hr1 hrdelta ell
  have hs := combinedLoss_budget J ht htau hseed0 hseed hTau hc2
  let s := combinedLoss seed c2 tau J
  have hsa : s/aRank ≤ etaRank/2 := by
    apply (div_le_iff₀ ha).mpr
    rw [htId] at hs
    dsimp [s]
    nlinarith [hs.2]
  have hdelta : r^(etaRank/2) ≤ delta^s :=
    (Real.rpow_le_rpow_of_exponent_ge hr hr1 hsa).trans
      (delta_loss_lower hd hr.le ha hs.1 hrdelta)
  have hrsmall : r^(etaRank/2) ≤ 1/K := by
    calc
      _ ≤ (delta^aRank)^(etaRank/2) := Real.rpow_le_rpow hr.le hrdelta (by positivity)
      _ = delta^(t/2) := by
        rw [←Real.rpow_mul hd.le,htId]
        congr 1
        ring
      _ ≤ _ := hcut delta hd hsmall
  have hbase : r^(2*etaRank) ≤
      ((r^etaRank/(4*((g:ℝ)+1)))/menuCost J)*delta^s := by
    calc
      _ = (r^etaRank*r^(etaRank/2))*r^(etaRank/2) := by
        rw [←Real.rpow_add hr,←Real.rpow_add hr]
        congr 1
        ring
      _ ≤ (r^etaRank*r^(etaRank/2))*(1/K) :=
        mul_le_mul_of_nonneg_left hrsmall (by positivity)
      _ ≤ (r^etaRank*delta^s)*(1/K) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdelta (by positivity)) (by positivity)
      _ = _ := by
        dsimp [K]
        field_simp [(menuCost_pos J).ne',show 4*((g:ℝ)+1)≠0 by positivity]
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hr.le _) hbase ell
  rw [←Real.rpow_mul_natCast hr.le] at hp
  have hexp : (2*etaRank)*(ell:ℝ)=2*(ell:ℝ)*etaRank := by ring
  rw [hexp] at hp
  exact hp

/-- Apply the one pre-source cutoff to the actual constructed retained family.
All original pairs, local witnesses and predecessor intersections are retained. -/
theorem exists_uniform_weak_retention (g J : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀n : ℕ,∀D : FiniteScaleSource n,0 < D.thickness → D.thickness ≤ delta0 →
      ∀aRank etaRank seed c2 tau r : ℝ,
        0 < aRank → 0 < etaRank → t=aRank*etaRank →
        0 ≤ tau → 0 ≤ seed → seed ≤ tau/16384 →
        tau ≤ t/(1000*((J:ℝ)+1)) → c2=t/4 →
        0 < r → r ≤ 1 → r ≤ D.thickness^aRank →
      ∀a q : ℝ,∀stop ell : ℕ,∀E2 : Finset (Fin n × Index),∀w : Index → ℕ,
        RetainedFamily D a stop E2 q ell w J
          (retainedFraction D.thickness (r^etaRank/(4*((g:ℝ)+1))) seed c2 tau J ell) →
        RetainedFamily D a stop E2 q ell w J (r^(2*(ell:ℝ)*etaRank)) := by
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_rank_retention_cutoff g J ht
  refine ⟨delta0,hd0,hd01,?_⟩
  intro n D hd hsmall aRank etaRank seed c2 tau r ha he htId htau hseed0 hseed hTau hc2 hr hr1 hrdelta
    a q stop ell E2 w HC
  exact retainedFamily_mono
    (H D.thickness hd hsmall aRank etaRank seed c2 tau r ha he htId htau hseed0 hseed hTau hc2 hr hr1 hrdelta ell) HC

end NativeCompatibleWeightedRetention
