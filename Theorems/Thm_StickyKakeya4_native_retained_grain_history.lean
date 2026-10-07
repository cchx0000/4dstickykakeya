import Theorems.Thm_StickyKakeya4_native_actual_grain_history
import Theorems.Thm_StickyKakeya4_native_compatible_weighted_retention

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeRetainedGrainHistory
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning NativeOriginalParentDensityCore
open NativeLocalPairFibers NativeSquaredGrainQueries NativeQueriedVertexWeights
open NativeJointUniformCoarseRelations NativeDirectionRankDichotomy NativeCompatibleAngularCandidates
open WeightedRichDirectionalLayers NativeCompatibleNodeDirections NativeActualGrainHistory
open NativeCompatibleWeightedRetention NativeRetainedQueryMenu

/-- One cutoff depending only on the fixed grain count and common rank budget.
It is chosen before D, the actual rank, and the stopping radius. -/
def historyCutoff (J : ℕ) (t : ℝ) (ht : 0 < t) : ℝ :=
  (NativeQuarterScaleParameters.exists_small_power_cutoff ht
    (show 0 < 1/((2^J:ℕ):ℝ) by positivity)).choose

theorem historyCutoff_spec (J : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < historyCutoff J t ht ∧ historyCutoff J t ht ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ historyCutoff J t ht → delta^t ≤ 1/((2^J:ℕ):ℝ) :=
  (NativeQuarterScaleParameters.exists_small_power_cutoff ht
    (show 0 < 1/((2^J:ℕ):ℝ) by positivity)).choose_spec

theorem rank_halving_cost (J : ℕ) (t : ℝ) (ht : 0 < t)
    {delta aRank etaRank r : ℝ} (hd : 0 < delta) (hsmall : delta ≤ historyCutoff J t ht)
    (heta : 0 ≤ etaRank) (hid : aRank*etaRank=t) (hr : 0 < r) (hscale : r ≤ delta^aRank) :
    ((2^J:ℕ):ℝ)*r^etaRank ≤ 1 := by
  have hp : r^etaRank ≤ delta^t := by
    calc
      _ ≤ (delta^aRank)^etaRank := Real.rpow_le_rpow hr.le hscale heta
      _ = _ := by rw [←Real.rpow_mul hd.le,hid]
  have hh := hp.trans ((historyCutoff_spec J t ht).2.2 delta hd hsmall)
  have hC : (0:ℝ) < ((2^J:ℕ):ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left hh hC.le
  simpa only [mul_one_div_cancel hC.ne'] using hm

/-- The history's fixed 2^J loss is absorbed ONCE, by one additional rank
power. This lemma does not multiply a source-delta loss at successive levels. -/
theorem retained_power_after_halving (J ell : ℕ) {r etaRank M0 M1 M2 : ℝ}
    (hr : 0 < r) (hM2 : 0 ≤ M2)
    (hret : r^(2*(ell:ℝ)*etaRank)*M0 ≤ M1)
    (hhalf : M1 ≤ ((2^J:ℕ):ℝ)*M2) (hcost : ((2^J:ℕ):ℝ)*r^etaRank ≤ 1) :
    r^((2*(ell:ℝ)+1)*etaRank)*M0 ≤ M2 := by
  calc
    _ = r^etaRank*(r^(2*(ell:ℝ)*etaRank)*M0) := by
      rw [←mul_assoc,←Real.rpow_add hr]
      congr 2
      ring
    _ ≤ r^etaRank*M1 := mul_le_mul_of_nonneg_left hret (Real.rpow_pos_of_pos hr _).le
    _ ≤ r^etaRank*(((2^J:ℕ):ℝ)*M2) :=
      mul_le_mul_of_nonneg_left hhalf (Real.rpow_pos_of_pos hr _).le
    _ = (((2^J:ℕ):ℝ)*r^etaRank)*M2 := by ring
    _ ≤ 1*M2 := mul_le_mul_of_nonneg_right hcost hM2
    _ = M2 := one_mul _

/-- Exactly J successor grain depths; the root is not counted as an extra cut. -/
def historyDepth (J stop : ℕ) (i : Fin J) : ℕ := grainDepth J stop i.succ

lemma historyDepth_eq_depth (J stop : ℕ) (i : Fin J) :
    historyDepth J stop i=depth J stop (i.val+1) := by
  unfold historyDepth depth
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ,min_eq_left (Nat.succ_le_of_lt i.isLt)]

lemma historyDepth_le_stop (J stop : ℕ) (i : Fin J) : historyDepth J stop i ≤ stop :=
  (grainDepth_bounds J stop i.succ).2

/-- The original retained-family fields and the actual history share ONE P,
ONE initial S, and the unchanged E2 point weights. The final fraction has only
one extra rank-loss power after the complete finite history. -/
def HasRetainedHistory {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (stop : ℕ)
    (E : Finset (Fin n × Index)) (q : ℝ) (ell J Q2 : ℕ)
    (r etaRank lambda c1 c2 : ℝ) : Prop :=
  let w := pointWeight E
  ∃P⊆terminalFamily D a stop E q ell, ∃S⊆E.image Prod.snd,
    S=P.image Prod.fst ∧
    (∀x y,x∈P → y∈P → x.1=y.1 → x=y) ∧
    SelfUniform.mass (fun p => w p.1) P=SelfUniform.mass w S ∧
    r^(2*(ell:ℝ)*etaRank)*(SelfUniform.mass w (E.image Prod.snd):ℝ) ≤ (SelfUniform.mass w S:ℝ) ∧
    (∀j,j<J+1 → ∀x y,x∈P → y∈P →
      spatialLabel D (2^(depth J stop j)) x.1=spatialLabel D (2^(depth J stop j)) y.1 →
      projectWord stop (depth J stop j) x.2=projectWord stop (depth J stop j) y.2) ∧
    (∀p∈P,LocalWitness D a stop E q ell p) ∧
    (∀j,j<J → ∀v∈P.image (node D J stop (j+1)),
      ancestorNode (depth J stop (j+1)) (depth J stop j) v∈P.image (node D J stop j) ∧
      (candidate D J stop (j+1) P v ∩ candidate D J stop j P
        (ancestorNode (depth J stop (j+1)) (depth J stop j) v)).Nonempty) ∧
    ∃ (point : Fin J → Index → Index)
      (tuple : Fin J → Index → Fin ell → (Fin n × Index))
      (anchor : Fin J → Index → Fin ell → Fin n),
      (∀i,IsNodeDirectionSystem D a (historyDepth J stop i) E S q ell
        (point i) (tuple i) (anchor i)) ∧
      HasGrainHistory D E (historyDepth J stop) ell (fun i => natStageDirectionIndex h (tuple i))
        S Q2 lambda c1 c2 ∧
      r^((2*(ell:ℝ)+1)*etaRank)*(E.card:ℝ) ≤
        (mass (history D E (historyDepth J stop) ell
          (fun i => natStageDirectionIndex h (tuple i)) S J) w:ℝ)

/-- Actual retained-family to history assembly. The cutoff depends only on J
and the common rank budget t and precedes the source. The prescribed retained
family is unpacked once; its original P, S, compatibility and trace survive. -/
theorem construct_actual_retained_history (J : ℕ) (t : ℝ) (ht : 0 < t)
    {n level : ℕ} {D : FiniteScaleSource n} {eta eta2 a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (hsmall : D.thickness ≤ historyCutoff J t ht)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hEne : E.Nonempty) (hER : ∀z∈E,z.1∈R)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (stop : ℕ) (hm6 : ∀i : Fin J,6 ≤ historyDepth J stop i)
    (hpL : ∀i : Fin J,phaseDepth (historyDepth J stop i) ≤ level)
    (hscale : ∀i : Fin J,D.thickness ≤ (64/((2^(historyDepth J stop i):ℕ):ℝ))^2)
    (HF : ∀i : Fin J,HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth (historyDepth J stop i)) (phaseDepth (historyDepth J stop i))
        (representative h R a (2^(phaseDepth (historyDepth J stop i))))))
    (HC : ∀i : Fin J,HasUniformFibers E Q2
      (fixedPair D a level (phaseDepth (historyDepth J stop i)) (historyDepth J stop i)
        (representative h R a (2^(phaseDepth (historyDepth J stop i))))))
    (HV : ∀i : Fin J,HasUniformFibers E Q2
      (fun z => spatialLabel D (2^(phaseDepth (historyDepth J stop i))) z.2))
    (q : ℝ) (hq : 0 < q) (ell : ℕ) (hell : 0 < ell)
    (aRank etaRank r : ℝ) (hetaRank : 0 ≤ etaRank) (hid : aRank*etaRank=t)
    (hr : 0 < r) (hrscale : r ≤ D.thickness^aRank)
    (Hfamily : RetainedFamily D a stop E q ell (pointWeight E) J (r^(2*(ell:ℝ)*etaRank))) :
    HasRetainedHistory h a stop E q ell J Q2 r etaRank lambda c1 c2 := by
  obtain ⟨P,hP,S,hSE,hS,hinj,hmass,hret,hcompat,hwitness,htrace⟩ := Hfamily
  subst S
  have hretOriginal := hret
  change r^(2*(ell:ℝ)*etaRank)*(mass (E.image Prod.snd) (pointWeight E):ℝ) ≤
    (mass (P.image Prod.fst) (pointWeight E):ℝ) at hret
  rw [NativeQueriedVertexWeights.reference_mass] at hret
  have hCardE : (0:ℝ) < E.card := by exact_mod_cast card_pos.mpr hEne
  have hpositive : 0 < r^(2*(ell:ℝ)*etaRank)*(E.card:ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hr _) hCardE
  have hPne : P.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty.mp hne] at hret
    simp only [image_empty,WeightedRichDirectionalLayers.mass,sum_empty,Nat.cast_zero] at hret
    exact (not_le_of_gt hpositive) hret
  have hcompat' : ∀i : Fin J,∀x y,x∈P → y∈P →
      spatialLabel D (2^(historyDepth J stop i)) x.1=spatialLabel D (2^(historyDepth J stop i)) y.1 →
      projectWord stop (historyDepth J stop i) x.2=projectWord stop (historyDepth J stop i) y.2 := by
    intro i
    simpa only [historyDepth_eq_depth J stop i] using
      hcompat (i.val+1) (by omega : i.val+1<J+1)
  obtain ⟨point,tuple,anchor,hnode,hhistory⟩ := construct_actual_grain_history h original horiginal ha
    R E hE hER F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta2 hdy hlambda hRich hcost1 hcost2
    stop (historyDepth J stop) (historyDepth_le_stop J stop) hm6 hpL hscale HF HC HV
    q hq ell hell P hP hPne hcompat'
  refine ⟨P,hP,P.image Prod.fst,hSE,rfl,hinj,hmass,hretOriginal,hcompat,hwitness,htrace,
    point,tuple,anchor,hnode,hhistory,?_⟩
  have hhalf : (mass (P.image Prod.fst) (pointWeight E):ℝ) ≤ ((2^J:ℕ):ℝ)*
      (mass (history D E (historyDepth J stop) ell (fun i => natStageDirectionIndex h (tuple i))
        (P.image Prod.fst) J) (pointWeight E):ℝ) := by
    exact_mod_cast hhistory.2.2.2.1
  exact retained_power_after_halving J ell hr (Nat.cast_nonneg _) hret hhalf
    (rank_halving_cost J t ht h.1.2.1 hsmall hetaRank hid hr hrscale)

end NativeRetainedGrainHistory
