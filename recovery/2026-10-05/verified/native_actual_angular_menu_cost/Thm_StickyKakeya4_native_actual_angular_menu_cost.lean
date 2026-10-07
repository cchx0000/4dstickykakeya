import Theorems.Thm_StickyKakeya4_native_actual_angular_menu_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section

namespace NativeActualAngularMenuCost
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeCubicalIncidenceCounts NativeJointUniformCoarseRelations NativeIncidentRankSelection
open NativeDirectionRankDichotomy NativeOriginalCoarseTupleMenu NativeOriginalAngularTupleMenu
open NativeIncidenceMultiplicityTower NativeCoarseFineMultiplicity NativeMiddleWindowBalance
open NativeTwoStageTransversalityBudget NativeActualAngularMenuLower SelfUniform
open NativeOriginalParentDensityCore NativeLocalPairUniformCore NativeLocalMenuInterpolation
open scoped BigOperators

/-- The literal global incidence retention pays exactly one lambda factor in
the surviving mean. This is valid for the unchanged E1/E2 support inclusion. -/
lemma retained_mean_lower {T X : Type*} [DecidableEq X]
    (E1 E2 : Finset (T × X)) (h21 : E2⊆E1) (lambda G : ℝ)
    (hlambda : 0 ≤ lambda) (hG : 0 < G)
    (hret : lambda*(E1.card:ℝ) ≤ G*E2.card) :
    (lambda/G)*NativeIncidenceMultiplicityTower.multiplicity E1 ≤ NativeIncidenceMultiplicityTower.multiplicity E2 := by
  apply retained_incidence_multiplicity E1 E2 h21 (div_nonneg hlambda hG.le)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hG).mpr
  simpa only [mul_comm] using hret

/-- The actual first cost is seed/8 and the actual second cost is c2.
Their radix losses, true E1 near bound and true global E2 retention derive
the linear angular-menu base. Lambda stays explicit, before the rank power. -/
theorem actual_cost_ratio_lower {T X : Type*} [DecidableEq X]
    (E1 E2 : Finset (T × X)) (h21 : E2⊆E1)
    (delta eta seed c2 kappa rho lambda : ℝ)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (hrho : 0 < rho) (hlambda : 0 < lambda)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G)
    (hQ1 : 0 < Q1) (hQ2 : 0 < Q2) (hGF : G ≤ F2)
    (hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (hnear : delta^(-kappa+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity E1)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2)) :
    (lambda/686)*delta^(11*seed/8+c2)*rho^(-kappa) ≤
      NativeIncidenceMultiplicityTower.multiplicity E2/(686*(Q1:ℝ)^2*(Q2:ℝ)^2*(delta^(-seed)*(delta/rho)^(-kappa))) := by
  have hGR : (0:ℝ) < G := by exact_mod_cast hG
  have hQ1R : (0:ℝ) < Q1 := by exact_mod_cast hQ1
  have hQ2R : (0:ℝ) < Q2 := by exact_mod_cast hQ2
  have hmean := retained_mean_lower E1 E2 h21 lambda G hlambda.le hGR hret
  have hnear2 : (lambda/G)*delta^(-kappa+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity E2 :=
    (mul_le_mul_of_nonneg_left hnear (div_nonneg hlambda.le hGR.le)).trans hmean
  have hnearProd : lambda*delta^(-kappa+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity E2*(G:ℝ) := by
    apply (div_le_iff₀ hGR).mp
    simpa only [div_mul_eq_mul_div] using hnear2
  have hQ1cost := radix_sq_le_of_transfer_cost hd hd1 heta F1 Q1 hF1 hcost1
  have hGQ2cost := retention_radix_le_of_transfer_cost hd hd1 heta F2 Q2 (G:ℝ)
    (by exact_mod_cast hGF) hcost2
  have hcost : (G:ℝ)*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ delta^(-(seed/8+c2)) := by
    calc
      _ = (Q1:ℝ)^2*((G:ℝ)*(Q2:ℝ)^2) := by ring
      _ ≤ delta^(-(seed/8))*delta^(-c2) :=
        mul_le_mul hQ1cost hGQ2cost (by positivity) (by positivity)
      _ = _ := by rw [←Real.rpow_add hd]; congr 1; ring
  let U := delta^(-seed)*(delta/rho)^(-kappa)
  have hU : 0 < U := by dsimp [U]; positivity
  have hcancel : rho^(-kappa)*U=delta^(-seed-kappa) := by
    have hp : rho^(-kappa) ≠ 0 := (Real.rpow_pos_of_pos hrho _).ne'
    dsimp [U]
    rw [Real.div_rpow hd.le hrho.le]
    calc
      _ = delta^(-seed)*delta^(-kappa) := by field_simp [hp]
      _ = _ := by
        simpa only [sub_eq_add_neg] using (Real.rpow_add hd (-seed) (-kappa)).symm
  have hden : 0 < 686*(Q1:ℝ)^2*(Q2:ℝ)^2*U := by positivity
  apply (le_div_iff₀ hden).mpr
  apply (mul_le_mul_iff_right₀ hGR).mp
  calc
    _ = lambda*delta^(11*seed/8+c2)*rho^(-kappa)*U*
        ((G:ℝ)*(Q1:ℝ)^2*(Q2:ℝ)^2) := by ring
    _ ≤ lambda*delta^(11*seed/8+c2)*rho^(-kappa)*U*delta^(-(seed/8+c2)) :=
      mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = lambda*(delta^(11*seed/8+c2)*(rho^(-kappa)*U)*delta^(-(seed/8+c2))) := by ring
    _ = lambda*delta^(-kappa+seed/4) := by
      rw [hcancel,←Real.rpow_add hd,←Real.rpow_add hd]
      congr 2
      ring
    _ ≤ _ := hnearProd
    _ = (G:ℝ)*NativeIncidenceMultiplicityTower.multiplicity E2 := by ring

/-- The actual parent scale is delta/rho with rho=64/2^m. -/
lemma parent_scale_identity (delta : ℝ) (m : ℕ) :
    ((2^m:ℕ):ℝ)*delta/64=delta/((64:ℝ)/((2^m:ℕ):ℝ)) := by
  field_simp

lemma original_factor_pos (d g L : ℕ) : 0 < factor d g L := by
  by_cases hsum : 0 < (d+g)+g
  · unfold factor retentionCost
    positivity
  · have hd : d=0 := by omega
    have hg : g=0 := by omega
    subst d
    subst g
    simp [factor,retentionCost]

/-- Source-facing numerator readback at the actual stopping depth. All factors
and radices are the computed source/refinement quantities; positivity and the
second retained-factor comparison are proved here. The only rank retention is
the literal r^rankLoss/(4(g+1)), and no independent small-f parameter is supplied. -/
theorem stopping_weighted_numerator {n d1 d2 g : ℕ} {D : FiniteScaleSource n}
    {eta a seed c2 kappa : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (heta : 0 ≤ eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E1 F E2 : Finset (Fin n × Index))
    (h21 : E2⊆E1) (hE2 : E2⊆incidences original) (L1 L2 m : ℕ)
    (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (r rankLoss : ℝ) (hr : 0 < r)
    (hret : (r^rankLoss/(4*((g:ℝ)+1)))*(E1.card:ℝ) ≤
      (retentionCost d2 1 L2:ℝ)*E2.card)
    (hnear : D.thickness^(-kappa+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity E1)
    (hcost1 : (125*175616*16384:ℝ)*(factor d1 (g+1) L1:ℝ)*
      (coreRadix original R L1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hcost2 : (125*175616*16384:ℝ)*(factor d2 1 L2:ℝ)*
      (NativeSourceSizeBounds.radix F.card L2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2))
    (hOld : ∀x y,x∈E1 → y∈E1 →
      degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^m)) E1 x ≤
      (coreRadix original R L1)^2*
        degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^m)) E1 y)
    (Hpoint : HasUniformFibers E2 (NativeSourceSizeBounds.radix F.card L2) Prod.snd)
    (hupper : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E1 p) ≤
        D.thickness^(-seed)*((((2^m:ℕ):ℝ)*D.thickness/64)^(-kappa)))
    (q : ℝ) (ell : ℕ)
    (Hchains : ∀k∈E2.image Prod.snd,
      (((pointSet E2 k).card:ℝ)/2)^ell ≤
        ((chains (pointSet E2 k) (fun z => slopeVector D z.1) q ell).card:ℝ))
    (w : Index → ℕ) :
    (((r^rankLoss/(4*((g:ℝ)+1)))/686)*D.thickness^(11*seed/8+c2)*
      ((64:ℝ)/((2^m:ℕ):ℝ))^(-kappa))^ell*(SelfUniform.mass w (E2.image Prod.snd):ℝ) ≤
      ((∑k∈E2.image Prod.snd,w k*(angularMenu D a m E2 k q ell).card:ℕ):ℝ) := by
  have hd : 0 < D.thickness := h.1.2.1
  let lambda := r^rankLoss/(4*((g:ℝ)+1))
  let rho := (64:ℝ)/((2^m:ℕ):ℝ)
  let U := D.thickness^(-seed)*(D.thickness/rho)^(-kappa)
  let F1 := factor d1 (g+1) L1
  let F2 := factor d2 1 L2
  let G := retentionCost d2 1 L2
  let Q1 := coreRadix original R L1
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hF1 : 0 < F1 := original_factor_pos _ _ _
  have hG : 0 < G := by dsimp [G,retentionCost]; positivity
  have hQ1 : 0 < Q1 := lt_of_lt_of_le (by norm_num : 0 < (4:ℕ))
    (NativeSourceSizeBounds.radix_four_le (retained original R).card L1)
  have hQ2 : 0 < Q2 := lt_of_lt_of_le (by norm_num : 0 < (4:ℕ))
    (NativeSourceSizeBounds.radix_four_le F.card L2)
  have hGF : G ≤ F2 := NativeSecondRefinementCost.retained_cost_le_factor d2 1 L2 (by omega)
  have Href : HasUniformFibers E1 Q1 (formalPair D a m) := by
    intro x hx y hy
    have hh := hOld x y hx hy
    change degree (fun _ : Fin n × Index => 1)
      (fun x y => formalPair D a m x=formalPair D a m y) E1 x ≤
      Q1^2*degree (fun _ : Fin n × Index => 1)
        (fun x y => formalPair D a m x=formalPair D a m y) E1 y at hh
    simpa only [unit_degree_eq_fiber] using hh
  have Hupper : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E1 p) ≤ U := by
    intro p hp
    simpa only [U,rho,parent_scale_identity] using hupper p hp
  have hratio := actual_cost_ratio_lower E1 E2 h21 D.thickness eta seed c2 kappa rho lambda
    h.1.2.1 h.1.2.2.1 heta hrho hlambda F1 F2 G Q1 Q2 hF1 hG hQ1 hQ2 hGF
    hret hnear hcost1 hcost2
  have hweighted := weighted_angular_numerator_lower h original horiginal ha E1 E2 h21 hE2
    m Q1 Q2 hQ1 hQ2 hscale Href Hpoint U hU Hupper q ell Hchains w
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hratio ell)
    (Nat.cast_nonneg (α := ℝ) (SelfUniform.mass w (E2.image Prod.snd)))).trans hweighted

end NativeActualAngularMenuCost
