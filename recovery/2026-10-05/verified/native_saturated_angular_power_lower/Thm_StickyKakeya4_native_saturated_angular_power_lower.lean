import Theorems.Thm_StickyKakeya4_native_saturated_ancestor_angular_lower
import Theorems.Thm_StickyKakeya4_native_reference_original_parent_profiles

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

noncomputable section
namespace NativeSaturatedAngularPowerLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeOriginalCellChartGeometry
open NativeOriginalPointSaturation NativeOriginalPointAngularLower NativeSaturatedAncestorAngularLower
open NativeIncidenceMultiplicityTower NativeLocalMenuInterpolation NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeCoarseFineMultiplicity

lemma local_scale_ratio (delta : ℝ) (c g : ℕ) (hcg : c≤ g) :
    localScale delta g=((2^(g-c):ℕ):ℝ)*localScale delta c := by
  have hp : ((2^g:ℕ):ℝ)=((2^(g-c):ℕ):ℝ)*((2^c:ℕ):ℝ) := by
    rw [←Nat.cast_mul,←pow_add,Nat.sub_add_cancel hcg]
  dsimp [localScale]
  rw [hp]
  ring

/-- The scheduled predecessor gap costs exactly an original-delta power.
This power is retained explicitly until the later stopping-scale budget. -/
theorem ancestor_parent_power_upper {delta kappa tau gap : ℝ}
    (hd : 0< delta) (hd1 : delta≤ 1) (hk : 0≤ kappa) (hk3 : kappa≤ 3) (hgap0 : 0≤ gap)
    (level c g : ℕ) (hdy : delta=(2:ℝ)⁻¹^level) (hcg : c≤ g)
    (hgap : ((g-c:ℕ):ℝ)≤ gap*level) :
    delta^(-tau)*(localScale delta c)^(-kappa)≤ 
      delta^(-(tau+3*gap))*(localScale delta g)^(-kappa) := by
  let ratio : ℝ := ((2^(g-c):ℕ):ℝ)
  have hratio : 0< ratio := by dsimp [ratio]; positivity
  have hR := dyadic_gap_power hdy hgap
  have hPower : ratio^kappa≤ delta^(-(3*gap)) := by
    have hh := Real.rpow_le_rpow hratio.le hR hk
    rw [←Real.rpow_mul hd.le] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by nlinarith only [hk3,hgap0]))
  have heps := localScale_pos hd c
  have hscale : localScale delta g=ratio*localScale delta c := local_scale_ratio delta c g hcg
  have hid : (localScale delta c)^(-kappa)=ratio^kappa*(localScale delta g)^(-kappa) := by
    rw [hscale,Real.mul_rpow hratio.le heps.le,←mul_assoc,←Real.rpow_add hratio]
    simp
  rw [hid]
  calc
    _ ≤  delta^(-tau)*(delta^(-(3*gap))*(localScale delta g)^(-kappa)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPower
        (Real.rpow_nonneg (localScale_pos hd g).le _)) (Real.rpow_nonneg hd.le _)
    _ = _ := by rw [←mul_assoc,←Real.rpow_add hd]; congr 1; ring

lemma actual_angular_scale_ratio (delta : ℝ) (m s : ℕ) (hs : 3≤ s) :
    localScale delta m=((64/((2^s:ℕ):ℝ))/8)*localScale delta (m+s-3) := by
  have hm : m≤ m+s-3 := by omega
  have hp : ((2^s:ℕ):ℝ)=8*((2^((m+s-3)-m):ℕ):ℝ) := by
    have he : s=3+((m+s-3)-m) := by omega
    calc
      _ = ((2^(3+((m+s-3)-m)):ℕ):ℝ) := by rw [←he]
      _ = _ := by rw [pow_add]; norm_num
  rw [local_scale_ratio delta m (m+s-3) hm,hp]
  have hnonzero : ((2^((m+s-3)-m):ℕ):ℝ)≠0 := by positivity
  field_simp
  ring

/-- Cancel the actual complementary local scales only after retaining the
entire original-delta loss. -/
theorem cancel_parent_powers {delta epsBase epsFine rho kappa tau gap gamma C : ℝ}
    (hd : 0< delta) (hb : 0< epsBase) (hf : 0< epsFine) (hr : 0< rho)
    (hk : 0≤ kappa) (hg : 0≤ gamma)
    (hscale : epsBase=(rho/8)*epsFine)
    (H : gamma*(delta^tau*epsBase^(-kappa))≤ C*(delta^(-(tau+3*gap))*epsFine^(-kappa))) :
    gamma*delta^(2*tau+3*gap)*rho^(-kappa)≤ C := by
  have hp : rho^(-kappa)*epsFine^(-kappa)≤ epsBase^(-kappa) := by
    rw [←Real.mul_rpow hr.le hf.le]
    apply Real.rpow_le_rpow_of_nonpos hb _ (neg_nonpos.mpr hk)
    rw [hscale]
    nlinarith only [hr,hf]
  have hpower : delta^(2*tau+3*gap)*delta^(-(tau+3*gap))=delta^tau := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hB : 0< delta^(-(tau+3*gap))*epsFine^(-kappa) := by positivity
  apply (mul_le_mul_iff_right₀ hB).mp
  calc
    _ = gamma*delta^tau*(rho^(-kappa)*epsFine^(-kappa)) := by
      calc
        _ = gamma*(delta^(2*tau+3*gap)*delta^(-(tau+3*gap)))*(rho^(-kappa)*epsFine^(-kappa)) := by ring
        _ = _ := by rw [hpower]
    _ ≤  gamma*(delta^tau*epsBase^(-kappa)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (mul_nonneg hg (Real.rpow_nonneg hd.le tau))
    _ ≤  _ := by simpa only [mul_comm] using H

/-- Actual original-parent profiles and literal parent-edge retention
produce the rho^{-kappa} point angular lower. No mean-ratio or angular-AD
certificate is an input. c is an installed scheduled ancestor of m+s-3. -/
theorem saturated_reference_power_lower {n : ℕ} {D : FiniteScaleSource n} {eta a tau gap gamma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E1 E2 S : Finset (Fin n × Index)) (h21 : E2⊆ E1) (hE1 : E1⊆ incidences original)
    (level m s c : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤ level)
    (hs : 3≤ s) (hf : m+s-3≤ level) (hcf : c≤ m+s-3)
    (hgap0 : 0≤ gap) (hgap : (((m+s-3)-c:ℕ):ℝ)≤ gap*level)
    (p : Parent) (HS : Saturated (parentEdges D a (2^m) E2 p) S Prod.snd)
    (hgamma : 0≤ gamma)
    (hret : gamma*(parentEdges D a (2^m) E1 p).card≤ (parentEdges D a (2^m) E2 p).card)
    (Q1 Q2 : ℕ) (HRef : HasUniformFibers E1 Q1 (formalPair D a c))
    (HPoint : HasUniformFibers (parentEdges D a (2^m) E2 p) Q2 Prod.snd)
    (HProfiles : ∀d : ℕ,d≤ level → ∀t : Parent,(parentEdges D a (2^d) E1 t).Nonempty →
      D.thickness^tau*(localScale D.thickness d)^(-extremalExponent)≤ multiplicity (parentEdges D a (2^d) E1 t) ∧
      multiplicity (parentEdges D a (2^d) E1 t)≤ D.thickness^(-tau)*(localScale D.thickness d)^(-extremalExponent))
    (k : Index) (hk : k∈S.image Prod.snd) :
    gamma*D.thickness^(2*tau+3*gap)*(64/((2^s:ℕ):ℝ))^(-extremalExponent)≤ 
      343*(Q1:ℝ)^2*(Q2:ℝ)^2*(pointMenu D m s p S k).card := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hP21 : parentEdges D a (2^m) E2 p⊆ parentEdges D a (2^m) E1 p := filter_subset_filter _ h21
  have hSn : S.Nonempty := image_nonempty.mp ⟨k,hk⟩
  have hp1 : (parentEdges D a (2^m) E1 p).Nonempty := hSn.mono (HS.1.trans hP21)
  have hLower := mul_le_mul_of_nonneg_left (HProfiles m hm p hp1).1 hgamma
  have hRet := retained_incidence_multiplicity _ _ hP21 hgamma hret
  have hLower' := hLower.trans hRet
  have hS1 : S⊆ E1 := HS.1.trans ((filter_subset _ _).trans h21)
  have hscale : ((2^(m+s-3):ℕ):ℝ)*D.thickness≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hf]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  let U := D.thickness^(-tau)*(localScale D.thickness c)^(-extremalExponent)
  have hU : 0≤ U := mul_nonneg (Real.rpow_nonneg hd.le _)
    (Real.rpow_nonneg (localScale_pos hd c).le _)
  have hMenu := saturated_ancestor_point_lower h original horiginal ha E1 _ S HS hS1 (hS1.trans hE1)
    m s c hs hcf hscale p Q1 Q2 HRef HPoint U hU
    (fun t ht => (HProfiles c (hcf.trans hf) t ht).2) k hk
  have hUUpper := ancestor_parent_power_upper (tau:=tau) hd hd1 extremalExponent_nonneg extremalExponent_le_three
    hgap0 level c (m+s-3) hdy hcf hgap
  have hCombined : gamma*(D.thickness^tau*(localScale D.thickness m)^(-extremalExponent))≤ 
      (343*(Q1:ℝ)^2*(Q2:ℝ)^2*(pointMenu D m s p S k).card)*
        (D.thickness^(-(tau+3*gap))*(localScale D.thickness (m+s-3))^(-extremalExponent)) := by
    apply (hLower'.trans hMenu).trans
    have hh := mul_le_mul_of_nonneg_left hUUpper
      (show 0≤ 343*(Q1:ℝ)^2*(Q2:ℝ)^2*(pointMenu D m s p S k).card by positivity)
    simpa only [mul_assoc,mul_comm,mul_left_comm,U] using hh
  exact cancel_parent_powers hd (localScale_pos hd m) (localScale_pos hd (m+s-3)) (by positivity)
    extremalExponent_nonneg hgamma (actual_angular_scale_ratio D.thickness m s hs) hCombined

end NativeSaturatedAngularPowerLower
