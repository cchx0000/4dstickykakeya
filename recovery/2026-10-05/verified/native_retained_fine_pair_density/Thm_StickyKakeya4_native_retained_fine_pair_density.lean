import Theorems.Thm_StickyKakeya4_native_raw_point_global_profiles
import Theorems.Thm_StickyKakeya4_native_queried_vertex_weights

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeRetainedFinePairDensity
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeRawPointSourceProfiles NativeRawPointGlobalProfiles NativeFullCoarseShadow
open NativeCoarsePointMultiplicity NativeMiddleWindowBalance NativeCoarseDyadicShading
open NativeSameSourceCoarseSelection NativeCoarseDirectionThinning
open NativeCoarseShadingCapacity
open scoped BigOperators ENNReal

/-- Actual full-shadow pair count on the globally fixed original representatives. -/
def finePairCount {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level f : ℕ) : ℕ :=
  (E.image (physicalPair h R a level f)).card

lemma full_mass_eq_pair_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (E : Finset (Fin n × Index)) (hR : ∀z∈E,z.1∈R)
    (level f : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : f ≤ level) :
    (wzTotalShadingVolume (fullSource h R a level f E)).toReal =
      (finePairCount h R E a level f:ℝ)*(32/((2^f:ℕ):ℝ))^4 := by
  have hh := coarse_shading_real h.1.2.1 a (2^f) (block level f) (block_pos level f)
    (representative h R a (2^f)) E (R.image (parentLabel D a (2^f)))
    (fun z hz => mem_image_of_mem _ (hR z hz))
  rw [block_mesh hdy hf] at hh
  rw [full_mass_real]
  exact hh

def pairDensityConstant : ℝ :=
  16*43*(2051:ℝ)^4*(373248*64^3*NativeOriginalPrunedMass.volumeConstant)

lemma pairDensityConstant_pos : 0 < pairDensityConstant := by
  have hh := NativeOriginalPrunedMass.volumeConstant_pos
  dsimp [pairDensityConstant]
  positivity

/-- Cancel the common physical cell volume without discarding the retention
factor or any original-delta power. -/
lemma density_cross {delta eta zeta tau lambda F C v power V I : ℝ}
    (hd : 0 < delta) (hv : 0 < v) (hpower : 0 < power)
    (hlambda : 0 ≤ lambda) (hC : 0 ≤ C)
    (hraw : V ≤ C*delta^(-zeta)/(delta^tau*power*v))
    (hmass : lambda*(delta^(2*eta)/16) ≤ F*43*delta^(-zeta)*(I*v)) :
    lambda*delta^(2*eta+2*zeta+tau)*power*V ≤ 16*43*C*F*I := by
  have hraw' := (le_div_iff₀ (show 0 < delta^tau*power*v by positivity)).mp hraw
  have hm := mul_le_mul_of_nonneg_right hmass
    (show 0 ≤ 16*C*delta^(-zeta) by positivity)
  have hr := mul_le_mul_of_nonneg_left hraw'
    (show 0 ≤ lambda*delta^(2*eta) by positivity)
  have hc : lambda*delta^(2*eta)*delta^tau*power*V*v ≤
      16*43*C*F*I*delta^(-zeta)*delta^(-zeta)*v := by
    nlinarith only [hr,hm]
  have hc' := (mul_le_mul_iff_left₀ hv).mp hc
  have hh := mul_le_mul_of_nonneg_right hc' (Real.rpow_pos_of_pos hd (2*zeta)).le
  have hleft : delta^(2*eta)*delta^tau*delta^(2*zeta)=delta^(2*eta+2*zeta+tau) := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    congr 1
    ring
  have hright : delta^(-zeta)*delta^(-zeta)*delta^(2*zeta)=1 := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    rw [show -zeta+-zeta+2*zeta=(0:ℝ) by ring,Real.rpow_zero]
  calc
    _ = (lambda*delta^(2*eta)*delta^tau*power*V)*delta^(2*zeta) := by rw [←hleft]; ring
    _ ≤ (16*43*C*F*I*delta^(-zeta)*delta^(-zeta))*delta^(2*zeta) := hh
    _ = 16*43*C*F*I*(delta^(-zeta)*delta^(-zeta)*delta^(2*zeta)) := by ring
    _ = _ := by rw [hright,mul_one]

/-- The actual E1 outer-depth-zero conditional lower, original populations,
and literal E2 retention supply a global fine-pair density at any fine depth.
No E1 or E2 off-menu pair uniformity is assumed. -/
theorem source_fine_pair_density {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a tau : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1)
    (L : ℕ) (scales : Fin g → ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (Hcore : IsCore D original R a eta zeta d g L Rel scales E1)
    (f : ℕ) (hf6 : 6 ≤ f) (hf : f ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HC : NativeTwoScaleConfiguration.HasConditionalTwoScale h R E1 a level 0 f tau)
    (G : ℕ) (hG : 0 < G) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card) :
    lambda*D.thickness^(2*eta+2*zeta+tau)*
      (1/((2^f:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent)*
      (rawPointCount D E2 f:ℝ) ≤
        pairDensityConstant*(factor d g L:ℝ)*G*(finePairCount h R E2 a level f:ℝ) := by
  obtain ⟨horiginal,hdy,ha,_hRn,_hcard,_hshade,_hden,_hCW,Hpop⟩ := Hbackbone
  let F1 := factor d g L
  let C : ℝ := (2051:ℝ)^4*(373248*64^3*NativeOriginalPrunedMass.volumeConstant)
  have hd := h.1.2.1
  have hR1 : ∀z∈E1,z.1∈R := fun z hz => (mem_filter.mp (Hcore.1 hz)).2
  have hR2 : ∀z∈E2,z.1∈R := fun z hz => hR1 z (h21 hz)
  have hF1 : 0 < F1 := by
    obtain ⟨z,hz⟩ := Hcore.2.1
    have hi : 0 < (incidences original).card :=
      card_pos.mpr ⟨z,(Hcore.1.trans (filter_subset _ _)) hz⟩
    have hh := Hcore.2.2.1
    change (incidences original).card ≤ F1*E1.card at hh
    by_contra hf0
    rw [Nat.eq_zero_of_not_pos hf0,zero_mul] at hh
    omega
  have hGlobal := global_shadow_bounds_of_conditional (zeta:=zeta) h R E1 Hcore.2.1 hR1 level f
    (by
      intro p hp
      simpa using (Hpop ⟨0,by omega⟩ p hp).1) HC
  have hraw1 := raw_point_upper h original horiginal ha R E1 Hcore.1 Hcore.2.1
    level f hdy hf hf6 (fun p hp => (Hpop ⟨f,Nat.lt_succ_of_le hf⟩ p hp).1)
    _ (by positivity) hGlobal.1
  have hraw2 : (rawPointCount D E2 f:ℝ) ≤ (rawPointCount D E1 f:ℝ) := by
    exact_mod_cast raw_point_count_mono D E1 E2 h21 f
  have hRet := two_stage_incidence_retention original E1 E2 F1 G lambda hlambda Hcore.2.2.1 hret
  have hsource : (wzTotalShadingVolume D).toReal=((incidences original).card:ℝ)*(D.thickness/2)^4 := by
    rw [total_shading_eq_incidence_volume D (half_pos hd) original horiginal]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (half_pos hd).le]
  have hcoarse := selected_dyadic_shading_transfer h original horiginal ha R E2
    (h21.trans Hcore.1) level f hdy hf
    (fun p hp => (Hpop ⟨f,Nat.lt_succ_of_le hf⟩ p hp).2) (representative h R a (2^f))
  rw [←full_mass_real,full_mass_eq_pair_count h R a E2 hR2 level f hdy hf] at hcoarse
  have hmass : lambda*(D.thickness^(2*eta)/16) ≤
      ((F1:ℝ)*G)*43*D.thickness^(-zeta)*
        ((finePairCount h R E2 a level f:ℝ)*(32/((2^f:ℕ):ℝ))^4) := by
    calc
      _ ≤ lambda*(wzTotalShadingVolume D).toReal :=
        mul_le_mul_of_nonneg_left (original_shading_mass_lower h original horiginal hsmall) hlambda
      _ = (lambda*((incidences original).card:ℝ))*(D.thickness/2)^4 := by rw [hsource]; ring
      _ ≤ (((F1:ℝ)*G)*E2.card)*(D.thickness/2)^4 :=
        mul_le_mul_of_nonneg_right hRet (by positivity)
      _ = ((F1:ℝ)*G)*((E2.card:ℝ)*(D.thickness/2)^4) := by ring
      _ ≤ ((F1:ℝ)*G)*(43*D.thickness^(-zeta)*
          ((finePairCount h R E2 a level f:ℝ)*(32/((2^f:ℕ):ℝ))^4)) :=
        mul_le_mul_of_nonneg_left hcoarse (by positivity)
      _ = _ := by ring
  have hC : 0 ≤ C := by
    have hh := NativeOriginalPrunedMass.volumeConstant_pos
    dsimp [C]
    positivity
  have hh := density_cross hd (by positivity : 0 < (32/((2^f:ℕ):ℝ))^4)
    (by positivity : 0 < (1/((2^f:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent))
    hlambda hC (hraw2.trans hraw1) hmass
  convert hh using 1
  dsimp [C,F1,pairDensityConstant]
  ring

end NativeRetainedFinePairDensity
