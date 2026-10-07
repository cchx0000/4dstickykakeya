import Theorems.Thm_StickyKakeya4_native_spatial_parent_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeParentVertexMassCap
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeRawPointSourceProfiles NativeRawPointGlobalProfiles NativeFullCoarseShadow
open NativeMiddleWindowBalance NativeRetainedFinePairDensity NativeSpatialAngularGeometry
open NativeConditionedPairMenu NativeAllTwoScaleConfiguration NativeTwoScaleConfiguration
open NativeFixedCompactKakeyaExponent NativeSpatialParentCount NativeQueriedVertexWeights
open scoped BigOperators

/-- Installed uniformity of the original pair map controls every literal
incidence subset; no uniformity is asserted for that subset. -/
lemma uniform_subset_cross {A B : Type*} [DecidableEq A] [DecidableEq B]
    (E S : Finset A) (hS : S⊆E) (f : A → B) (Q : ℕ)
    (HU : HasUniformFibers E Q f) :
    S.card*(E.image f).card ≤ Q^2*E.card*(S.image f).card := by
  calc
    _ = ∑v∈S.image f,(S.filter (fun z => f z=v)).card*(E.image f).card := by
      rw [←sum_mul,←card_eq_sum_card_image f S]
    _ ≤ ∑_v∈S.image f,Q^2*E.card := by
      apply sum_le_sum
      intro v _hv
      have hs := card_le_card (filter_subset_filter (fun z => f z=v) hS)
      have hh := NativeCoarseUniformImageDegrees.point_fiber_card_cross E
        (fun z => ((),f z)) (Q^2) HU v
      have hh' : (E.filter (fun z => f z=v)).card*(E.image f).card ≤ Q^2*E.card := by
        simpa only [image_image,Function.comp_def] using hh
      exact (Nat.mul_le_mul_right _ hs).trans hh'
    _ = _ := by simp [Nat.mul_comm]

/-- The computed integer cap is at least half its real defining average.
This keeps the precise cap used in the existing global grain count. -/
lemma average_le_twice_cap {T X V : Type*} [DecidableEq T] [DecidableEq X] [DecidableEq V]
    (E : Finset (T × X)) (hE : E.Nonempty) (f : X → V) (Q : ℕ)
    (HU : HasUniformFibers E Q (fun z => f z.2)) :
    (Q:ℝ)^2*E.card ≤ 2*(vertexCap E f Q:ℝ)*(vertices E f).card := by
  have hV : 0 < (vertices E f).card := card_pos.mpr ((hE.image Prod.snd).image f)
  have hM := vertexCap_pos E hE f Q HU
  have hd := Nat.mod_add_div (Q^2*E.card) (vertices E f).card
  have hr := Nat.mod_lt (Q^2*E.card) hV
  have hb : (vertices E f).card ≤ (vertexCap E f Q)*(vertices E f).card := by
    simpa using Nat.mul_le_mul_right (vertices E f).card (Nat.succ_le_of_lt hM)
  have hc : Q^2*E.card ≤ 2*(vertexCap E f Q)*(vertices E f).card := by
    change _+(vertices E f).card*(vertexCap E f Q)=_ at hd
    nlinarith only [hd,hr,hb]
  exact_mod_cast hc

lemma depth_power_factor (c f : ℕ) (kappa : ℝ) :
    (1/((2^f:ℕ):ℝ))^(-kappa) = (1/((2^c:ℕ):ℝ))^(-kappa)*
      ((64/((2^f:ℕ):ℝ))/(64/((2^c:ℕ):ℝ)))^(-kappa) := by
  rw [←Real.mul_rpow (by positivity : (0:ℝ) ≤ 1/((2^c:ℕ):ℝ)) (by positivity)]
  congr 1
  field_simp

def parentCapConstant : ℝ := 2*2401*pairDensityConstant

lemma parentCapConstant_pos : 0 < parentCapConstant := by
  have hh := pairDensityConstant_pos
  dsimp [parentCapConstant]
  positivity

/-- Exact cancellation retains both the parent power and all paid source
losses. The fine power cancels through the original conditional ratio. -/
lemma cap_cross {delta eta zeta tau lambda Pc ratio V I A M S C : ℝ}
    (hd : 0 < delta) (hratio : 0 < ratio) (hV : 0 < V)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hDensity : lambda*delta^(2*eta+2*zeta+tau)*(Pc*ratio)*V ≤ C*I)
    (hLocal : S*I ≤ A*(2401*delta^(-(3*tau))*ratio))
    (hCap : A ≤ 2*M*V) :
    lambda*delta^(2*eta+2*zeta+4*tau)*Pc*S ≤ 2*2401*C*M := by
  have hh : (lambda*delta^(2*eta+2*zeta+tau)*Pc*S)*(V*ratio) ≤
      (2*2401*C*M*delta^(-(3*tau)))*(V*ratio) := by
    calc
      _ = (lambda*delta^(2*eta+2*zeta+tau)*(Pc*ratio)*V)*S := by ring
      _ ≤ (C*I)*S := mul_le_mul_of_nonneg_right hDensity hS
      _ = C*(S*I) := by ring
      _ ≤ C*(A*(2401*delta^(-(3*tau))*ratio)) := mul_le_mul_of_nonneg_left hLocal hC
      _ ≤ C*((2*M*V)*(2401*delta^(-(3*tau))*ratio)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCap (by positivity)) hC
      _ = _ := by ring
  have hcancel := (mul_le_mul_iff_left₀ (mul_pos hV hratio)).mp hh
  have hp := mul_le_mul_of_nonneg_right hcancel (Real.rpow_pos_of_pos hd (3*tau)).le
  have hleft : delta^(2*eta+2*zeta+tau)*delta^(3*tau)=delta^(2*eta+2*zeta+4*tau) := by
    rw [←Real.rpow_add hd]
    congr 1
    ring
  have hright : delta^(-(3*tau))*delta^(3*tau)=1 := by
    rw [←Real.rpow_add hd,neg_add_cancel,Real.rpow_zero]
  calc
    _ = (lambda*delta^(2*eta+2*zeta+tau)*Pc*S)*delta^(3*tau) := by rw [←hleft]; ring
    _ ≤ (2*2401*C*M*delta^(-(3*tau)))*delta^(3*tau) := hp
    _ = (2*2401*C*M)*(delta^(-(3*tau))*delta^(3*tau)) := by ring
    _ = _ := by rw [hright,mul_one]

/-- A genuine parent/raw-fine-cell incidence mass cap, derived from the same
E1 source and E2 pair/raw query fields. Arbitrary later cuts inherit this
upper. The lambda, F1, G and delta losses remain literal in the cross form. -/
theorem source_parent_vertex_cap {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a seed tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 E2 : Finset (Fin n × Index)) (h21 : E2⊆E1) (hE2 : E2.Nonempty) (L : ℕ)
    (schedule : Fin (g+1) → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (htau : 0 < tau) (heta : 0 ≤ eta) (hseed : seed ≤ tau/16384)
    (hg : 0 < g) (hgl : g ≤ level)
    (hgrid : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (hschedule : schedule=fullSchedule tau htau g level)
    (Hcore : IsCore D original R a eta zeta d (g+1) L Rel
      (fun j => 2^(schedule j).val) E1)
    (hcost : (125*175616*16384:ℝ)*(factor d (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (hconditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
      HasUniformFibers E1 (coreRadix original R L)
        (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val))
    (hreference : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau)
    (G : ℕ) (hG : 0 < G) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card)
    (c f Q2 : ℕ) (hcf : c ≤ f) (hf6 : 6 ≤ f) (hf : f ≤ level) (hsmall : D.thickness ≤ 1/8)
    (HP : HasUniformFibers E2 Q2 (physicalPair h R a level f))
    (HV : HasUniformFibers E2 Q2 (fun z => spatialLabel D (2^f) z.2))
    (S : Finset (Fin n × Index)) (hS : S⊆E2) (p : Parent) (v : Index)
    (hparent : ∀z∈S,parentLabel D a (2^c) z.1=p)
    (hspace : ∀z∈S,spatialLabel D (2^f) z.2=v) :
    lambda*D.thickness^(2*eta+2*zeta+4*tau)*(1/((2^c:ℕ):ℝ))^(-extremalExponent)*(S.card:ℝ) ≤
      parentCapConstant*(factor d (g+1) L:ℝ)*G*
        (vertexCap E2 (spatialLabel D (2^f)) Q2:ℝ) := by
  have hHer := NativeReferenceHereditaryUpper.from_master_reference h original R E1 schedule Rel
    htau heta hseed hg hgl hgrid Hbackbone hschedule Hcore hcost hconditioned hreference
  have hSp : parentEdges D a (2^c) S p=S := filter_eq_self.mpr hparent
  have hu := hHer S (hS.trans h21) c f hcf hf p
  rw [hSp] at hu
  have hPair := fine_pair_count_in_raw_cell h original R Hbackbone S
    ((hS.trans h21).trans Hcore.1) f hf v hspace _ (by have hd := h.1.2.1; positivity) hu
  have hlocal := uniform_subset_cross E2 S hS (physicalPair h R a level f) Q2 HP
  have hlocalR : (S.card:ℝ)*(finePairCount h R E2 a level f:ℝ) ≤
      (Q2:ℝ)^2*E2.card*(finePairCount h R S a level f:ℝ) := by exact_mod_cast hlocal
  have hlocal' := hlocalR.trans (mul_le_mul_of_nonneg_left hPair (by positivity))
  have hdensity := source_fine_pair_density h original R E1 E2 h21 L
    (fun j => 2^(schedule j).val) Rel Hbackbone Hcore f hf6 hf hsmall
    (hreference 0 f (Nat.zero_le _) hf) G hG lambda hlambda hret
  rw [depth_power_factor c f extremalExponent] at hdensity
  have hcap := average_le_twice_cap E2 hE2 (spatialLabel D (2^f)) Q2 HV
  have hVeq : vertices E2 (spatialLabel D (2^f))=E2.image (fun z => spatialLabel D (2^f) z.2) := by
    simp only [vertices,image_image,Function.comp_def]
  have hV : (0:ℝ) < rawPointCount D E2 f := by
    exact_mod_cast card_pos.mpr (hE2.image (fun z => spatialLabel D (2^f) z.2))
  rw [hVeq] at hcap
  have hC : 0 ≤ pairDensityConstant*(factor d (g+1) L:ℝ)*G := by
    have hh := pairDensityConstant_pos
    positivity
  have hh := cap_cross h.1.2.1 (by positivity : 0 <
      ((64/((2^f:ℕ):ℝ))/(64/((2^c:ℕ):ℝ)))^(-extremalExponent)) hV
    (Nat.cast_nonneg S.card) hC hdensity (by simpa only [mul_assoc] using hlocal') hcap
  convert hh using 1
  dsimp [parentCapConstant]
  ring

end NativeParentVertexMassCap
