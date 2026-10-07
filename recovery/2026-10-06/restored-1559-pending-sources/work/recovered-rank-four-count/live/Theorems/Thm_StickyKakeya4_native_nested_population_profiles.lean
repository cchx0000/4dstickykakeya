import Theorems.Thm_StickyKakeya4_native_nested_population_selection
import Theorems.Thm_StickyKakeya4_native_phase_height_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

noncomputable section
namespace NativeNestedPopulationProfiles
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalParentDensityCore
open NativeMiddleWindowBalance NativeCoarseAncestorCounts NativeDyadicParentCells
open NativeActivePhasePopulation NativePhaseHeightPopulation NativeNestedPopulationSelection
open scoped BigOperators

/-- Phase resolution and translated height mesh are independent. In particular,
the finer witness parent does not replace the outer slice height. -/
theorem phase_height_population_at_height {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (heightDepth c f : ℕ) (hhlevel : heightDepth ≤ level) (hmf : c ≤ f) (hfl : f ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (hEn : E.Nonempty)
    (p : Parent) (hp : ∀z∈E,parentLabel D a (2^c) z.1=p)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hret : mu*(R.filter (fun i => parentLabel D a (2^c) i=p)).card ≤ D.thickness*E.card) :
    mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^c:ℕ):ℝ))^3 ≤
      (43904*(64/((2^heightDepth:ℕ):ℝ)))*(phaseHeightLabels D a (64/((2^heightDepth:ℕ):ℝ)) f E).card := by
  obtain ⟨horiginal,hdy,ha,_hRn,_hnR,_hshade,_hdensity,_hcw,Hpop⟩ := Hbackbone
  have hd := h.1.2.1
  let rho : ℝ := 64/((2^heightDepth:ℕ):ℝ)
  let V (d : ℕ) : ℝ := ((1/((2^d:ℕ):ℝ))/D.thickness)^3
  let F := fun z : Fin n × Index => (parentLabel D a (2^f) z.1,heightLabel D a rho z.2)
  have hV (d : ℕ) : 0 < V d := by dsimp [V]; positivity
  have hRp : (R.filter (fun i => parentLabel D a (2^c) i=p)).Nonempty := by
    obtain ⟨z,hz⟩ := hEn
    exact ⟨z.1,mem_filter.mpr ⟨(mem_filter.mp (hE hz)).2,hp z hz⟩⟩
  have hcoarse := (Hpop ⟨c,by omega⟩ p hRp).1
  have hsum : (E.card:ℝ)=∑c∈E.image F,((E.filter (fun z => F z=c)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image F E
  have hcap : D.thickness*E.card ≤
      (43904*rho)*(D.thickness^(-zeta)*V f)*(E.image F).card := by
    rw [hsum,mul_sum]
    calc
      _ ≤ ∑_c∈E.image F,(43904*rho)*(D.thickness^(-zeta)*V f) := by
        apply sum_le_sum
        intro c hc
        obtain ⟨z,hz,hzc⟩ := mem_image.mp hc
        let Q := R.filter (fun i => parentLabel D a (2^f) i=c.1)
        let A := E.filter (fun z => parentLabel D a (2^f) z.1=c.1)
        have hAR : A⊆retained original Q := by
          intro z hz
          have he := (mem_filter.mp hz).1
          have hq := (mem_filter.mp hz).2
          have hzz := hE he
          simp only [retained,mem_filter] at hzz ⊢
          exact ⟨hzz.1,mem_filter.mpr ⟨hzz.2,hq⟩⟩
        have hQn : Q.Nonempty :=
          ⟨z.1,mem_filter.mpr ⟨(mem_filter.mp (hE hz)).2,congrArg Prod.fst hzc⟩⟩
        have heq : E.filter (fun z => F z=c)=heightEdges D a rho A c.2 := by
          ext z
          simp only [heightEdges,A,F,mem_filter,Prod.ext_iff]
          tauto
        rw [heq]
        exact (retained_height_capacity h original horiginal ha level heightDepth hdy hhlevel Q A hAR c.2).trans
          (mul_le_mul_of_nonneg_left (Hpop ⟨f,by omega⟩ c.1 hQn).2 (by positivity))
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  have hcross : mu*(D.thickness^zeta*V c) ≤
      (D.thickness^(-zeta)*V f)*((43904*rho)*(E.image F).card) := by
    calc
      _ ≤ mu*(R.filter (fun i => parentLabel D a (2^c) i=p)).card :=
        mul_le_mul_of_nonneg_left hcoarse hmu
      _ ≤ D.thickness*E.card := hret
      _ ≤ _ := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hcap
  have hden : 0 < D.thickness^(-zeta)*V f := mul_pos (Real.rpow_pos_of_pos hd _) (hV f)
  have hlo : mu*((D.thickness^zeta*V c)/(D.thickness^(-zeta)*V f)) ≤
      (43904*rho)*(E.image F).card := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hcross
  have hr : (0:ℝ)<1/((2^f:ℕ):ℝ) := by positivity
  rw [show (D.thickness^zeta*V c)/(D.thickness^(-zeta)*V f)=
      D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^c:ℕ):ℝ))^3 by
    dsimp [V]
    rw [scale_ratio D.thickness _ _ zeta (-zeta) hd hr]
    rw [show zeta-(-zeta)=2*zeta by ring]
    congr 2
    simp only [div_eq_mul_inv,one_mul,inv_inv]
    exact mul_comm _ _] at hlo
  simpa only [phaseHeightLabels,rho,F,mul_assoc] using hlo

/-- Original height capacity at an independent installed outer height. -/
theorem parent_height_population_at_height {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (heightDepth c : ℕ) (hhlevel : heightDepth ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (hEn : E.Nonempty)
    (p : Parent) (hp : ∀z∈E,parentLabel D a (2^c) z.1=p)
    (mu : ℝ)
    (hret : mu*(R.filter (fun i => parentLabel D a (2^c) i=p)).card ≤ D.thickness*E.card) :
    mu ≤ (43904*(64/((2^heightDepth:ℕ):ℝ)))*(heightLabels D a (64/((2^heightDepth:ℕ):ℝ)) E).card := by
  obtain ⟨horiginal,hdy,ha,_hRn,_hnR,_hshade,_hdensity,_hcw,_Hpop⟩ := Hbackbone
  let Q := R.filter (fun i => parentLabel D a (2^c) i=p)
  let rho : ℝ := 64/((2^heightDepth:ℕ):ℝ)
  have hEQ : E⊆retained original Q := by
    intro z hz
    have hzz := hE hz
    simp only [retained,mem_filter] at hzz ⊢
    exact ⟨hzz.1,mem_filter.mpr ⟨hzz.2,hp z hz⟩⟩
  have hQn : Q.Nonempty := by
    obtain ⟨z,hz⟩ := hEn
    exact ⟨z.1,(mem_filter.mp (hEQ hz)).2⟩
  have hQr : (0:ℝ)<Q.card := Nat.cast_pos.mpr (card_pos.mpr hQn)
  have hsum : (E.card:ℝ)=∑t∈heightLabels D a rho E,((heightEdges D a rho E t).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image (fun z : Fin n × Index => heightLabel D a rho z.2) E
  have hcap : D.thickness*E.card ≤
      ((43904*rho)*(heightLabels D a rho E).card)*(Q.card:ℝ) := by
    rw [hsum,mul_sum]
    calc
      _ ≤ ∑_t∈heightLabels D a rho E,(43904*rho)*(Q.card:ℝ) :=
        sum_le_sum (fun t _ht => retained_height_capacity h original horiginal ha level heightDepth hdy hhlevel Q E hEQ t)
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  exact (mul_le_mul_iff_left₀ hQr).mp (hret.trans hcap)

end NativeNestedPopulationProfiles
