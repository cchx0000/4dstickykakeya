import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

noncomputable section
namespace NativeActivePhasePopulation
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalParentDensityCore
open NativeOriginalPrunedMass NativeCoarseAncestorCounts NativeDyadicParentCells NativeMiddleWindowBalance
open scoped BigOperators ENNReal

def rowConstant : ℝ := 16*volumeConstant

lemma rowConstant_pos : 0<rowConstant := mul_pos (by norm_num) volumeConstant_pos

/-- Original cubical incidence mass has a uniform upper bound per full tube
label. This does not assert a lower bound for individual shading rows. -/
theorem retained_incidence_capacity {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (R : Finset (Fin n)) :
    D.thickness*(retained original R).card ≤ rowConstant*R.card := by
  have hd := h.1.2.1
  have hh := shadingMass_upper h R
  rw [retained_shading_eq D hd original horiginal R] at hh
  have hr := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (show 0 ≤ mesh D from (half_pos hd).le),
    ENNReal.toReal_ofReal hd.le,ENNReal.toReal_ofReal volumeConstant_pos.le] at hr
  change (retained original R).card*(D.thickness/2)^4 ≤
    (R.card:ℝ)*(volumeConstant*D.thickness^3) at hr
  apply (mul_le_mul_iff_right₀ (pow_pos hd 3)).mp
  calc
    _ = 16*((retained original R).card*(D.thickness/2)^4) := by ring
    _ ≤ 16*((R.card:ℝ)*(volumeConstant*D.thickness^3)) :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by unfold rowConstant; ring

lemma parent_retained_eq {n : ℕ} (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ) (p : Parent) :
    parentEdges D a N (retained original R) p=
      retained original (R.filter (fun i => parentLabel D a N i=p)) := by
  ext z
  simp only [parentEdges,retained,mem_filter]
  tauto

lemma parent_incidence_capacity {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (R : Finset (Fin n)) (a : ℝ) (N : ℕ) (E : Finset (Fin n × Index))
    (hE : E⊆retained original R) (p : Parent) :
    D.thickness*(parentEdges D a N E p).card ≤
      rowConstant*(R.filter (fun i => parentLabel D a N i=p)).card := by
  have hs : parentEdges D a N E p⊆parentEdges D a N (retained original R) p :=
    filter_subset_filter _ hE
  have hh := retained_incidence_capacity h original horiginal
    (R.filter (fun i => parentLabel D a N i=p))
  rw [←parent_retained_eq D original R a N p] at hh
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hs)) h.1.2.1.le).trans hh

def activePhases {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (f : ℕ)
    (E : Finset (Fin n × Index)) : Finset Parent :=
  E.image (fun z => parentLabel D a (2^f) z.1)

lemma activePhases_subset {n : ℕ} (D : FiniteScaleSource n) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a : ℝ) {m f : ℕ} (hmf : m ≤ f)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : ∀z∈E,parentLabel D a (2^m) z.1=p) :
    activePhases D a f E⊆descendants D R a f m p := by
  rw [←image_parent_fiber_eq_descendants D R a hmf p]
  intro q hq
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
  exact mem_image_of_mem _ (mem_filter.mpr ⟨(mem_filter.mp (hE hz)).2,hp z hz⟩)

/-- Paid incidence density relative to the complete R-parent forces an
actual active fine-phase lower. Both sides use the same R and original labels. -/
theorem active_phase_population {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f : ℕ) (hmf : m ≤ f) (hfl : f ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (hEn : E.Nonempty)
    (p : Parent) (hp : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hret : mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*E.card) :
    mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
      rowConstant*(activePhases D a f E).card ∧
    ((activePhases D a f E).card:ℝ) ≤
      D.thickness^(-2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 := by
  obtain ⟨horiginal,_hdy,_ha,_hRn,_hnR,_hshade,_hdensity,_hcw,Hpop⟩ := Hbackbone
  have hd := h.1.2.1
  let V (d : ℕ) : ℝ := ((1/((2^d:ℕ):ℝ))/D.thickness)^3
  have hV (d : ℕ) : 0<V d := by dsimp [V]; positivity
  have hsub := activePhases_subset D original R a hmf E hE p hp
  have hAn : (activePhases D a f E).Nonempty := hEn.image _
  have hdesc := coarse_ancestor_AD h R a zeta level Hpop hmf hfl p (hAn.mono hsub)
  have hRp : (R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty := by
    obtain ⟨z,hz⟩ := hEn
    exact ⟨z.1,mem_filter.mpr ⟨(mem_filter.mp (hE hz)).2,hp z hz⟩⟩
  have hcoarse := (Hpop ⟨m,by omega⟩ p hRp).1
  have hsum : (E.card:ℝ)=∑q∈activePhases D a f E,((parentEdges D a (2^f) E q).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image (fun z : Fin n × Index => parentLabel D a (2^f) z.1) E
  have hcap : D.thickness*E.card ≤
      rowConstant*(D.thickness^(-zeta)*V f)*(activePhases D a f E).card := by
    rw [hsum,mul_sum]
    calc
      _ ≤ ∑_q∈activePhases D a f E,rowConstant*(D.thickness^(-zeta)*V f) := by
        apply sum_le_sum
        intro q hq
        obtain ⟨z,hz,hzq⟩ := mem_image.mp hq
        have hqR : (R.filter (fun i => parentLabel D a (2^f) i=q)).Nonempty :=
          ⟨z.1,mem_filter.mpr ⟨(mem_filter.mp (hE hz)).2,hzq⟩⟩
        exact (parent_incidence_capacity h original horiginal R a (2^f) E hE q).trans
          (mul_le_mul_of_nonneg_left (Hpop ⟨f,by omega⟩ q hqR).2 rowConstant_pos.le)
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  have hcross : mu*(D.thickness^zeta*V m) ≤
      (D.thickness^(-zeta)*V f)*(rowConstant*(activePhases D a f E).card) := by
    calc
      _ ≤ mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card :=
        mul_le_mul_of_nonneg_left hcoarse hmu
      _ ≤ D.thickness*E.card := hret
      _ ≤ _ := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hcap
  have hden : 0<D.thickness^(-zeta)*V f := mul_pos (Real.rpow_pos_of_pos hd _) (hV f)
  have hlo : mu*((D.thickness^zeta*V m)/(D.thickness^(-zeta)*V f)) ≤
      rowConstant*(activePhases D a f E).card := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hcross
  have hr : (0:ℝ)<1/((2^f:ℕ):ℝ) := by positivity
  rw [show (D.thickness^zeta*V m)/(D.thickness^(-zeta)*V f)=
      D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 by
    dsimp [V]
    rw [scale_ratio D.thickness _ _ zeta (-zeta) hd hr]
    rw [show zeta-(-zeta)=2*zeta by ring]
    congr 2
    simp only [div_eq_mul_inv,one_mul,inv_inv]
    exact mul_comm _ _] at hlo
  exact ⟨by simpa only [mul_assoc] using hlo,
    (Nat.cast_le.mpr (card_le_card hsub)).trans hdesc.2⟩

end NativeActivePhasePopulation
