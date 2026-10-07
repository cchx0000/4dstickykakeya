import Theorems.Thm_StickyKakeya4_native_phase_height_population
import Theorems.Thm_StickyKakeya4_native_height_window_relations
import Theorems.Thm_StickyKakeya4_native_column_population_bounds
import Theorems.Thm_StickyKakeya4_native_population_parent_selection
import Theorems.Thm_StickyKakeya4_native_anisotropic_column_menus

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

noncomputable section
namespace NativeVariableHeightPopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalParentDensityCore
open NativePaddedCellFiberCount NativeLocalParentPhysicalMap NativeContractedUnitParent
open NativeAnisotropicShortRowGeometry NativeActivePhasePopulation
open NativeMiddleWindowBalance NativeCoarseAncestorCounts
open scoped BigOperators

open NativePhaseHeightPopulation NativeColumnPopulationBounds

theorem phase_height_population {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f b : ℕ) (hmf : m ≤ f) (hfl : f ≤ level) (hbL : b ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (hEn : E.Nonempty)
    (p : Parent) (hp : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hret : mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*E.card) :
    mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
      (43904*(64/((2^b:ℕ):ℝ)))*(phaseHeightLabels D a (64/((2^b:ℕ):ℝ)) f E).card := by
  obtain ⟨horiginal,hdy,ha,_hRn,_hnR,_hshade,_hdensity,_hcw,Hpop⟩ := Hbackbone
  have hd := h.1.2.1
  let rho : ℝ := 64/((2^b:ℕ):ℝ)
  let V (d : ℕ) : ℝ := ((1/((2^d:ℕ):ℝ))/D.thickness)^3
  let F := fun z : Fin n × Index => (parentLabel D a (2^f) z.1,heightLabel D a rho z.2)
  have hV (d : ℕ) : 0 < V d := by dsimp [V]; positivity
  have hRp : (R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty := by
    obtain ⟨z,hz⟩ := hEn
    exact ⟨z.1,mem_filter.mpr ⟨(mem_filter.mp (hE hz)).2,hp z hz⟩⟩
  have hcoarse := (Hpop ⟨m,by omega⟩ p hRp).1
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
        exact (retained_height_capacity h original horiginal ha level b hdy hbL Q A hAR c.2).trans
          (mul_le_mul_of_nonneg_left (Hpop ⟨f,by omega⟩ c.1 hQn).2 (by positivity))
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  have hcross : mu*(D.thickness^zeta*V m) ≤
      (D.thickness^(-zeta)*V f)*((43904*rho)*(E.image F).card) := by
    calc
      _ ≤ mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card :=
        mul_le_mul_of_nonneg_left hcoarse hmu
      _ ≤ D.thickness*E.card := hret
      _ ≤ _ := by simpa only [mul_assoc,mul_left_comm,mul_comm] using hcap
  have hden : 0 < D.thickness^(-zeta)*V f := mul_pos (Real.rpow_pos_of_pos hd _) (hV f)
  have hlo : mu*((D.thickness^zeta*V m)/(D.thickness^(-zeta)*V f)) ≤
      (43904*rho)*(E.image F).card := by
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
  simpa only [phaseHeightLabels,rho,F,mul_assoc] using hlo

theorem parent_height_population {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m b : ℕ) (hbL : b ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (hEn : E.Nonempty)
    (p : Parent) (hp : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (mu : ℝ)
    (hret : mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*E.card) :
    mu ≤ (43904*(64/((2^b:ℕ):ℝ)))*(heightLabels D a (64/((2^b:ℕ):ℝ)) E).card := by
  obtain ⟨horiginal,hdy,ha,_hRn,_hnR,_hshade,_hdensity,_hcw,_Hpop⟩ := Hbackbone
  let Q := R.filter (fun i => parentLabel D a (2^m) i=p)
  let rho : ℝ := 64/((2^b:ℕ):ℝ)
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
        sum_le_sum (fun t _ht => retained_height_capacity h original horiginal ha level b hdy hbL Q E hEQ t)
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  exact (mul_le_mul_iff_left₀ hQr).mp (hret.trans hcap)

theorem height_population_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (H : ℝ) (hH : 0<H)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) :
    H*(heightLabels D a H E).card ≤ 8+2*H := by
  let lo : ℤ := ⌊(-4:ℝ)/H⌋
  let hi : ℤ := ⌊(4:ℝ)/H⌋
  have hlohi : lo ≤ hi := Int.floor_mono (by apply div_le_div_of_nonneg_right (by norm_num) hH.le)
  have hsub : heightLabels D a H E⊆Icc lo hi := by
    intro t ht
    obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
    have hb := abs_le.mp (original_translated_height_abs h original horiginal ha z (hE hz))
    exact mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right hb.1 hH.le),
      Int.floor_mono (div_le_div_of_nonneg_right hb.2 hH.le)⟩
  have hcard : ((Icc lo hi).card:ℝ)=(hi:ℝ)+1-(lo:ℝ) := by
    exact_mod_cast Int.card_Icc_of_le lo hi (by omega)
  have hbound : ((Icc lo hi).card:ℝ) ≤ 8/H+2 := by
    rw [hcard]
    have hl := Int.lt_floor_add_one ((-4:ℝ)/H)
    have hh := Int.floor_le ((4:ℝ)/H)
    change (-4:ℝ)/H < (lo:ℝ)+1 at hl
    change (hi:ℝ) ≤ (4:ℝ)/H at hh
    ring_nf at hl hh ⊢
    linarith only [hl,hh]
  calc
    _ ≤ H*((Icc lo hi).card:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub)) hH.le
    _ ≤ H*(8/H+2) := mul_le_mul_of_nonneg_left hbound hH.le
    _ = 8+2*H := by field_simp


lemma height_population_upper_eight {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (H : ℝ) (hH : 0 < H) (hH8 : H ≤ 8)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) :
    H*(heightLabels D a H E).card ≤ 24 :=
  (height_population_upper h original horiginal ha H hH E hE).trans (by linarith)

/-- Literal phase/column pairs with independent horizontal and height depths. -/
def columnPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f b : ℕ) (p : Parent)
    (z : Fin n × Index) : Parent × Index :=
  (parentLabel D a (2^f) z.1,
    columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^b:ℕ):ℝ)) z.2)

lemma column_phase_height_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f b : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) :
    (((parentEdges D a (2^m) E p).image (columnPair D a m f b p)).image
      (fun q => (q.1,q.2 (3:Fin 4))))=
      phaseHeightLabels D a (64/((2^b:ℕ):ℝ)) f (parentEdges D a (2^m) E p) := by
  simp only [phaseHeightLabels,columnPair,image_image,Function.comp_def,column_height_readback]

lemma column_height_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f b : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) :
    (NativeHeightWindowRelations.points D a m f b E p).image (fun q => q (3:Fin 4))=
      heightLabels D a (64/((2^b:ℕ):ℝ)) (parentEdges D a (2^m) E p) := by
  simp only [heightLabels,NativeHeightWindowRelations.points,image_image,Function.comp_def,column_height_readback]

/-- The actual original parent density gives the variable-height numerator
and occupied-height lower. No incidence density inside an individual time
window or an individual tube is assumed. -/
theorem reference_numerator_lower {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (m f b : ℕ) (hmf : m ≤ f) (hfL : f ≤ level) (hbL : b ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 ≤ population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card) :
    let H := 64/((2^b:ℕ):ℝ)
    (population*D.thickness^(2*zeta)/43904)*(relativeWidth m f)^(-3:ℝ) ≤
      H*((parentEdges D a (2^m) E p).image (columnPair D a m f b p)).card ∧
    population/43904 ≤
      H*((NativeHeightWindowRelations.points D a m f b E p).image (fun q => q (3:Fin 4))).card := by
  let F := parentEdges D a (2^m) E p
  have hF : F⊆retained original R := (filter_subset _ _).trans hE
  have hparent : ∀z∈F,parentLabel D a (2^m) z.1=p := fun _z hz => (mem_filter.mp hz).2
  have hPH := phase_height_population h original R level HB m f b hmf hfL hbL F hF hp p hparent
    population hpopulation hret
  have hH := parent_height_population h original R level HB m b hbL F hF hp p hparent population hret
  have hJ : (phaseHeightLabels D a (64/((2^b:ℕ):ℝ)) f F).card ≤
      ((parentEdges D a (2^m) E p).image (columnPair D a m f b p)).card := by
    rw [←column_phase_height_image D a m f b E p]
    exact card_image_le
  have hJr : ((phaseHeightLabels D a (64/((2^b:ℕ):ℝ)) f F).card:ℝ) ≤
      ((parentEdges D a (2^m) E p).image (columnPair D a m f b p)).card := by exact_mod_cast hJ
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<43904)).mpr
    rw [←inverse_scale_cube]
    exact (hPH.trans (mul_le_mul_of_nonneg_left hJr (by positivity))).trans_eq (by ring)
  · rw [column_height_image D a m f b E p]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<43904)).mpr
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hH

end NativeVariableHeightPopulation
