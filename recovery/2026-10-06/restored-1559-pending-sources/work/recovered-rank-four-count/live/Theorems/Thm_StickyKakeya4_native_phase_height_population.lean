import Theorems.Thm_StickyKakeya4_native_population_parent_selection
import Theorems.Thm_StickyKakeya4_native_anisotropic_column_menus

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

noncomputable section
namespace NativePhaseHeightPopulation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalIncidenceCounts NativeOriginalParentSelection NativeOriginalParentDensityCore
open NativePaddedCellFiberCount NativeLocalParentPhysicalMap NativeContractedUnitParent
open NativeAnisotropicShortRowGeometry NativeActivePhasePopulation
open NativeMiddleWindowBalance NativeCoarseAncestorCounts
open scoped BigOperators

/-- Literal translated height in the actual parent physical chart. -/
def heightLabel {n : ℕ} (D : FiniteScaleSource n) (a H : ℝ) (k : Index) : ℤ :=
  ⌊(mesh D*(((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2))/H⌋

lemma column_height_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N : ℕ) (p : Parent) (sigma H : ℝ) (k : Index) :
    columnLabel D a N p sigma H k (3:Fin 4)=heightLabel D a H k := by
  simp only [columnLabel,chartWidth,if_true,NativeLocalParentPhysicalMap.physicalMap,baseMap,contractPoint,
    show (3:Fin 4)=Fin.last 3 by rfl,ActualSlopeSource.heightPoint_last,
    PiLp.smul_apply,smul_eq_mul,heightLabel,cellCenter]
  congr 1
  push_cast
  ring

lemma heightLabel_integer {n : ℕ} {D : FiniteScaleSource n} (hd : 0 < D.thickness)
    (a : ℝ) (B : ℕ) (hB : 0 < B) (k : Index) :
    heightLabel D a ((B:ℝ)*mesh D) k=(k (3:Fin 4)-shift D a)/(B:ℕ) := by
  have hm : mesh D≠0 := (half_pos hd).ne'
  have hBr : (B:ℝ)≠0 := by exact_mod_cast hB.ne'
  have he : (mesh D*(((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2))/((B:ℝ)*mesh D)=
      (((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)/(B:ℝ) := by field_simp
  rw [heightLabel,he,Int.floor_div_natCast]
  congr 1
  rw [Int.floor_intCast_add]
  norm_num

/-- One actual translated height cell contains exactly B possible old time
rows, each having the proved original per-tube capacity21952. -/
theorem height_row_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (B : ℕ) (hB : 0 < B) (i : Fin n) (t : ℤ) :
    ((original i).filter (fun k => heightLabel D a ((B:ℝ)*mesh D) k=t)).card ≤ 21952*B := by
  let S := (original i).filter (fun k => heightLabel D a ((B:ℝ)*mesh D) k=t)
  let rs := Icc ((B:ℤ)*t) ((B:ℤ)*t+B-1)
  have hBi : (0:ℤ)<B := by exact_mod_cast hB
  have hm : ∀k∈S,k (3:Fin 4)-shift D a∈rs := by
    intro k hk
    have he := (mem_filter.mp hk).2
    rw [heightLabel_integer h.1.2.1 a B hB] at he
    have hlo := (Int.le_ediv_iff_mul_le hBi).mp he.ge
    have hhi := (Int.ediv_lt_iff_lt_mul hBi).mp (show (k (3:Fin 4)-shift D a)/(B:ℤ)<t+1 by omega)
    apply mem_Icc.mpr
    constructor <;> nlinarith
  have hc : ∀r∈rs,(S.filter (fun k => k (3:Fin 4)-shift D a=r)).card ≤ 21952 := by
    intro r _hr
    exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans
      (original_row_card_le h original horiginal ha i r)
  have hh := card_le_mul_card_image_of_maps_to hm 21952 hc
  have hrs : rs.card=B := by
    have hh : (rs.card:ℤ)=B := by
      dsimp [rs]
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simpa only [hrs] using hh

lemma dyadic_height_mesh {n : ℕ} {D : FiniteScaleSource n} (level m : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level) :
    ((128*2^(level-m):ℕ):ℝ)*mesh D=64/((2^m:ℕ):ℝ) := by
  have hp : (2:ℝ)^level=(2:ℝ)^m*(2:ℝ)^(level-m) := by
    rw [←pow_add,Nat.add_sub_of_le hm]
  simp only [mesh,hdy,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,inv_pow]
  rw [hp]
  field_simp
  norm_num

/-- The original per-tube capacity at the actual coarser translated height
is43904H/delta, including the original chart's genuine translation. -/
theorem dyadic_height_row_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level)
    (i : Fin n) (t : ℤ) :
    D.thickness*((original i).filter
      (fun k => heightLabel D a (64/((2^m:ℕ):ℝ)) k=t)).card ≤
        43904*(64/((2^m:ℕ):ℝ)) := by
  have hscale := dyadic_height_mesh level m hdy hm
  have hh := height_row_card h original horiginal ha (128*2^(level-m)) (by positivity) i t
  rw [hscale] at hh
  have hc : (((original i).filter (fun k => heightLabel D a (64/((2^m:ℕ):ℝ)) k=t)).card:ℝ) ≤
      21952*((128*2^(level-m):ℕ):ℝ) := by exact_mod_cast hh
  calc
    _ ≤ D.thickness*(21952*((128*2^(level-m):ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left hc h.1.2.1.le
    _ = 43904*(((128*2^(level-m):ℕ):ℝ)*mesh D) := by unfold mesh; ring
    _ = _ := by rw [hscale]

def heightEdges {n : ℕ} (D : FiniteScaleSource n) (a H : ℝ)
    (E : Finset (Fin n × Index)) (t : ℤ) : Finset (Fin n × Index) :=
  E.filter (fun z => heightLabel D a H z.2=t)

def phaseHeightLabels {n : ℕ} (D : FiniteScaleSource n) (a H : ℝ) (f : ℕ)
    (E : Finset (Fin n × Index)) : Finset (Parent × ℤ) :=
  E.image (fun z => (parentLabel D a (2^f) z.1,heightLabel D a H z.2))

/-- Summing actual row capacities over the original tube labels incurs no
incidence multiplicity or new weight. -/
theorem retained_height_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level)
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (t : ℤ) :
    D.thickness*(heightEdges D a (64/((2^m:ℕ):ℝ)) E t).card ≤
      (43904*(64/((2^m:ℕ):ℝ)))*(R.card:ℝ) := by
  let rows := fun i => (original i).filter (fun k => heightLabel D a (64/((2^m:ℕ):ℝ)) k=t)
  have hs : heightEdges D a (64/((2^m:ℕ):ℝ)) E t⊆retained rows R := by
    rintro ⟨i,k⟩ hz
    obtain ⟨hzE,hzt⟩ := mem_filter.mp hz
    have hzR := hE hzE
    simp only [retained,mem_filter,mem_incidences] at hzR ⊢
    exact ⟨mem_filter.mpr ⟨hzR.1,hzt⟩,hzR.2⟩
  have hc : ((heightEdges D a (64/((2^m:ℕ):ℝ)) E t).card:ℝ) ≤
      ∑i∈R,((rows i).card:ℝ) := by
    have hh := card_le_card hs
    rw [retained_card rows R] at hh
    exact_mod_cast hh
  calc
    _ ≤ D.thickness*(∑i∈R,((rows i).card:ℝ)) := mul_le_mul_of_nonneg_left hc h.1.2.1.le
    _ = ∑i∈R,D.thickness*((rows i).card:ℝ) := mul_sum _ _ _
    _ ≤ ∑_i∈R,43904*(64/((2^m:ℕ):ℝ)) :=
      sum_le_sum (fun i _hi => dyadic_height_row_capacity h original horiginal ha level m hdy hm i t)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

/-- The joint fine-phase/translated-height numerator is derived from actual
parent population density, with no lower on any individual shading row. -/
theorem phase_height_population {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f : ℕ) (hmf : m ≤ f) (hfl : f ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (hEn : E.Nonempty)
    (p : Parent) (hp : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hret : mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*E.card) :
    mu*D.thickness^(2*zeta)*(((2^f:ℕ):ℝ)/((2^m:ℕ):ℝ))^3 ≤
      (43904*(64/((2^m:ℕ):ℝ)))*(phaseHeightLabels D a (64/((2^m:ℕ):ℝ)) f E).card := by
  obtain ⟨horiginal,hdy,ha,_hRn,_hnR,_hshade,_hdensity,_hcw,Hpop⟩ := Hbackbone
  have hd := h.1.2.1
  let rho : ℝ := 64/((2^m:ℕ):ℝ)
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
        exact (retained_height_capacity h original horiginal ha level m hdy (hmf.trans hfl) Q A hAR c.2).trans
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

def heightLabels {n : ℕ} (D : FiniteScaleSource n) (a H : ℝ)
    (E : Finset (Fin n × Index)) : Finset ℤ := E.image (fun z => heightLabel D a H z.2)

/-- The same population density gives the occupied-height lower directly,
without a loss from the phase AD comparison. -/
theorem parent_height_population {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m : ℕ) (hm : m ≤ level)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R) (hEn : E.Nonempty)
    (p : Parent) (hp : ∀z∈E,parentLabel D a (2^m) z.1=p)
    (mu : ℝ)
    (hret : mu*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤ D.thickness*E.card) :
    mu ≤ (43904*(64/((2^m:ℕ):ℝ)))*(heightLabels D a (64/((2^m:ℕ):ℝ)) E).card := by
  obtain ⟨horiginal,hdy,ha,_hRn,_hnR,_hshade,_hdensity,_hcw,_Hpop⟩ := Hbackbone
  let Q := R.filter (fun i => parentLabel D a (2^m) i=p)
  let rho : ℝ := 64/((2^m:ℕ):ℝ)
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
        sum_le_sum (fun t _ht => retained_height_capacity h original horiginal ha level m hdy hm Q E hEQ t)
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  exact (mul_le_mul_iff_left₀ hQr).mp (hret.trans hcap)

lemma original_translated_height_abs {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (z : Fin n × Index) (hz : z∈incidences original) :
    |mesh D*(((z.2 (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)| ≤ 4 := by
  have hh := (NativeOriginalParentPhysicalData.original_cell_bounds h original horiginal a ha hz).1
  change |(mesh D/4)*(((z.2 (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)| ≤ 1 at hh
  have he : mesh D*(((z.2 (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)=
      4*((mesh D/4)*(((z.2 (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)) := by ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
  linarith only [hh]

/-- The original fixed graph window bounds all occupied translated heights.
The origin is the actual chart translation, not the unshifted raw grid. -/
theorem height_population_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (H : ℝ) (hH : 0<H) (hH1 : H ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) :
    H*(heightLabels D a H E).card ≤ 10 := by
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
    _ ≤ 10 := by linarith only [hH1]

end NativePhaseHeightPopulation
