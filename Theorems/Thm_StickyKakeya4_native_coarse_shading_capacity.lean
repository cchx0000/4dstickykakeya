import Theorems.Thm_StickyKakeya4_native_padded_cell_fiber_count
import Theorems.Thm_StickyKakeya4_native_original_pruned_mass
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
noncomputable section
namespace NativeCoarseShadingCapacity
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalPaddedCells NativePaddedCellFiberCount
open scoped BigOperators ENNReal

/-- Every projected cube meets the line of an original representative. The
integer multiplier retains exact dyadic compatibility with the source mesh. -/
def projectedLabel {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (B : ℕ)
    (j : Fin n) (k : Index) : Index :=
  wzDyadicCellIndex ((B:ℝ)*D.thickness/128) (frontPoint D a (0,0) j k)

def label {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N B : ℕ)
    (rep : Parent → Fin n) (e : Fin n × Index) : Parent × Index :=
  (parentLabel D a N e.1,projectedLabel D a B (rep (parentLabel D a N e.1)) e.2)

def coarse {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N B : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) : Finset (Parent × Index) :=
  E.image (label D a N B rep)

def rows {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N B : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) : Finset Index :=
  ((coarse D a N B rep E).filter (fun e => e.1=p)).image Prod.snd

/-- The row formula does not depend on which original representative was
chosen. Exactly 8B consecutive original rows can map to one output row. -/
lemma projectedLabel_height {n : ℕ} {D : FiniteScaleSource n} (hd : 0 < D.thickness)
    (a : ℝ) (B : ℕ) (hB : 0 < B) (j : Fin n) (k : Index) :
    projectedLabel D a B j k (3:Fin 4)=(k (3:Fin 4)-shift D a)/(8*B:ℕ) := by
  change ⌊frontPoint D a (0,0) j k (3:Fin 4)/((B:ℝ)*D.thickness/128)⌋=_
  rw [frontPoint_height]
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have he : (oldTime D a k/128)/((B:ℝ)*D.thickness/128)=
      (((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)/(8*B:ℕ) := by
    dsimp [oldTime,ShearBinFibers.oldCenter,chartIndex,mesh]
    push_cast
    field_simp [hd.ne',hBr.ne']
    ring
  rw [he,Int.floor_div_natCast]
  have hx : ⌊(((k (3:Fin 4)-shift D a:ℤ):ℝ)+1/2)⌋=k (3:Fin 4)-shift D a := by
    rw [Int.floor_intCast_add]
    norm_num
  rw [hx]

/-- This is a capacity bound on the ORIGINAL cells, projected to any chosen
original representative; no per-tube shading lower bound is used. -/
theorem projected_fiber_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (B : ℕ) (hB : 0 < B) (i j : Fin n) (q : Index) :
    ((original i).filter (fun k => projectedLabel D a B j k=q)).card ≤ 175616*B := by
  let S := (original i).filter (fun k => projectedLabel D a B j k=q)
  let b : ℤ := 8*(B:ℤ)
  let rs := Icc (b*q (3:Fin 4)) (b*q (3:Fin 4)+b-1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hm : ∀k∈S,k (3:Fin 4)-shift D a∈rs := by
    intro k hk
    have he := congrFun (mem_filter.mp hk).2 (3:Fin 4)
    rw [projectedLabel_height h.1.2.1 a B hB] at he
    have he' : (k (3:Fin 4)-shift D a)/b=q (3:Fin 4) := by
      simpa only [b,Nat.cast_mul,Nat.cast_ofNat] using he
    apply mem_Icc.mpr
    have hlo := (Int.le_ediv_iff_mul_le hb).mp he'.ge
    have hhi := (Int.ediv_lt_iff_lt_mul hb).mp (show (k (3:Fin 4)-shift D a)/b<q (3:Fin 4)+1 by omega)
    constructor <;> nlinarith
  have hc : ∀r∈rs,(S.filter (fun k => k (3:Fin 4)-shift D a=r)).card ≤ 21952 := by
    intro r _hr
    exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans
      (original_row_card_le h original horiginal ha i r)
  have H := card_le_mul_card_image_of_maps_to hm 21952 hc
  have hrs : rs.card=8*B := by
    have hh : (rs.card:ℤ)=8*(B:ℤ) := by
      dsimp [rs]
      rw [Int.card_Icc_of_le _ _ (by nlinarith)]
      dsimp [b] at *
      omega
    exact_mod_cast hh
  rw [hrs] at H
  simpa only [←Nat.mul_assoc,show 21952*8=175616 by norm_num] using H

/-- A joint coarse incidence fiber is charged to the ACTUAL full original
parent population, and the original row capacity for each of those tubes. -/
theorem joint_fiber_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n)
    (E : Finset (Fin n × Index))
    (hE : ∀e∈E,e.1∈R ∧ e.2∈original e.1) (v : Parent × Index) :
    (E.filter (fun e => label D a N B rep e=v)).card ≤
      (175616*B)*(R.filter (fun i => parentLabel D a N i=v.1)).card := by
  let S := E.filter (fun e => label D a N B rep e=v)
  apply card_le_mul_card_image_of_maps_to (f := Prod.fst)
  · intro e he
    obtain ⟨he,hv⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨(hE e he).1,congrArg Prod.fst hv⟩
  · intro i _hi
    let T := S.filter (fun e => e.1=i)
    have hinj : Set.InjOn Prod.snd (T:Set (Fin n × Index)) := by
      intro e he f hf hef
      exact Prod.ext ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm) hef
    have hsub : T.image Prod.snd ⊆ (original i).filter (fun k => projectedLabel D a B (rep v.1) k=v.2) := by
      intro k hk
      obtain ⟨e,he,rfl⟩ := mem_image.mp hk
      obtain ⟨he,hei⟩ := mem_filter.mp he
      obtain ⟨he,hv⟩ := mem_filter.mp he
      have hp : parentLabel D a N e.1=v.1 := congrArg Prod.fst hv
      have hq : projectedLabel D a B (rep (parentLabel D a N e.1)) e.2=v.2 := congrArg Prod.snd hv
      rw [hp] at hq
      refine mem_filter.mpr ⟨?_,hq⟩
      simpa only [hei] using (hE e he).2
    calc
      T.card=(T.image Prod.snd).card := (card_image_iff.mpr hinj).symm
      _ ≤ ((original i).filter (fun k => projectedLabel D a B (rep v.1) k=v.2)).card := card_le_card hsub
      _ ≤ 175616*B := projected_fiber_card_le h original horiginal ha B hB i (rep v.1) v.2

/-- The full-parent multiplicity upper bound is consumed on the same
original incidence family before any color or deletion is selected. -/
theorem total_incidence_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a M : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n)
    (E : Finset (Fin n × Index))
    (hE : ∀e∈E,e.1∈R ∧ e.2∈original e.1)
    (hM : ∀p∈R.image (parentLabel D a N),((R.filter (fun i => parentLabel D a N i=p)).card:ℝ) ≤ M) :
    (E.card:ℝ) ≤ (175616*(B:ℝ)*M)*((coarse D a N B rep E).card:ℝ) := by
  have hsum : (E.card:ℝ)=∑v∈coarse D a N B rep E,((E.filter (fun e => label D a N B rep e=v)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image (label D a N B rep) E
  rw [hsum]
  calc
    _ ≤ ∑ _v∈coarse D a N B rep E,175616*(B:ℝ)*M := by
      apply sum_le_sum
      intro v hv
      obtain ⟨e,he,hev⟩ := mem_image.mp hv
      have hp : v.1∈R.image (parentLabel D a N) :=
        mem_image.mpr ⟨e.1,(hE e he).1,congrArg Prod.fst hev⟩
      have hc : ((E.filter (fun e => label D a N B rep e=v)).card:ℝ) ≤
          (175616*(B:ℝ))*((R.filter (fun i => parentLabel D a N i=v.1)).card:ℝ) := by
        exact_mod_cast joint_fiber_card_le h original horiginal ha R N B hB rep E hE v
      exact hc.trans (mul_le_mul_of_nonneg_left (hM v.1 hp) (by positivity))
    _ = _ := by simp [mul_comm]


/-- Exact cancellation of the four scale powers. The input is the derived
incidence capacity, not a density or AD certificate on the output. -/
lemma cell_mass_scale_cancellation {delta rho loss : ℝ} {B : ℕ} {fine coarseCount : ℝ}
    (hd : 0 < delta) (_hr : 0 < rho) (hloss : 0 ≤ loss) (hc : 0 ≤ coarseCount)
    (hB : (B:ℝ)=4096*rho/delta)
    (hcount : fine ≤ 175616*(B:ℝ)*(loss*(rho/delta)^3)*coarseCount) :
    fine*(delta/2)^4 ≤ 43*loss*(coarseCount*((B:ℝ)*delta/128)^4) := by
  have hcoef : 175616*(B:ℝ)*(loss*(rho/delta)^3)*coarseCount*(delta/2)^4=
      (175616/4096:ℝ)*loss*(coarseCount*((B:ℝ)*delta/128)^4) := by
    rw [hB]
    field_simp [hd.ne']
    ring
  calc
    _ ≤ (175616*(B:ℝ)*(loss*(rho/delta)^3)*coarseCount)*(delta/2)^4 :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := hcoef
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hc (by positivity))
      exact mul_le_mul_of_nonneg_right (by norm_num : (175616/4096:ℝ) ≤ 43) hloss

/-- The retained incidence family contains every original shading cell on R. -/
def retained {n : ℕ} (original : Fin n → Finset Index) (R : Finset (Fin n)) :
    Finset (Fin n × Index) := (incidences original).filter (fun e => e.1∈R)

lemma retained_spec {n : ℕ} (original : Fin n → Finset Index) (R : Finset (Fin n))
    (e : Fin n × Index) : e∈retained original R ↔ e.1∈R ∧ e.2∈original e.1 := by
  rcases e with ⟨i,k⟩
  simp only [retained,mem_filter,mem_incidences,and_comm]

lemma retained_card {n : ℕ} (original : Fin n → Finset Index) (R : Finset (Fin n)) :
    (retained original R).card=∑i∈R,(original i).card := by
  rw [card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=R)
    (fun e he => ((retained_spec original R e).mp he).1)]
  apply sum_congr rfl
  intro i hi
  have he : (retained original R).filter (fun e => e.1=i)=(original i).image (fun k => (i,k)) := by
    ext e
    rcases e with ⟨j,k⟩
    simp only [mem_filter,retained_spec,mem_image,Prod.mk.injEq]
    aesop
  rw [he,card_image_of_injective _ (fun x y h => congrArg Prod.snd h)]

lemma coarse_card_sum_rows {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N B : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (P : Finset Parent)
    (hP : ∀e∈E,parentLabel D a N e.1∈P) :
    (coarse D a N B rep E).card=∑p∈P,(rows D a N B rep E p).card := by
  have hm : ∀v∈coarse D a N B rep E,v.1∈P := by
    intro v hv
    obtain ⟨e,he,rfl⟩ := mem_image.mp hv
    exact hP e he
  rw [card_eq_sum_card_fiberwise hm]
  apply sum_congr rfl
  intro p _hp
  symm
  apply card_image_iff.mpr
  intro e he f hf hef
  exact Prod.ext ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm) hef

lemma retained_shading_real {n : ℕ} {D : FiniteScaleSource n} (hd : 0 < D.thickness)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i) (R : Finset (Fin n)) :
    (∑i∈R,(volume (D.shading i)).toReal)=((retained original R).card:ℝ)*(D.thickness/2)^4 := by
  simp_rw [horiginal]
  simp only [mesh,volume_wzCellShading (half_pos hd),ENNReal.toReal_mul,
    ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofReal (half_pos hd).le]
  rw [←sum_mul]
  congr 1
  exact_mod_cast (retained_card original R).symm

lemma coarse_shading_real {n : ℕ} {D : FiniteScaleSource n} (hd : 0 < D.thickness)
    (a : ℝ) (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n)
    (E : Finset (Fin n × Index)) (P : Finset Parent)
    (hP : ∀e∈E,parentLabel D a N e.1∈P) :
    (∑p∈P,(volume (wzCellShading ((B:ℝ)*D.thickness/128) (fun _ : Fin 1 => rows D a N B rep E p) 0)).toReal)=
      ((coarse D a N B rep E).card:ℝ)*((B:ℝ)*D.thickness/128)^4 := by
  have hm : 0 < (B:ℝ)*D.thickness/128 := by positivity
  simp_rw [volume_wzCellShading hm,ENNReal.toReal_mul,
    ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofReal hm.le]
  rw [←sum_mul]
  congr 1
  exact_mod_cast (coarse_card_sum_rows D a N B rep E P hP).symm

/-- Actual aggregate shading mass survives spatial coarse projection with
only the original parent AD loss. No per-fine-tube density is assumed or
inferred. The output sets are the literal front-meeting cube images. -/
theorem actual_aggregate_shading_transfer {n : ℕ} {D : FiniteScaleSource n} {eta a rho zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n)
    (hr : 0 < rho) (hscale : (B:ℝ)=4096*rho/D.thickness)
    (hM : ∀p∈R.image (parentLabel D a N),((R.filter (fun i => parentLabel D a N i=p)).card:ℝ) ≤
      D.thickness^(-zeta)*(rho/D.thickness)^3) :
    (∑i∈R,(volume (D.shading i)).toReal) ≤ 43*D.thickness^(-zeta)*
      (∑p∈R.image (parentLabel D a N),
        (volume (wzCellShading ((B:ℝ)*D.thickness/128)
          (fun _ : Fin 1 => rows D a N B rep (retained original R) p) 0)).toReal) := by
  have hE : ∀e∈retained original R,e.1∈R ∧ e.2∈original e.1 :=
    fun e he => (retained_spec original R e).mp he
  have hP : ∀e∈retained original R,parentLabel D a N e.1∈R.image (parentLabel D a N) :=
    fun e he => mem_image_of_mem _ (hE e he).1
  rw [retained_shading_real h.1.2.1 original horiginal R,
    coarse_shading_real h.1.2.1 a N B hB rep (retained original R) _ hP]
  exact cell_mass_scale_cancellation h.1.2.1 hr (Real.rpow_pos_of_pos h.1.2.1 _).le (by positivity) hscale
    (total_incidence_capacity h original horiginal ha R N B hB rep (retained original R) hE hM)

end NativeCoarseShadingCapacity
