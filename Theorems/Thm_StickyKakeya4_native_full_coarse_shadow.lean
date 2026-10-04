import Theorems.Thm_StickyKakeya4_native_coarse_source_mass
import Theorems.Thm_StickyKakeya4_native_coarse_direction_thinning
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3400000
noncomputable section
namespace NativeFullCoarseShadow
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCoarseDirectionThinning NativeCoarseCellSource NativeCoarseRepresentativeGeometry
open NativeCoarseShadingCapacity NativeCoarseShadingPruning NativeCoarseSourceProfiles NativeCoarseSourceMass
open NativeOriginalPrunedMass
open scoped BigOperators ENNReal

/-- The actual coarse cube shading attached to an original full parent. -/
def shadow {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) : Set E4 :=
  wzCellShading (32/((2^m:ℕ):ℝ))
    (fun _ : Fin 1 => rows D a (2^m) (NativeCoarseDyadicShading.block level m) rep E p) 0

lemma representative_injOn {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (N : ℕ) :
    Set.InjOn (representative h R a N) (R.image (parentLabel D a N):Set Parent) := by
  intro p hp q hq hpq
  calc
    p=parentLabel D a N (representative h R a N p) := (representative_spec h R a N hp).2.symm
    _ = parentLabel D a N (representative h R a N q) := congrArg _ hpq
    _ = q := (representative_spec h R a N hq).2

/-- The COMPLETE actual coarse shadow is a finite source of distinct genuine
marked lines. Coarse direction separation is not asserted for this family;
the extremal law is applied only to its separately admitted retained core. -/
def fullSource {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level m : ℕ)
    (E : Finset (Fin n × Index)) : FiniteScaleSource (R.image (parentLabel D a (2^m))).card :=
  let P := R.image (parentLabel D a (2^m))
  let rep := representative h R a (2^m)
  unweightedMarkedShadingSource (64/((2^m:ℕ):ℝ))
    (fun i => NativeContractedUnitParent.line D a (0,0) (rep (parentIndex P i)))
    (line_injective_of_direction_separated _ h.1.2.1 (by
      intro i j hij
      rw [direction_zero_parent h a,direction_zero_parent h a]
      apply h.1.2.2.2.2.2.2.2.2.2.1
      intro he
      apply hij
      apply parentIndex_injective P
      exact representative_injOn h R a (2^m) (parentIndex_mem P i) (parentIndex_mem P j) he))
    (fun i => shadow D a level m rep E (parentIndex P i))

lemma full_shading {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level m : ℕ)
    (E : Finset (Fin n × Index)) (i : Fin (R.image (parentLabel D a (2^m))).card) :
    (fullSource h R a level m E).shading i =
      shadow D a level m (representative h R a (2^m)) E
        (parentIndex (R.image (parentLabel D a (2^m))) i) := rfl

lemma shadow_ne_top {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) :
    volume (shadow D a level m rep E p) ≠ ⊤ := by
  unfold shadow
  rw [volume_wzCellShading (by positivity : 0 < 32/((2^m:ℕ):ℝ))]
  finiteness

lemma iUnion_parentIndex (Q : Finset Parent) (f : Parent → Set E4) :
    (⋃i : Fin Q.card,f (parentIndex Q i))=⋃p∈Q,f p := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨parentIndex Q i,parentIndex_mem Q i,hi⟩
  · rintro ⟨p,hp,hx⟩
    exact ⟨Q.equivFin ⟨p,hp⟩,by simpa only [parentIndex,Equiv.symm_apply_apply] using hx⟩

lemma full_union {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level m : ℕ)
    (E : Finset (Fin n × Index)) :
    sourceUnion (fullSource h R a level m E)=
      ⋃p∈R.image (parentLabel D a (2^m)),shadow D a level m (representative h R a (2^m)) E p := by
  rw [sourceUnion_eq_iUnion_shading_of_weights_one _ (fun _i => rfl)]
  simp only [full_shading]
  exact iUnion_parentIndex (R.image (parentLabel D a (2^m)))
    (shadow D a level m (representative h R a (2^m)) E)

lemma core_union {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (level m : ℕ) (Q : Finset Parent)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q)))) :
    sourceUnion (source h a level m Q rep E hsep)=⋃p∈Q,shadow D a level m rep E p := by
  rw [sourceUnion_eq_iUnion_shading_of_weights_one _ (fun _i => rfl)]
  simp only [source_shading]
  exact iUnion_parentIndex Q (shadow D a level m rep E)

lemma core_union_subset_full {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (level m : ℕ)
    (Q : Finset Parent) (hQ : Q⊆R.image (parentLabel D a (2^m))) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤
      dist (direction (D.line (representative h R a (2^m) p)))
        (direction (D.line (representative h R a (2^m) q)))) :
    sourceUnion (source h a level m Q (representative h R a (2^m)) E hsep)⊆
      sourceUnion (fullSource h R a level m E) := by
  rw [core_union,full_union]
  intro x hx
  obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hp,hx⟩ := Set.mem_iUnion.mp hp
  exact Set.mem_iUnion.mpr ⟨p,Set.mem_iUnion.mpr ⟨hQ hp,hx⟩⟩

lemma full_mass_ne_top {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level m : ℕ)
    (E : Finset (Fin n × Index)) : wzTotalShadingVolume (fullSource h R a level m E)≠⊤ := by
  unfold wzTotalShadingVolume
  apply ENNReal.sum_ne_top.mpr
  intro i _hi
  rw [full_shading]
  exact shadow_ne_top D a level m (representative h R a (2^m)) E _

lemma full_mass_real {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (level m : ℕ)
    (E : Finset (Fin n × Index)) :
    (wzTotalShadingVolume (fullSource h R a level m E)).toReal=
      ∑p∈R.image (parentLabel D a (2^m)),weight D a level m (representative h R a (2^m)) E p := by
  rw [wzTotalShadingVolume, ENNReal.toReal_sum]
  · simp only [full_shading]
    exact sum_parentIndex (R.image (parentLabel D a (2^m)))
      (weight D a level m (representative h R a (2^m)) E)
  · intro i _hi
    rw [full_shading]
    exact shadow_ne_top D a level m (representative h R a (2^m)) E _

/-- Original occupied-cell counts bound the TOTAL full coarse shadow mass,
including all cells excluded by a direction color. -/
theorem full_mass_upper {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (h6 : 6 ≤ m) (E : Finset (Fin n × Index)) (hE : ∀x∈E,x.2∈original x.1)
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ)) :
    (wzTotalShadingVolume (fullSource h R a level m E)).toReal ≤
      (373248*64^3*volumeConstant)*D.thickness^(-zeta) := by
  rw [full_mass_real]
  have hcount := NativeCoarsePruningBudget.original_occupied_count h R (2^m) (by positivity) H
  have hU : 0 ≤ volumeConstant*(64/((2^m:ℕ):ℝ))^3 := mul_nonneg volumeConstant_pos.le (by positivity)
  calc
    _ ≤ ∑_p∈R.image (parentLabel D a (2^m)),volumeConstant*(64/((2^m:ℕ):ℝ))^3 :=
      sum_le_sum (fun p _hp => actual_weight_upper h original horiginal ha level m hdy hm h6
        (representative h R a (2^m)) E hE p)
    _ = ((R.image (parentLabel D a (2^m))).card:ℝ)*(volumeConstant*(64/((2^m:ℕ):ℝ))^3) := by simp
    _ ≤ (373248*D.thickness^(-zeta)*((2^m:ℕ):ℝ)^3)*(volumeConstant*(64/((2^m:ℕ):ℝ))^3) :=
      mul_le_mul_of_nonneg_right hcount hU
    _ = _ := by field_simp

/-- The admitted core's upper multiplicity bounds the COMPLETE coarse shadow
on all original R. Thus scale-dependent cores do not require scale-dependent
replacement of the original fine family in the global upper-bound argument. -/
theorem full_multiplicity_le_core {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (h6 : 6 ≤ m) (E : Finset (Fin n × Index)) (hE : ∀x∈E,x.2∈original x.1)
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ))
    (Q : Finset Parent) (hQ : Q⊆R.image (parentLabel D a (2^m)))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤
      dist (direction (D.line (representative h R a (2^m) p)))
        (direction (D.line (representative h R a (2^m) q))))
    (hshade : D.thickness^(5*zeta) ≤
      ∑p∈Q,weight D a level m (representative h R a (2^m)) E p)
    (hcost : (373248*64^3*volumeConstant)*D.thickness^zeta ≤ 1) :
    (ENNReal.ofReal D.thickness).rpow (7*zeta)*NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level m E) ≤
      NativeFiniteKakeyaCounts.multiplicity
        (source h a level m Q (representative h R a (2^m)) E hsep) := by
  let S := source h a level m Q (representative h R a (2^m)) E hsep
  let F := fullSource h R a level m E
  have hd := h.1.2.1
  have hM : D.thickness^(7*zeta)*(wzTotalShadingVolume F).toReal ≤ (wzTotalShadingVolume S).toReal := by
    rw [source_total_shading_real]
    calc
      _ ≤ D.thickness^(7*zeta)*((373248*64^3*volumeConstant)*D.thickness^(-zeta)) :=
        mul_le_mul_of_nonneg_left (full_mass_upper h original horiginal ha R level m hdy hm h6 E hE H)
          (Real.rpow_pos_of_pos hd _).le
      _ = ((373248*64^3*volumeConstant)*D.thickness^zeta)*D.thickness^(5*zeta) := by
        rw [mul_left_comm,mul_assoc,←Real.rpow_add hd,show 7*zeta+(-zeta)=zeta+5*zeta by ring,Real.rpow_add hd]
        ring
      _ ≤ 1*D.thickness^(5*zeta) := mul_le_mul_of_nonneg_right hcost (Real.rpow_pos_of_pos hd _).le
      _ = D.thickness^(5*zeta) := one_mul _
      _ ≤ _ := hshade
  have hpT : (ENNReal.ofReal D.thickness).rpow (7*zeta)≠⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top
  have hMenn : (ENNReal.ofReal D.thickness).rpow (7*zeta)*wzTotalShadingVolume F ≤ wzTotalShadingVolume S := by
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hpT (full_mass_ne_top h R a level m E))
      (source_total_shading_ne_top (a:=a) h level m Q _ E hsep)).mp
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hd.le] using hM
  have hUnion : volume (sourceUnion S) ≤ volume (sourceUnion F) :=
    measure_mono (core_union_subset_full h R level m Q hQ E hsep)
  change (ENNReal.ofReal D.thickness).rpow (7*zeta)*(wzTotalShadingVolume F/volume (sourceUnion F)) ≤
    wzTotalShadingVolume S/volume (sourceUnion S)
  rw [←mul_div_assoc]
  exact ENNReal.div_le_div hMenn hUnion

end NativeFullCoarseShadow
