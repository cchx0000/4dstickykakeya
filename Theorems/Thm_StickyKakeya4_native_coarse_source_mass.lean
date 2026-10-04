import Theorems.Thm_StickyKakeya4_native_coarse_source_profiles
import Theorems.Thm_StickyKakeya4_native_coarse_mass_budget
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
noncomputable section
namespace NativeCoarseSourceMass
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseCellSource NativeCoarseRepresentativeGeometry
open NativeCoarseSourceProfiles NativeCoarseShadingPruning NativeOriginalPrunedMass
open scoped BigOperators ENNReal

variable {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
variable (h : IsWangZakharovNativeFiniteInput D eta) (level m : ℕ)
variable (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
variable (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q))))

lemma source_shading_ne_top (i : Fin Q.card) :
    volume ((source h a level m Q rep E hsep).shading i)≠⊤ := by
  rw [source_shading,volume_wzCellShading (by positivity : 0 < 32/((2^m:ℕ):ℝ))]
  finiteness

lemma source_total_shading_real :
    (wzTotalShadingVolume (source h a level m Q rep E hsep)).toReal=
      ∑p∈Q,weight D a level m rep E p := by
  rw [wzTotalShadingVolume,ENNReal.toReal_sum (fun i _hi => source_shading_ne_top h level m Q rep E hsep i)]
  exact source_shading_sum h level m Q rep E hsep

lemma source_total_shading_ne_top : wzTotalShadingVolume (source h a level m Q rep E hsep)≠⊤ :=
  ENNReal.sum_ne_top.mpr (fun i _hi => source_shading_ne_top h level m Q rep E hsep i)

lemma source_tube_real_upper (h6 : 6 ≤ m) (i : Fin Q.card) :
    (volume (markedUnitTube ((source h a level m Q rep E hsep).line i)
      (source h a level m Q rep E hsep).thickness)).toReal ≤ volumeConstant*(64/((2^m:ℕ):ℝ))^3 := by
  have hh := volume_markedUnitTube_upper_bound (zero_parent_valid_slab h a (rep (parentIndex Q i))).1
    (by positivity : 0 < 64/((2^m:ℕ):ℝ)) (coarse_thickness_le_one m h6)
  have hr := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 64/((2^m:ℕ):ℝ)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi^2/2)] at hr
  exact hr.trans_eq (by dsimp [volumeConstant]; ring)

lemma source_tube_ne_top (h6 : 6 ≤ m) (i : Fin Q.card) :
    volume (markedUnitTube ((source h a level m Q rep E hsep).line i)
      (source h a level m Q rep E hsep).thickness)≠⊤ := by
  exact ne_top_of_le_ne_top (by finiteness)
    (volume_markedUnitTube_upper_bound (zero_parent_valid_slab h a (rep (parentIndex Q i))).1
      (by positivity : 0 < 64/((2^m:ℕ):ℝ)) (coarse_thickness_le_one m h6))

lemma source_tube_mass_ne_top (h6 : 6 ≤ m) :
    wzTotalTubeVolume (source h a level m Q rep E hsep)≠⊤ :=
  ENNReal.sum_ne_top.mpr (fun i _hi => source_tube_ne_top h level m Q rep E hsep h6 i)

lemma source_tube_mass_real_upper (h6 : 6 ≤ m) :
    (wzTotalTubeVolume (source h a level m Q rep E hsep)).toReal ≤
      (Q.card:ℝ)*(volumeConstant*(64/((2^m:ℕ):ℝ))^3) := by
  rw [wzTotalTubeVolume,ENNReal.toReal_sum (fun i _hi => source_tube_ne_top h level m Q rep E hsep h6 i)]
  calc
    _ ≤ ∑_i : Fin Q.card,volumeConstant*(64/((2^m:ℕ):ℝ))^3 :=
      sum_le_sum (fun i _hi => source_tube_real_upper h level m Q rep E hsep h6 i)
    _ = _ := by simp

/-- The actual coarse tube mass is controlled by the complete original
occupied-cell count. Original-direction packing and cell lower population
supply that count; no relative coarse density has been assumed. -/
theorem source_tube_mass_original_bound (h6 : 6 ≤ m) {zeta : ℝ}
    (R : Finset (Fin n)) (hQ : Q⊆R.image (parentLabel D a (2^m)))
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ)) :
    (wzTotalTubeVolume (source h a level m Q rep E hsep)).toReal ≤
      (373248*64^3*volumeConstant)*D.thickness^(-zeta) := by
  have hcount : (Q.card:ℝ) ≤ 373248*D.thickness^(-zeta)*((2^m:ℕ):ℝ)^3 :=
    (show (Q.card:ℝ) ≤ (R.image (parentLabel D a (2^m))).card by exact_mod_cast card_le_card hQ).trans
      (NativeCoarsePruningBudget.original_occupied_count h R (2^m) (by positivity) H)
  have hU : 0 ≤ volumeConstant*(64/((2^m:ℕ):ℝ))^3 := mul_nonneg volumeConstant_pos.le (by positivity)
  calc
    _ ≤ (Q.card:ℝ)*(volumeConstant*(64/((2^m:ℕ):ℝ))^3) := source_tube_mass_real_upper h level m Q rep E hsep h6
    _ ≤ (373248*D.thickness^(-zeta)*((2^m:ℕ):ℝ)^3)*(volumeConstant*(64/((2^m:ℕ):ℝ))^3) :=
      mul_le_mul_of_nonneg_right hcount hU
    _ = _ := by field_simp

/-- Aggregate density follows from the actual retained coarse shading lower
mass and the proved total tube upper mass, with the original-delta cost. -/
theorem source_density_original_power (h6 : 6 ≤ m) {zeta : ℝ}
    (R : Finset (Fin n)) (hQ : Q⊆R.image (parentLabel D a (2^m)))
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ))
    (hshade : D.thickness^(5*zeta) ≤ ∑p∈Q,weight D a level m rep E p)
    (hcost : (373248*64^3*volumeConstant)*D.thickness^zeta ≤ 1) :
    D.thickness^(7*zeta)*(wzTotalTubeVolume (source h a level m Q rep E hsep)).toReal ≤
      (wzTotalShadingVolume (source h a level m Q rep E hsep)).toReal := by
  have hd := h.1.2.1
  rw [source_total_shading_real]
  calc
    _ ≤ D.thickness^(7*zeta)*((373248*64^3*volumeConstant)*D.thickness^(-zeta)) :=
      mul_le_mul_of_nonneg_left (source_tube_mass_original_bound h level m Q rep E hsep h6 R hQ H)
        (Real.rpow_pos_of_pos hd _).le
    _ = ((373248*64^3*volumeConstant)*D.thickness^zeta)*D.thickness^(5*zeta) := by
      rw [mul_left_comm,mul_assoc,←Real.rpow_add hd,show 7*zeta+(-zeta)=zeta+5*zeta by ring,Real.rpow_add hd]
      ring
    _ ≤ 1*D.thickness^(5*zeta) := mul_le_mul_of_nonneg_right hcost (Real.rpow_pos_of_pos hd _).le
    _ = D.thickness^(5*zeta) := one_mul _
    _ ≤ _ := hshade

end NativeCoarseSourceMass
