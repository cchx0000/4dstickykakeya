import Theorems.Thm_StickyKakeya4_native_local_parent_source

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeOriginalShadingRestriction
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeLocalParentSource
open scoped ENNReal BigOperators

/-- Restrict only the literal original cells. Every original line, empty row,
weight, mark and carrier-tree label is retained. -/
def source {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index)) :
    FiniteScaleSource n :=
  { D with shading := wzCellShading (mesh D) (selectedCells E) }

lemma shading_subset {n : ℕ} (D : FiniteScaleSource n)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original) (i : Fin n) :
    (source D E).shading i ⊆ D.shading i := by
  rw [horiginal]
  intro x hx
  simp only [source, wzCellShading, Set.mem_iUnion, mem_coe] at hx ⊢
  obtain ⟨k,hk,hx⟩ := hx
  exact ⟨k,selectedCells_subset original E hE i hk,hx⟩

lemma total_shading {n : ℕ} (D : FiniteScaleSource n) (hd : 0 < D.thickness)
    (E : Finset (Fin n × Index)) :
    wzTotalShadingVolume (source D E) = E.card * (ENNReal.ofReal (mesh D))^4 := by
  simpa only [selected_incidences, mesh] using
    total_shading_eq_incidence_volume (source D E) (half_pos hd) (selectedCells E)
      (fun _ => rfl)

lemma union_subset {n : ℕ} (D : FiniteScaleSource n) (hw : ∀ i, D.weight i = 1)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original) :
    sourceUnion (source D E) ⊆ sourceUnion D := by
  rw [sourceUnion_eq_iUnion_shading_of_weights_one D hw,
    sourceUnion_eq_iUnion_shading_of_weights_one (source D E) hw]
  exact Set.iUnion_mono (shading_subset D original horiginal E hE)

/-- Finite incidence retention is exactly the corresponding shading-volume
retention, since the original half-thickness mesh is unchanged. -/
theorem mass_retention {n : ℕ} (D : FiniteScaleSource n) (hd : 0 < D.thickness)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (E : Finset (Fin n × Index)) (loss : ℝ)
    (hret : D.thickness^loss * ((incidences original).card : ℝ) ≤ E.card) :
    (ENNReal.ofReal D.thickness).rpow loss * wzTotalShadingVolume D ≤
      wzTotalShadingVolume (source D E) := by
  have hc : (ENNReal.ofReal D.thickness).rpow loss * (incidences original).card ≤
      (E.card : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hd loss).le,
      ENNReal.ofReal_rpow_of_pos hd, ENNReal.ofReal_natCast, ENNReal.rpow_eq_pow] using
      ENNReal.ofReal_le_ofReal hret
  rw [total_shading D hd E,
    total_shading_eq_incidence_volume D (half_pos hd) original horiginal, ← mul_assoc]
  exact mul_le_mul' hc le_rfl

/-- A genuine retained original shading remains a native input on the same
entire tube backbone. Only its proved global retention exponent is paid. -/
theorem native_input {n : ℕ} {D : FiniteScaleSource n} {eta loss : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hloss : 0 ≤ loss)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (hret : D.thickness^loss * ((incidences original).card : ℝ) ≤ E.card) :
    IsWangZakharovNativeFiniteInput (source D E) (eta+loss) := by
  have hden := h.1.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨hn,hd,hd1,hdy,hv,hw,_hm,_hcub,hsub,hsep,hAD,hCW,_hden⟩,hg,hnrm⟩ :=
    NativeFiniteKakeyaCounts.input_mono h (by linarith : eta ≤ eta+loss)
  refine ⟨⟨hn,hd,hd1,hdy,hv,hw,?_,?_,?_,hsep,hAD,hCW,?_⟩,hg,hnrm⟩
  · exact fun i => measurableSet_wzCellShading _ (selectedCells E) i
  · intro i
    have hhalf : IsWZDyadicScale (mesh D) := by
      obtain ⟨level,hlevel⟩ := hdy
      refine ⟨level+1,?_⟩
      change D.thickness/2 = (2:ℝ)⁻¹^(level+1)
      rw [hlevel,pow_succ]
      ring
    refine ⟨mesh D,half_pos hd,?_,?_,hhalf,?_⟩
    · change D.thickness/2 ≤ D.thickness
      linarith
    · change D.thickness ≤ 2*(D.thickness/2)
      linarith
    · exact isWZCubicalShading_wzCellShading _ (selectedCells E) i
  · exact fun i => (shading_subset D original horiginal E hE i).trans (hsub i)
  · have he0 : ENNReal.ofReal D.thickness ≠ 0 := by positivity
    have heT : ENNReal.ofReal D.thickness ≠ ⊤ := ENNReal.ofReal_ne_top
    change (ENNReal.ofReal D.thickness).rpow (eta+loss) * wzTotalTubeVolume D ≤ _
    calc
      _ = (ENNReal.ofReal D.thickness).rpow loss *
          ((ENNReal.ofReal D.thickness).rpow eta * wzTotalTubeVolume D) := by
        simp only [ENNReal.rpow_eq_pow]
        rw [ENNReal.rpow_add _ _ he0 heT]
        ring
      _ ≤ (ENNReal.ofReal D.thickness).rpow loss * wzTotalShadingVolume D :=
        mul_le_mul' le_rfl hden
      _ ≤ _ := mass_retention D hd original horiginal E loss hret

/-- Actual average multiplicity retains the proved original incidence fraction;
no monotonicity of averages under arbitrary deletion is asserted. -/
theorem multiplicity_retention {n : ℕ} {D : FiniteScaleSource n} {eta loss : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (hret : D.thickness^loss * ((incidences original).card : ℝ) ≤ E.card) :
    (ENNReal.ofReal D.thickness).rpow loss * NativeFiniteKakeyaCounts.multiplicity D ≤
      NativeFiniteKakeyaCounts.multiplicity (source D E) := by
  unfold NativeFiniteKakeyaCounts.multiplicity
  rw [← mul_div_assoc]
  exact ENNReal.div_le_div (mass_retention D h.1.2.1 original horiginal E loss hret)
    (measure_mono (union_subset D h.1.2.2.2.2.2.1 original horiginal E hE))

end NativeOriginalShadingRestriction
