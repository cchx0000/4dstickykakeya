/- Actual variable retention inside one admitted reference source.
No native admission for the sparse current shading is assumed or proved. -/
import Theorems.Thm_StickyKakeya4_native_actual_local_density

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeCurrentReferenceIncidenceRetention
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeActualLocalDensity NativeOriginalPrunedMass
open scoped ENNReal BigOperators

lemma source_cells_real_volume {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) :
    (wzTotalShadingVolume (source h R E a m p)).toReal =
      ((incidences (sourceCells D R E a (2^m) p)).card : ℝ) *
        ((((2^m : ℕ) : ℝ) * D.thickness / 128)^4) := by
  have hm : 0 < (((2^m : ℕ) : ℝ) * D.thickness / 128) := by
    have hd := h.1.2.1
    positivity
  rw [total_shading_eq_incidence_volume (source h R E a m p) hm
    (sourceCells D R E a (2^m) p) (source_shading h R E a m p)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hm.le]

/-- The old parent average and the ACTUAL total retention cost give a
literal sourceCells retention factor. The admitted source remains Eref;
T supplies only a sparse shading on its same full parent tube index set. -/
theorem retained_incidence_ratio {n : ℕ} {D : FiniteScaleSource n}
    {eta etaRef a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈ Set.Icc (-(1/2 : ℝ)) (1/2 : ℝ))
    (R : Finset (Fin n)) (Eref H T : Finset (Fin n × Index))
    (m : ℕ) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) etaRef)
    (hT : T ⊆ incidences original)
    (hQ : ∀ z ∈ T, z.1 ∈ parentLabels D R a (2^m) p)
    (population C : ℝ) (hpopulation : 0 < population) (hC : 0 < C)
    (hparent : population * (parentLabels D R a (2^m) p).card ≤ D.thickness * H.card)
    (hretain : (H.card : ℝ) ≤ C * T.card) :
    let Iref := incidences (sourceCells D R Eref a (2^m) p)
    let IT := incidences (sourceCells D R T a (2^m) p)
    population * (Iref.card : ℝ) ≤ (1024*175616*volumeConstant) * C * IT.card ∧
      (Iref.card : ℝ) ≤ ((1024*175616*volumeConstant) * C / population) * IT.card := by
  intro Iref IT
  let Sref := source h R Eref a m p
  let ST := source h R T a m p
  let Q := parentLabels D R a (2^m) p
  let eps : ℝ := ((2^m : ℕ) : ℝ) * D.thickness / 64
  have hd := h.1.2.1
  have Href : IsWangZakharovFiniteInput Sref etaRef := hReferenceNative.1
  rcases Href with ⟨_hn, heps, heps1, _hdy, hvalid, _hw, _hmeas, _hcub, hsub,
    _hsep, _had, _hcw, _hden⟩
  have ht := total_tube_upper Sref heps heps1 hvalid
  have hrefE : wzTotalShadingVolume Sref ≤
      Q.card * (ENNReal.ofReal volumeConstant * (ENNReal.ofReal eps)^3) := by
    calc
      _ ≤ wzTotalTubeVolume Sref := by
        unfold wzTotalShadingVolume wzTotalTubeVolume
        exact sum_le_sum (fun i _ => measure_mono (hsub i))
      _ ≤ _ := ht
  have href : (wzTotalShadingVolume Sref).toReal ≤ (Q.card : ℝ) * volumeConstant * eps^3 := by
    have hh := ENNReal.toReal_mono (by finiteness) hrefE
    have heps' : 0 ≤ eps := by dsimp only [eps]; positivity
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal volumeConstant_pos.le, ENNReal.toReal_ofReal heps', mul_assoc] using hh
  have hmass := selected_parent_mass_le_source h original horiginal ha R T hT m p
  rw [selected_parent_real_shading_eq_card D hd T Q hQ] at hmass
  have hpar : population * (Q.card : ℝ) ≤ D.thickness * C * T.card :=
    hparent.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hretain hd.le)
  have hselected : population * (Q.card : ℝ) * eps^3 ≤
      (1024*175616 : ℝ) * C * (wzTotalShadingVolume ST).toReal := by
    apply (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 64^3/16)).mp
    calc
      _ = (population * (Q.card : ℝ)) *
          ((((2^m : ℕ) : ℝ)^3 * D.thickness^3) / 16) := by dsimp only [eps]; ring
      _ ≤ (D.thickness * C * T.card) *
          ((((2^m : ℕ) : ℝ)^3 * D.thickness^3) / 16) :=
        mul_le_mul_of_nonneg_right hpar (by positivity)
      _ = C * (((2^m : ℕ) : ℝ)^3 * ((T.card : ℝ) * (mesh D)^4)) := by
        dsimp only [mesh]
        ring
      _ ≤ C * ((175616*64^4 : ℝ) * (wzTotalShadingVolume ST).toReal) :=
        mul_le_mul_of_nonneg_left hmass hC.le
      _ = _ := by ring
  have hvol : population * (wzTotalShadingVolume Sref).toReal ≤
      (1024*175616*volumeConstant) * C * (wzTotalShadingVolume ST).toReal := by
    calc
      _ ≤ population * ((Q.card : ℝ) * volumeConstant * eps^3) :=
        mul_le_mul_of_nonneg_left href hpopulation.le
      _ = volumeConstant * (population * (Q.card : ℝ) * eps^3) := by ring
      _ ≤ volumeConstant * ((1024*175616 : ℝ) * C * (wzTotalShadingVolume ST).toReal) :=
        mul_le_mul_of_nonneg_left hselected volumeConstant_pos.le
      _ = _ := by ring
  have hcount : population * (Iref.card : ℝ) ≤ (1024*175616*volumeConstant) * C * IT.card := by
    change population * (wzTotalShadingVolume (source h R Eref a m p)).toReal ≤
      (1024*175616*volumeConstant) * C * (wzTotalShadingVolume (source h R T a m p)).toReal at hvol
    rw [source_cells_real_volume, source_cells_real_volume] at hvol
    have hmesh : 0 < ((((2^m : ℕ) : ℝ) * D.thickness / 128)^4) := by positivity
    apply (mul_le_mul_iff_right₀ hmesh).mp
    simpa only [Iref, IT, mul_assoc, mul_left_comm, mul_comm] using hvol
  refine ⟨hcount, ?_⟩
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpopulation).mpr
  simpa only [mul_comm] using hcount

end NativeCurrentReferenceIncidenceRetention
