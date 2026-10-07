import Theorems.Thm_StickyKakeya4_native_local_parent_source_counts
import Theorems.Thm_StickyKakeya4_native_original_pruned_mass

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeActualLocalDensity
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeOriginalPrunedMass
open scoped ENNReal BigOperators

/-- Tube volume is bounded using the valid geometry of the actual source. -/
lemma total_tube_upper {n : ℕ} (S : FiniteScaleSource n)
    (heps : 0 < S.thickness) (heps1 : S.thickness ≤ 1)
    (hvalid : ∀i,IsValidLine (S.line i)) :
    wzTotalTubeVolume S ≤ n * (ENNReal.ofReal volumeConstant *
      (ENNReal.ofReal S.thickness)^3) := by
  unfold wzTotalTubeVolume
  calc
    _ ≤ ∑_i : Fin n, ENNReal.ofReal volumeConstant * (ENNReal.ofReal S.thickness)^3 := by
      apply sum_le_sum
      intro i _hi
      have ht := volume_markedUnitTube_upper_bound (hvalid i) heps heps1
      calc
        _ ≤ 32*(ENNReal.ofReal S.thickness)^3*ENNReal.ofReal (Real.pi^2/2) := ht
        _ = _ := by
          rw [volumeConstant,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 32),ENNReal.ofReal_ofNat]
          ring
    _ = _ := by simp

/-- The original selected-parent density and scalar budget imply density
for the genuine new cubical shading on the full original parent backbone. -/
theorem source_density {n : ℕ} {D : FiniteScaleSource n} {eta zeta a e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (level m : ℕ) (hdy : D.thickness = (2:ℝ)⁻¹^level) (hm : m ≤ level) (p : Parent)
    (hQ : ∀z∈E,z.1 ∈ parentLabels D R a (2^m) p)
    (F Qrad : ℝ) (hF : 0 < F) (hQrad : 0 < Qrad)
    (hparent : D.thickness^(eta+2*zeta) * (parentLabels D R a (2^m) p).card ≤
      D.thickness * F * Qrad^2 * E.card)
    (hbudget : (1024*175616*volumeConstant) * F * Qrad^2 *
      (((2^m:ℕ):ℝ)*D.thickness/64)^e ≤ D.thickness^(eta+2*zeta)) :
    (ENNReal.ofReal (source h R E a m p).thickness).rpow e *
      wzTotalTubeVolume (source h R E a m p) ≤
        wzTotalShadingVolume (source h R E a m p) := by
  let S := source h R E a m p
  let Q := parentLabels D R a (2^m) p
  let eps := S.thickness
  have hd := h.1.2.1
  have hg := source_geometric_fields h original horiginal ha R E hE level m hdy hm p
  have heps : 0 < eps := hg.1
  have ht := total_tube_upper S heps hg.2.1 hg.2.2.2.1
  have htn : wzTotalTubeVolume S ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) ht
  have htr : (wzTotalTubeVolume S).toReal ≤ (Q.card:ℝ)*volumeConstant*eps^3 := by
    have hr := ENNReal.toReal_mono (by finiteness) ht
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofReal volumeConstant_pos.le,ENNReal.toReal_ofReal (show 0 ≤ S.thickness from heps.le),
      mul_assoc] using hr
  have hsn : wzTotalShadingVolume S ≠ ⊤ := by
    unfold wzTotalShadingVolume
    apply ENNReal.sum_ne_top.mpr
    intro i _hi
    change volume (wzCellShading (((2^m:ℕ):ℝ)*D.thickness/128)
      (sourceCells D R E a (2^m) p) i) ≠ ⊤
    rw [volume_wzCellShading (by positivity : 0 < ((2^m:ℕ):ℝ)*D.thickness/128)]
    finiteness
  have hmass := selected_parent_mass_le_source h original horiginal ha R E hE m p
  rw [selected_parent_real_shading_eq_card D hd E Q hQ] at hmass
  have hscalar : (1024*175616*volumeConstant)*eps^e*(Q.card:ℝ) ≤
      D.thickness*(E.card:ℝ) := by
    apply (mul_le_mul_iff_right₀ (mul_pos hF (sq_pos_of_pos hQrad))).mp
    have hb := (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg Q.card)).trans hparent
    convert hb using 1 <;> (try simp only [eps,S,source_thickness]) <;> ring
  have hscaled : (175616*64^4:ℝ)*(eps^e*((Q.card:ℝ)*volumeConstant*eps^3)) ≤
      ((2^m:ℕ):ℝ)^3*((E.card:ℝ)*(mesh D)^4) := by
    have hh := mul_le_mul_of_nonneg_right hscalar
      (show 0 ≤ ((2^m:ℕ):ℝ)^3*D.thickness^3/16 by positivity)
    calc
      _ = ((1024*175616*volumeConstant)*eps^e*(Q.card:ℝ)) *
          (((2^m:ℕ):ℝ)^3*D.thickness^3/16) := by
        simp only [eps,S,source_thickness]
        ring
      _ ≤ (D.thickness*(E.card:ℝ)) *
          (((2^m:ℕ):ℝ)^3*D.thickness^3/16) := hh
      _ = _ := by dsimp [mesh]; ring
  have hreal : eps^e*(wzTotalTubeVolume S).toReal ≤ (wzTotalShadingVolume S).toReal := by
    have hu := mul_le_mul_of_nonneg_left htr (Real.rpow_pos_of_pos heps e).le
    have hh := (mul_le_mul_of_nonneg_left hu
      (by norm_num : (0:ℝ) ≤ 175616*64^4)).trans (hscaled.trans hmass)
    exact (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ) < 175616*64^4)).mp hh
  have hn : (ENNReal.ofReal eps).rpow e * wzTotalTubeVolume S ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · rw [ENNReal.rpow_eq_pow,ENNReal.ofReal_rpow_of_pos heps]
      finiteness
    · exact htn
  apply (ENNReal.toReal_le_toReal hn hsn).mp
  simpa only [ENNReal.toReal_mul,ENNReal.rpow_eq_pow,ENNReal.ofReal_rpow_of_pos heps,
    ENNReal.toReal_ofReal (Real.rpow_pos_of_pos heps e).le] using hreal

end NativeActualLocalDensity
