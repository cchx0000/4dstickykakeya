/- NEW SOURCE, 2026-10-06. UNVERIFIED: awaiting the parent-controlled Lean queue.
The full coarse reference family is not asserted to be direction-separated
or to satisfy IsWangZakharovNativeFiniteInput. -/
import Theorems.Thm_StickyKakeya4_native_coarse_ancestor_counts
import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeFullReferenceCoarseCW
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeDyadicParentCells NativeCoarseAncestorCounts
open NativeFullCoarseShadow NativeCoarseCellSource NativeCoarseDirectionThinning
open NativeCoarseCWTransfer NativeCoarseShadingPruning NativeUnitParentNormalization
open scoped BigOperators ENNReal

/-- A single occupied depth-zero ancestor gives a lower count for the FULL
coarse parameter image. The selected shading has no role in this bound. -/
theorem full_parent_card_lower {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (hR : R.Nonempty) (level b : ℕ) (hb : b ≤ level)
    (H : ∀j : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^j.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3) :
    D.thickness^(2*zeta)*((2^b:ℕ):ℝ)^3 ≤ (R.image (parentLabel D a (2^b))).card := by
  obtain ⟨q,hq⟩ := hR.image (parentLabel D a (2^b))
  have hne : (descendants D R a b 0 (ancestor b 0 q)).Nonempty :=
    ⟨q,mem_filter.mpr ⟨hq,rfl⟩⟩
  have hlo := (coarse_ancestor_AD h R a zeta level H (Nat.zero_le b) hb
    (ancestor b 0 q) hne).1
  have hsub : descendants D R a b 0 (ancestor b 0 q) ⊆ R.image (parentLabel D a (2^b)) :=
    filter_subset _ _
  have hc : ((descendants D R a b 0 (ancestor b 0 q)).card:ℝ) ≤
      (R.image (parentLabel D a (2^b))).card := by exact_mod_cast card_le_card hsub
  have hlo' : D.thickness^(2*zeta)*((2^b:ℕ):ℝ)^3 ≤
      ((descendants D R a b 0 (ancestor b 0 q)).card:ℝ) := by
    simpa only [pow_zero,Nat.cast_one,div_one] using hlo
  exact hlo'.trans hc

/-- Literal contained-tube counts on the complete coarse source. This does
not use the separated-core constructor or a separation hypothesis. -/
lemma full_contained_count {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index)) (U : Set E4) :
    wzContainedTubeCount (fullSource h R a level b E) U=
      ((R.image (parentLabel D a (2^b))).filter (fun p =>
        markedUnitTube (NativeContractedUnitParent.line D a (0,0)
          (representative h R a (2^b) p)) (64/((2^b:ℕ):ℝ)) ⊆ U)).card := by
  exact NativeCoarseSourceProfiles.card_filter_parentIndex
    (R.image (parentLabel D a (2^b))) (fun p =>
      markedUnitTube (NativeContractedUnitParent.line D a (0,0)
        (representative h R a (2^b) p)) (64/((2^b:ℕ):ℝ)) ⊆ U)

/-- Relative CW on the FULL reference family, normalized using its actual
ancestor population. Its coefficient contains no selected-shading or q cost. -/
theorem full_CW_real {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (hR : R.Nonempty) (level b : ℕ) (hb : b ≤ level)
    (hscale : ((2^b:ℕ):ℝ)*D.thickness ≤ 1)
    (H : ∀j : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^j.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3)
    (E : Finset (Fin n × Index)) (U : Set E4) (hU : Convex ℝ U) (hfin : volume U≠⊤) :
    (wzContainedTubeCount (fullSource h R a level b E) U:ℝ) ≤
      (373248*512^4:ℝ)*D.thickness^(-eta-3*zeta)*(volume U).toReal*
        (R.image (parentLabel D a (2^b))).card := by
  let P := R.image (parentLabel D a (2^b))
  have hd := h.1.2.1
  have hpop := full_parent_card_lower h R hR level b hb H
  have hcount : ((2^b:ℕ):ℝ)^3 ≤ D.thickness^(-2*zeta)*(P.card:ℝ) := by
    have hp : 0 < D.thickness^(2*zeta) := Real.rpow_pos_of_pos hd _
    have hh : ((2^b:ℕ):ℝ)^3 ≤ (P.card:ℝ)/D.thickness^(2*zeta) :=
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm,P] using hpop)
    rw [show -2*zeta=-(2*zeta) by ring,Real.rpow_neg hd.le]
    simpa only [div_eq_mul_inv,mul_comm,P] using hh
  have hcw := original_coarse_CW_real h ha R (2^b) (by positivity) hscale P
    (subset_refl P) (representative h R a (2^b))
    (fun p hp => (representative_spec h R a (2^b) hp).2)
    (fun p hp => by
      obtain ⟨i,hi,hip⟩ := mem_image.mp hp
      exact (H ⟨b,by omega⟩ p ⟨i,mem_filter.mpr ⟨hi,hip⟩⟩).1) U hU hfin
  rw [full_contained_count]
  calc
    _ ≤ (373248*512^4:ℝ)*D.thickness^(-eta-zeta)*((2^b:ℕ):ℝ)^3*(volume U).toReal := hcw
    _ ≤ (373248*512^4:ℝ)*D.thickness^(-eta-zeta)*
        (D.thickness^(-2*zeta)*(P.card:ℝ))*(volume U).toReal :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount (by positivity)) ENNReal.toReal_nonneg
    _ = _ := by
      have hp : D.thickness^(-eta-zeta)*D.thickness^(-2*zeta)=D.thickness^(-eta-3*zeta) := by
        rw [←Real.rpow_add hd]
        congr 1
        ring
      calc
        _ = (373248*512^4:ℝ)*(D.thickness^(-eta-zeta)*D.thickness^(-2*zeta))*
            (volume U).toReal*(P.card:ℝ) := by ring
        _ = _ := by rw [hp]

/-- The same full-family CW inequality includes convex sets of infinite
volume, as required by the native interface's CW field. -/
theorem full_CW {n : ℕ} {D : FiniteScaleSource n} {eta a zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (hR : R.Nonempty) (level b : ℕ) (hb : b ≤ level)
    (hscale : ((2^b:ℕ):ℝ)*D.thickness ≤ 1)
    (H : ∀j : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^j.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^j.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^j.val:ℕ):ℝ))/D.thickness)^3)
    (E : Finset (Fin n × Index)) (U : Set E4) (hU : Convex ℝ U) :
    (wzContainedTubeCount (fullSource h R a level b E) U:ℝ≥0∞) ≤
      (373248*512^4:ℝ≥0∞)*(ENNReal.ofReal D.thickness).rpow (-eta-3*zeta)*volume U*
        (R.image (parentLabel D a (2^b))).card := by
  have hd := h.1.2.1
  have hp0 : (ENNReal.ofReal D.thickness).rpow (-eta-3*zeta)≠0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hd) ENNReal.ofReal_ne_top).ne'
  have hpT : (ENNReal.ofReal D.thickness).rpow (-eta-3*zeta)≠⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top
  by_cases hfin : volume U=⊤
  · have hn : ((R.image (parentLabel D a (2^b))).card:ℝ≥0∞)≠0 := by
      exact_mod_cast (card_pos.mpr (hR.image (parentLabel D a (2^b)))).ne'
    have hc : (373248*512^4:ℝ≥0∞)*(ENNReal.ofReal D.thickness).rpow (-eta-3*zeta)≠0 :=
      mul_ne_zero (by norm_num) hp0
    simp only [hfin,ENNReal.mul_top hc,ENNReal.top_mul hn,le_top]
  · have hright : (373248*512^4:ℝ≥0∞)*(ENNReal.ofReal D.thickness).rpow (-eta-3*zeta)*volume U*
        (R.image (parentLabel D a (2^b))).card≠⊤ := by finiteness
    apply (ENNReal.toReal_le_toReal (by simp) hright).mp
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofNat,ENNReal.toReal_natCast,←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hd.le] using full_CW_real h ha R hR level b hb hscale H E U hU hfin

/-- The genuine sparse shading stays an exact independent field of the same
full source; the preceding CW bounds never use its mass as a denominator. -/
theorem full_shading_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index)) :
    (wzTotalShadingVolume (fullSource h R a level b E)).toReal=
      ∑p∈R.image (parentLabel D a (2^b)),weight D a level b (representative h R a (2^b)) E p :=
  full_mass_real h R a level b E

end NativeFullReferenceCoarseCW
