/- UNVERIFIED fixed-source multiplicity reader. Its premises are actual
shading/union bounds and the remaining scalar payment, not a desired near
multiplicity conclusion. It will be joined to the deterministic Reference
constructor without choosing another source. -/
import Theorems.Thm_StickyKakeya4_native_fixed_compact_multiplicity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeFixedSourceReference
open Classical Finset MeasureTheory StickyKakeya4 NativeFiniteKakeyaCounts
open NativeFixedCompactKakeyaExponent
open scoped ENNReal

/-- Positive actual shading and a finite actual union imply genuine finite,
positive denominator. These are proved before converting multiplicity toReal. -/
theorem union_pos_of_shading_lower {n : ℕ} {D : FiniteScaleSource n} {eta L : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hL : 0<L)
    (hshade : ENNReal.ofReal L≤wzTotalShadingVolume D) :
    0<volume (sourceUnion D) := by
  have hW : ∀i,D.weight i=1 := h.1.2.2.2.2.2.1
  have htotal := total_shading_le_card_mul_union D hW
  by_contra hnot
  have hz : volume (sourceUnion D)=0 := le_antisymm (le_of_not_gt hnot) (zero_le _)
  rw [hz,mul_zero] at htotal
  have hbad : ENNReal.ofReal L≤0 := hshade.trans htotal
  exact (ENNReal.ofReal_pos.mpr hL).not_le hbad

/-- The same source's actual count-derived shading lower and actual union
upper give its near-extremal multiplicity. U can be the literal remembered
unionConstant(KXY), and L the remembered relation's exact shading lower. -/
theorem native_near_of_volume_bounds {n : ℕ} {D : FiniteScaleSource n} {eta L U : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hU : 0<U)
    (hshade : ENNReal.ofReal L≤wzTotalShadingVolume D)
    (hunion : volume (sourceUnion D)≤ENNReal.ofReal (U*D.thickness^extremalExponent))
    (hpaid : U*D.thickness^eta≤L) :
    D.thickness^(-extremalExponent+eta)≤(multiplicity D).toReal := by
  have hd : 0<D.thickness := h.1.2.1
  have hL : 0<L := (mul_pos hU (Real.rpow_pos_of_pos hd eta)).trans_le hpaid
  have hUnionPos := union_pos_of_shading_lower h hL hshade
  have hUnionTop : volume (sourceUnion D)≠⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hunion
  have hShadeTop : wzTotalShadingVolume D≠⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (NativeFixedCompactMultiplicity.total_shading_upper h)
  have hden : 0<(volume (sourceUnion D)).toReal := ENNReal.toReal_pos hUnionPos.ne' hUnionTop
  have hlo : L≤(wzTotalShadingVolume D).toReal := by
    have hh := ENNReal.toReal_mono hShadeTop hshade
    simpa only [ENNReal.toReal_ofReal hL.le] using hh
  have hup : (volume (sourceUnion D)).toReal≤U*D.thickness^extremalExponent := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hunion
    simpa only [ENNReal.toReal_ofReal (mul_pos hU (Real.rpow_pos_of_pos hd _)).le] using hh
  have hpower : D.thickness^(-extremalExponent+eta)*(U*D.thickness^extremalExponent)=
      U*D.thickness^eta := by
    calc
      _ = U*(D.thickness^(-extremalExponent+eta)*D.thickness^extremalExponent) := by ring
      _ = U*D.thickness^((-extremalExponent+eta)+extremalExponent) := by rw [←Real.rpow_add hd]
      _ = U*D.thickness^eta := by congr 2; ring
  have hprod : D.thickness^(-extremalExponent+eta)*(volume (sourceUnion D)).toReal≤
      (wzTotalShadingVolume D).toReal := by
    calc
      _ ≤ D.thickness^(-extremalExponent+eta)*(U*D.thickness^extremalExponent) :=
        mul_le_mul_of_nonneg_left hup (Real.rpow_nonneg hd.le _)
      _ = U*D.thickness^eta := hpower
      _ ≤ L := hpaid
      _ ≤ _ := hlo
  rw [multiplicity,ENNReal.toReal_div]
  exact (le_div_iff₀ hden).mpr hprod

end NativeFixedSourceReference
