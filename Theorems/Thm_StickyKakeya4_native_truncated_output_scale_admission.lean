import Theorems.Thm_StickyKakeya4_native_truncated_retention_coarse_selection
import Theorems.Thm_StickyKakeya4_native_effective_output_threshold
import Theorems.Thm_StickyKakeya4_native_full_coarse_shadow

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeTruncatedOutputScaleAdmission
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeUnitParentNormalization NativeCoarseDirectionThinning
open NativeCoarseCellSource NativeCoarseShadingCapacity NativeCoarseShadingPruning NativeCoarsePowerWindow
open NativeCoarseNativeAdmissibility NativeDyadicParentCells NativeFullCoarseShadow
open NativeTruncatedRetentionCoarseSelection NativeEffectiveOutputThreshold NativeCoarseRelativeCW
open NativeQuarterScaleParameters
open scoped BigOperators ENNReal

/-- Admission needing original reference populations only through b, while
retaining the full original fine shading level. Direct admission at the ACTUAL output mesh on one fixed native
reference and an arbitrary specified retained E. The only incidence loss
is the literal real factor F, paid at that output mesh; native admission of
the fine source shaded only by E is never an input. Both cutoffs are chosen
before the reference, E, and coarse depth. -/
theorem exists_same_reference_admission_through (e window : ℝ) (he : 0 < e) (hw : 0 < window) :
    let zetaMin := window*e/16
    ∃epsilon0 : ℝ,0 < epsilon0 ∧ epsilon0 ≤ 1/128 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
      (∀i,D.line i∈fixedCompactClass) → D.thickness ≤ epsilon0 → eta ≤ zetaMin/16 →
      ∀(original : Fin n → Finset Index) (a : ℝ) (level : ℕ)
        (R : Finset (Fin n)) (E : Finset (Fin n × Index)),
      (∀i,D.shading i=wzCellShading (mesh D) original i) →
      D.thickness=(2:ℝ)⁻¹^level →
      (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
      R.Nonempty → E ⊆ retained original R →
      ∀(b : ℕ) (F : ℝ),6 ≤ b → b ≤ level →
      D.thickness ≤ 1/((2^b:ℕ):ℝ) → 64/((2^b:ℕ):ℝ) ≤ D.thickness^window →
      0 < F → F ≤ (64/((2^b:ℕ):ℝ))^(-(e/32)) →
      ((incidences original).card:ℝ) ≤ F*(E.card:ℝ) →
      (∀ell : Fin (b+1),∀p : Parent,
        (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
          D.thickness^zetaMin*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
            ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
            D.thickness^(-zetaMin)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) →
      let rep := representative h R a (2^b)
      ∃(Q : Finset Parent)
        (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^b:ℕ):ℝ) ≤
          dist (direction (D.line (rep p))) (direction (D.line (rep q)))),
        Q⊆R.image (parentLabel D a (2^b)) ∧ Q.Nonempty ∧
        let C := source h a level b Q rep E hsep
        IsWangZakharovNativeFiniteInput C e ∧ (∀i,C.line i∈fixedCompactClass) ∧
        (ENNReal.ofReal (64/((2^b:ℕ):ℝ))).rpow (7*e/16)*
          NativeFiniteKakeyaCounts.multiplicity (fullSource h R a level b E) ≤
            NativeFiniteKakeyaCounts.multiplicity C ∧
        (64/((2^b:ℕ):ℝ))^(5*e/16) ≤ (wzTotalShadingVolume C).toReal := by
  intro zetaMin
  have hzMin : 0 < zetaMin := by dsimp [zetaMin]; positivity
  obtain ⟨ds,hds,HS⟩ := same_reference_coarse_selection_through hzMin
  obtain ⟨dOut,hdOut,hdOutSmall,Hout⟩ := exists_output_cutoff e he
  obtain ⟨dw,hdw,_hdw1,HW⟩ := exists_small_power_cutoff hw hdOut
  refine ⟨min (1/128) (min ds dw),lt_min (by norm_num) (lt_min hds hdw),min_le_left _ _,?_⟩
  intro n D eta h hK hsmall heta original a level R E horiginal hdy ha hR hE b F
    hb hbl hfine hwindow hF hFupper hret H rep
  let Delta : ℝ := 64/((2^b:ℕ):ℝ)
  let zeta := NativeEffectiveOutputThreshold.exponent D.thickness Delta e
  have hd : 0 < D.thickness := h.1.2.1
  have hd1 : D.thickness < 1 :=
    lt_of_le_of_lt (hsmall.trans (min_le_left _ _)) (by norm_num)
  have hD : 0 < Delta := by dsimp [Delta]; positivity
  have hDOut : Delta ≤ dOut := hwindow.trans
    (HW D.thickness hd (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hD1 : Delta ≤ 1 := (hDOut.trans hdOutSmall).trans (by norm_num)
  have hz : zetaMin ≤ zeta := fixed_lower_bound hd hd1 hD he.le hwindow
  have hzeta : 0 < zeta := hzMin.trans_le hz
  have hp (k : ℝ) : D.thickness^(k*zeta)=Delta^(k*e/16) :=
    power_readback hd hd1 hD e k
  have hp1 : D.thickness^zeta=Delta^(e/16) := by simpa only [one_mul] using hp 1
  have hp5 : D.thickness^(5*zeta)=Delta^(5*e/16) := hp 5
  have hp8 : D.thickness^(8*zeta)=Delta^(e/2) := by
    calc
      D.thickness^(8*zeta)=Delta^(8*e/16) := hp 8
      _=Delta^(e/2) := by congr 1; ring
  obtain ⟨habsorb,hupper,hdensity,hCW⟩ := Hout Delta F hD hDOut hF.le hFupper
  have Hnew : ∀ell : Fin (b+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 := by
    intro ell p hpop
    have hh := H ell p hpop
    have hratio : 0 ≤ ((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 := by positivity
    exact ⟨(mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hd hd1.le hz) hratio).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1.le (neg_le_neg hz)) hratio)⟩
  obtain ⟨Q,hQP,hQne,hQrep,hsep,hshade,Hpruned⟩ :=
    HS n D eta h (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) heta
      zeta F hz hF (by rwa [hp1]) original a level R E horiginal hdy ha hR hE hret b hb hbl Hnew
  have hEorig : ∀x∈E,x.2∈original x.1 :=
    fun x hx => ((retained_spec original R x).mp (hE hx)).2
  have hscale : ((2^b:ℕ):ℝ)*D.thickness ≤ 1 := by
    have hh := (le_div_iff₀ (show (0:ℝ)<((2^b:ℕ):ℝ) by positivity)).mp hfine
    simpa only [mul_comm] using hh
  have hpower : Delta^e ≤ D.thickness^(8*zeta) := by
    rw [hp8]
    exact Real.rpow_le_rpow_of_exponent_ge hD hD1 (by linarith only [he])
  have hcw : cwCost*D.thickness^(8*zeta-(eta+6*zeta)) ≤ 1 := by
    have hetaz : eta ≤ zeta := heta.trans (by linarith only [hz,hzMin])
    have hexp : zeta ≤ 8*zeta-(eta+6*zeta) := by linarith only [hetaz]
    calc
      _ ≤ cwCost*D.thickness^zeta := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hd hd1.le hexp) cwCost_pos.le
      _ ≤ 1 := by rwa [hp1]
  have hnative := native_input h hK hzeta.le original horiginal ha R level b hdy hbl hb hscale
    Q hQP hQne rep (fun p hp => (hQrep p hp).2) E hEorig hsep
    (fun p hp => (Hnew ⟨b,by omega⟩ p hp).1) (fun ell p hp => (Hpruned ell p hp).1)
    hshade hpower (by rwa [hp8]) (by rwa [hp1]) hcw
  refine ⟨Q,hsep,hQP,hQne,hnative,?_,?_,?_⟩
  · intro i
    exact NativeCoarseRepresentativeGeometry.zero_parent_mem_fixedCompactClass h hK ha (rep (parentIndex Q i))
  · have htransfer := full_multiplicity_le_core h original horiginal ha R level b hdy hbl hb E hEorig
      (fun p hp => (Hnew ⟨b,by omega⟩ p hp).1) Q hQP hsep hshade (by
        change densityCost*D.thickness^zeta ≤ 1
        rwa [hp1])
    rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hd, hp 7,
      ←ENNReal.ofReal_rpow_of_pos hD] at htransfer
    exact htransfer
  · rw [NativeCoarseSourceMass.source_total_shading_real]
    rwa [←hp5]

end NativeTruncatedOutputScaleAdmission
