import Theorems.Thm_StickyKakeya4_native_coarse_power_window
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3800000
noncomputable section
namespace NativeCoarseNativeAdmissibility
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeUnitParentNormalization NativeCoarseCellSource NativeCoarseSourceProfiles NativeCoarseSourceMass
open NativeCoarseRelativeCW NativeCoarsePowerWindow NativeCoarseShadingPruning NativeDyadicParentCells
open scoped BigOperators ENNReal

/-- Assemble the existing native predicate on the literal constructed source.
Every profile premise below is a previously derived original-cell or finite
pruning inequality; the source-only consumer discharges all of them. -/
theorem native_input {n : ℕ} {D : FiniteScaleSource n} {eta a zeta e : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (hz : 0 ≤ zeta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hm : m ≤ level) (h6 : 6 ≤ m) (hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1)
    (Q : Finset Parent) (hQ : Q⊆R.image (parentLabel D a (2^m))) (hQne : Q.Nonempty)
    (rep : Parent → Fin n) (hrep : ∀p∈Q,parentLabel D a (2^m) (rep p)=p)
    (E : Finset (Fin n × Index)) (hE : ∀x∈E,x.2∈original x.1)
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^m:ℕ):ℝ) ≤ dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (Horiginal : ∀p : Parent,(R.filter (fun i => parentLabel D a (2^m) i=p)).Nonempty →
      D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ))
    (Hpruned : ∀ell : Fin (m+1),∀p : Parent,
      (Q.filter (fun q => ancestor m ell.val q=p)).Nonempty →
        D.thickness^(8*zeta)*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
          ((Q.filter (fun q => ancestor m ell.val q=p)).card:ℝ))
    (hshade : D.thickness^(5*zeta) ≤ ∑p∈Q,weight D a level m rep E p)
    (hpower : (64/((2^m:ℕ):ℝ))^e ≤ D.thickness^(8*zeta))
    (hupper : 10077696*D.thickness^(8*zeta) ≤ 1)
    (hdensity : densityCost*D.thickness^zeta ≤ 1)
    (hcw : cwCost*D.thickness^(8*zeta-(eta+6*zeta)) ≤ 1) :
    IsWangZakharovNativeFiniteInput (source h a level m Q rep E hsep) e := by
  let S := source h a level m Q rep E hsep
  change IsWangZakharovNativeFiniteInput S e
  have hd := h.1.2.1
  obtain ⟨hdS,hdS1,hdyS,hvalid,_hSK,hweights,hmeas,hcub,hsub,hsepS,hslab,hfixed⟩ :=
    source_geometric_fields h hK original horiginal ha level m hdy hm h6 Q rep E hE hsep
  have hdS' : 0 < S.thickness := hdS
  have hneg : D.thickness^(-8*zeta) ≤ S.thickness^(-e) := negative_power_transfer hd hdS hpower
  have hmassfinite := source_total_shading_ne_top (a:=a) h level m Q rep E hsep
  have htubefinite := source_tube_mass_ne_top (a:=a) h level m Q rep E hsep h6
  refine ⟨⟨card_pos.mpr hQne,hdS,hdS1,hdyS,hvalid,hweights,hmeas,hcub,hsub,hsepS,?_,?_,?_⟩,hslab,hfixed⟩
  · intro i r hr hr1
    have hrp : 0 < r := hdS'.trans_le hr
    have hratio0 : 0 ≤ (r/S.thickness)^3 := pow_nonneg (div_nonneg hrp.le hdS'.le) 3
    have hlow := source_carrier_lower (a:=a) h level m Q rep E hsep hK ha hrep Hpruned i hr hr1
    have hu := source_carrier_upper (a:=a) h level m Q rep E hsep i hr
    have hc : (10077696:ℝ) ≤ D.thickness^(-8*zeta) := by
      rw [show -8*zeta=-(8*zeta) by ring,Real.rpow_neg hd.le,←one_div]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr hupper
    exact NativePaddedSourceAdmissibility.real_AD_to_enn hdS' hrp.le _
      ((mul_le_mul_of_nonneg_right hpower hratio0).trans hlow)
      (hu.trans (mul_le_mul_of_nonneg_right (hc.trans hneg) hratio0))
  · intro U hU
    change (wzContainedTubeCount S U:ℝ≥0∞) ≤ (ENNReal.ofReal S.thickness).rpow (-e)*volume U*Q.card
    have hp0 : (ENNReal.ofReal S.thickness).rpow (-e)≠0 :=
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hdS) ENNReal.ofReal_ne_top).ne'
    have hpT : (ENNReal.ofReal S.thickness).rpow (-e)≠⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hdS) ENNReal.ofReal_ne_top
    by_cases hfin : volume U=⊤
    · have hn0 : (Q.card:ℝ≥0∞)≠0 := by exact_mod_cast (card_pos.mpr hQne).ne'
      simp only [hfin,ENNReal.mul_top hp0,ENNReal.top_mul hn0,le_top]
    · have hO : ∀p∈Q,D.thickness^zeta*((1/((2^m:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^m) i=p)).card:ℝ) := by
        intro p hp
        obtain ⟨i,hi,hip⟩ := mem_image.mp (hQ hp)
        exact Horiginal p ⟨i,mem_filter.mpr ⟨hi,hip⟩⟩
      have hreal := source_CW_original_power h original horiginal ha R level m hdy hm h6 hscale
        Q hQ rep hrep E hE hsep hO hshade U hU hfin
      have hc := (coefficient_to_original_power hd hcw).trans hneg
      have hfinal : (wzContainedTubeCount S U:ℝ) ≤ S.thickness^(-e)*(volume U).toReal*(Q.card:ℝ) :=
        hreal.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc ENNReal.toReal_nonneg) (Nat.cast_nonneg _))
      have hright : (ENNReal.ofReal S.thickness).rpow (-e)*volume U*Q.card≠⊤ := by finiteness
      apply (ENNReal.toReal_le_toReal (by simp) hright).mp
      simp only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,ENNReal.toReal_natCast,
        ←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hdS'.le]
      exact hfinal
  · have hraw := source_density_original_power (a:=a) h level m Q rep E hsep h6 R hQ Horiginal hshade hdensity
    have hpow : S.thickness^e ≤ D.thickness^(7*zeta) :=
      hpower.trans (Real.rpow_le_rpow_of_exponent_ge hd h.1.2.2.1 (by linarith))
    have hfinal : S.thickness^e*(wzTotalTubeVolume S).toReal ≤ (wzTotalShadingVolume S).toReal :=
      (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans hraw
    have hpT : (ENNReal.ofReal S.thickness).rpow e≠⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hdS) ENNReal.ofReal_ne_top
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hpT htubefinite) hmassfinite).mp
    simp only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hdS'.le]
    exact hfinal

end NativeCoarseNativeAdmissibility
